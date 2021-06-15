// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#include "supp/portfolio_solver.h"

#include <boost/range/algorithm.hpp>
#include <boost/interprocess/shared_memory_object.hpp>
#include <boost/interprocess/mapped_region.hpp>
#include <boost/interprocess/managed_shared_memory.hpp>
#include <algorithm>

extern "C" {
#include <signal.h>
#include <sys/select.h>
#include <sys/time.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <unistd.h>
}

#include "checker_types.h"
#include "supp/logger.h"

using namespace std;
using namespace boost::interprocess;

namespace euforia {

//^----------------------------------------------------------------------------^

class PortfolioSolver::Impl {
 public:
  Stats stats_;
  std::vector<std::shared_ptr<Solver>> solvers_;

  Impl(std::vector<std::shared_ptr<Solver>> solvers);

  void Apply(std::function<void(Solver& s)> f) {
    boost::for_each(solvers_, [&](auto&& s) { return f(*s); });
  }

  void Push() { Apply([](auto&& s) { s.Push(); }); }
  void Pop() { Apply([](auto&& s) { s.Pop(); }); }
  void Add(const z3::expr& e) { Apply([&](auto&& s) { s.Add(e); }); }
  CheckResult Check(const size_t n, const z3::expr* assumptions);

  void DumpBenchmark(
    std::ostream& out, size_t n, const z3::expr* assumptions);

  void collect_statistics(Statistics * /*st*/) const {
  }

  template <typename... Args>
  void Log(int level, const char *fmt, const Args&... args) {
    logger.Log(level, "PortfolioSolver: {}",
               fmt::format(fmt, std::forward<const Args>(args)...));
  }

};

PortfolioSolver::Impl::Impl(std::vector<std::shared_ptr<Solver>> solvers)
    : solvers_(solvers) {}
  

CheckResult PortfolioSolver::Impl::Check(const size_t n,
                                         const z3::expr* assumptions) {
  static const char *shm_tag = "PortfolioSolverResult";
  struct ShmRemove {
    ShmRemove() { shared_memory_object::remove(shm_tag); }
    ~ShmRemove() { shared_memory_object::remove(shm_tag); }
  };

  // If it exists, delete it first

  // Create shared memory to return results
  shared_memory_object global_shm(open_or_create, shm_tag, read_write);

//   managed_shared_memory segment(open_or_create, shm_tag, read_only);

  // Set size
  global_shm.truncate(sizeof(CheckResult)*solvers_.size());

  mapped_region global_region(global_shm, read_write);

  Log(0, "pid {}: created shared memory for CheckResult", getpid());

  // Create forks for each solver
  vector<pid_t> pids(solvers_.size());
  for (size_t i = 0; i < solvers_.size(); i++) {
    auto s = solvers_[i];
    pid_t pid = pids[i] = fork();
    if (pid == 0) { // in child
      Log(0, "pid {}: child solver #{} version {}", getpid(), i,
                 s->version());
      // Check with solver s
      auto result = s->Check(n, assumptions);
      
      Log(0, "pid {}: solver Check() returned", getpid(), result);

      // Open created object
      shared_memory_object shm(open_only, shm_tag, read_write);
      
      Log(0, "pid {}: opened shm", getpid(), result);

      // Map the whole memory in this process
      mapped_region region(shm, read_write);
      
      Log(0, "pid {}: mapped shm", getpid(), result);

      CheckResult *result_dst = static_cast<CheckResult*>(region.get_address()) + i;
      *result_dst = result;
      
      Log(0, "pid {}: finished writing result, exiting", getpid(), result);
      exit(EXIT_SUCCESS);
    }
  }

  // Wait for a status change in child
  Log(0, "pid {}: waiting for solver pid status change", getpid());
  pid_t child;
  bool abnormal = false;
  while (true) {
    int wstatus;
    child = wait(&wstatus);
    if (WIFEXITED(wstatus)) {
      // yay, finished
      int exit_status = WEXITSTATUS(wstatus);
      if (WIFSIGNALED(wstatus)) {
        // child terminated by signal below
        int sig = WTERMSIG(wstatus);
        Log(0, "pid {}: pid {} exited with signal {}", getpid(),
            child, sig);
        abnormal = true;
      } else {
        Log(0, "pid {}: pid {} exited with status {}", getpid(),
            child, exit_status);
      }
      break;
    }
    // else if (WIF_CONTINUED(wstatus)) {
    // }
  }

  // Kill all processes
  Log(0, "killing all forked solvers");
  for (auto pid : pids) {
    if (pid > 0) {
      kill(pid, SIGSTOP);
      kill(pid, SIGKILL);
    }
  }

  if (abnormal) {
    exit(1);
  }

  // Read shared memory
  auto result_src = static_cast<CheckResult*>(global_region.get_address());
  Log(0, "pid {} returned result {}", child, *result_src);
  return *result_src;
}


void PortfolioSolver::Impl::DumpBenchmark(
    std::ostream& out, size_t n, const z3::expr* assumptions) {
  solvers_[0]->DumpBenchmark(out, n, assumptions);
}


//^----------------------------------------------------------------------------^


PortfolioSolver::PortfolioSolver(z3::context& c,
                                 std::vector<std::shared_ptr<Solver>> solvers)
    : pimpl_(make_unique<PortfolioSolver::Impl>(solvers)), ctx_(c) {}

PortfolioSolver::~PortfolioSolver() = default;

void PortfolioSolver::Push() { pimpl_->Push(); }

void PortfolioSolver::Pop() { pimpl_->Pop(); }

void PortfolioSolver::Add(const z3::expr& e) { pimpl_->Add(e); }

CheckResult
PortfolioSolver::Check(const size_t n, const z3::expr* assumptions) {
  return pimpl_->Check(n, assumptions);
}

std::shared_ptr<Model> PortfolioSolver::get_model() {
  EUFORIA_FATAL("unimplemented");
}

z3::expr_vector PortfolioSolver::unsat_core() {
  EUFORIA_FATAL("unimplemented");
}

z3::expr_vector PortfolioSolver::unsat_core_reasons() {
  EUFORIA_FATAL("unimplemented");
}

z3::expr_vector PortfolioSolver::assertions() const {
  EUFORIA_FATAL("unimplemented");
}

std::string PortfolioSolver::reason_unknown() const {
  return "shrug";
}

std::ostream& PortfolioSolver::Print(std::ostream& out) const {
  return out;
}

void PortfolioSolver::DumpBenchmark(
    std::ostream& out, size_t n, const z3::expr* assumptions) {
  pimpl_->DumpBenchmark(out, n, assumptions);
}

const char *PortfolioSolver::version() const {
  return "PortfolioSolver";
}

void PortfolioSolver::collect_statistics(Statistics *st) const {
  return pimpl_->collect_statistics(st);
}

} // end namespace euforia


#if 0
        // Use select() to wait on pids
        fd_set set;
        struct timeval timeout;

        // Initialize fdset
        FD_ZERO(&set);
        for (auto fd : pids) {
          FD_SET(fd, &set);
        }

        // Initialize timeout
        timeout.tv_sec = 1800;
        timeout.tv_usec = 0;

        int r = -1;
        while (r == -1) {
          r = select(
              FD_SETSIZE, &set, NULL, NULL, &timeout);
          if (r == -1) {
            if (errno != EINTR)
              break;
          }
        }
        if (r == 0) {
          // timeout
        }
        for (auto fd : pids) {
          if (FD_ISSET(fd, &set)) {
            // There is a ... something
          }
      }
#endif
