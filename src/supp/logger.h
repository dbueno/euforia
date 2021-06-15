// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#ifndef EUFORIA_LOGGER_H_
#define EUFORIA_LOGGER_H_

#include <fmt/format.h>
#include <fmt/ostream.h>
#include <fstream>
#include <unordered_set>

namespace euforia {

//! Logging, but by name, not level. I use it for zeroing in on some patterns.
//! The other logger is more of an overall narrative of euforia as it runs.
//! This logger is for cross-cutting, independent stories.
class NameLogger {
 public:
  NameLogger() {}

  void Enable(const std::string& n) {
    active_.insert(n);
  }

  void Disable(const std::string& n) {
    active_.erase(n);
  }

  bool should_log(const std::string& n) {
    return active_.find(n) != active_.end();
  }

  template <typename... Args> void Log(const std::string& name, const char *fmt,
                                       const Args&... args) {
    if (should_log(name)) {
      auto fmt_msg = [&](std::ostream& os) {
        fmt::print(os, "{}: ", name);
        fmt::print(os, fmt, std::forward<const Args>(args)...);
        fmt::print(os, "\n");
      };
      //fmt::print(std::cerr, "[{:06d}] ", count_);
      fmt_msg(std::cout);
    }
  }

 private:
  std::unordered_set<std::string> active_;
};

extern NameLogger nlogger;


// 1 - high level messages
// 2 - more info about high level messages
// 3 - low level action messages but not big formulas
// 4-5 - low level
// 10 - *absurdly* low level informational messages for debugging, like deleting from a map
class Logger {
  int level_;
  uint64_t count_;
  std::ofstream mirror_file_;

 public:
  Logger() : level_(0), count_(0) {}

  void set_level(int level) { level_ = level; }

  bool ShouldLog(int level) { return level <= level_; }

  void set_mirror_file(std::string filename) {
    mirror_file_ = std::ofstream(filename);
  }

  template <typename... Args> void Log(int level, const char *fmt,
                                       const Args&... args) {
    if (ShouldLog(level)) {
      auto fmt_msg = [&](std::ostream& os) {
        fmt::print(os, fmt, std::forward<const Args>(args)...);
        fmt::print(os, "\n");
      };
      //fmt::print(std::cerr, "[{:06d}] ", count_);
      fmt_msg(std::cout);
      if (mirror_file_.is_open())
        fmt_msg(mirror_file_);
      ++count_;
    }
  }
  
  template <typename... Args> void LogOpenFold(int level, const char *fmt,
                                               const Args&... args) {
    if (ShouldLog(level)) {
      //fmt::print(std::cerr, "[{:06d}] ", count_);
      auto fmt_msg = [&](std::ostream& os) {
        fmt::print(os, fmt, std::forward<const Args>(args)...);
        fmt::print(os, "{{{{{{");
        fmt::print(os, "\n");
      };
      fmt_msg(std::cout);
      if (mirror_file_.is_open())
        fmt_msg(mirror_file_);
      ++count_;
    }
  }
  
  template <typename... Args> void LogCloseFold(int level, const char *fmt,
                                                const Args&... args) {
    if (ShouldLog(level)) {
      //fmt::print(std::cerr, "[{:06d}] ", count_);
      auto fmt_msg = [&](std::ostream& os) {
        fmt::print(os, fmt, std::forward<const Args>(args)...);
        fmt::print(os, "}}}}}}");
        fmt::print(os, "\n");
      };
      fmt_msg(std::cout);
      if (mirror_file_.is_open())
        fmt_msg(mirror_file_);
      ++count_;
    }
  }

  template <typename... Args> void LogFold(int level, const char *fmt,
                                           const Args&... args) {
    if (ShouldLog(level)) {
      LogOpenFold(level, "");
      Log(level, fmt, std::forward<const Args>(args)...);
      LogCloseFold(level, "");
    }
  }

  void Log(int level, const char *msg) {
    if (ShouldLog(level)) {
      //fmt::print(std::cerr, "[{:06d}] ", count_);
      auto fmt_msg = [&](std::ostream& os) {
        fmt::print(os, msg);
        fmt::print(os, "\n");
      };
      fmt_msg(std::cout);
      if (mirror_file_.is_open())
        fmt_msg(mirror_file_);
      ++count_;
    }
  }
};

extern Logger logger;

#if defined(LOGGER_ON)
#define LOG(...) logger.Log(__VA_ARGS__)
#else
#define LOG(...) do {} while (false)
#endif // LOGGER_ON

constexpr int kLogLowest = 10;

} // end namespace euforia

#endif
