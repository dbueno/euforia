// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#if defined(__linux__) && !defined(_GNU_SOURCE)
#define _GNU_SOURCE 1
#endif


#include "supp/boolector_supp.h"

#include <bitset>
#include <boost/iterator/zip_iterator.hpp>
#include <gmpxx.h>
#include <iostream>
#include <llvm/Support/Casting.h>

#include "supp/std_supp.h"
#include "supp/wrapstream.h"


using namespace std;
using namespace llvm;

static inline int log2pow2(int size) {
  switch (size) {
    case 1: return 0;
    case 2: return 1;
    case 4: return 2;
    case 8: return 3;
    case 16: return 4;
    case 32: return 5;
    case 64: return 6;
    case 128: return 7;
  }
  EUFORIA_FATAL("size must be power of two < 256: got " + to_string(size));
}


/*-----------------------------------------------------------------------------------*/

namespace boolector {


std::size_t hash_value(const BoolectorNodeWrapper& n) {
  return n.hash();
}

std::ostream& operator<<(std::ostream& os, const BoolectorNodeWrapper& n) {
  auto *file = wrapostream(os);
  boolector_dump_smt2_node(boolector_get_btor(n.c_node_), file, n.c_node_);
  fclose(file);
  return os;
}

BoolectorNodeWrapper BoolectorNodeWrapper::operator()(const BoolectorNodeWrapper& a) {
  vector<BoolectorNodeWrapper> args({a});
  return boolector::apply(args, *this);
}

BoolectorNodeWrapper BoolectorNodeWrapper::operator()(const std::vector<BoolectorNodeWrapper>& args) {
  return boolector::apply(args, *this);
}

/*-----------------------------------------------------------------------------------*/
/* btor methods */


BtorWrapper::BtorWrapper() : c_btor_(boolector_new()), trfp(nullptr) {}

BtorWrapper::~BtorWrapper() {
  boolector_release_all(c_btor_);
  boolector_delete(c_btor_);
  if (trfp) fclose(trfp);
}

BtorWrapper::BtorWrapper(const BtorWrapper& other) 
  : c_btor_(boolector_clone(other.c_btor_)),
    trfp(boolector_get_trapi(other.c_btor_)) {
  for (auto& [name, node] : other.bitvecs) {
    bitvecs.insert({name, matchNode(node)});
  }
  for (auto& [name, node] : other.arrays) {
    arrays.insert({name, matchNode(node)});
  }
  for (auto& a : other.assumptions) {
    assumptions.push_back(matchNode(a));
  }
  for (auto& [name, node] : other.params) {
    params.insert({name, node});
  }
  for (auto& f : other.funs) {
    funs.push_back(f);
  }
}

void BtorWrapper::setOption(BtorOption o, uint32_t val) {
  boolector_set_opt(c_btor_, o, val);
}

uint32_t BtorWrapper::getOption(BtorOption o) const {
  return boolector_get_opt(c_btor_, o);
}

void BtorWrapper::PrintStats() const {
  boolector_print_stats(c_btor_);
}

void BtorWrapper::ResetStats() {
  boolector_reset_stats(c_btor_);
}

 BoolectorNodeWrapper BtorWrapper::zero(int width) {
  return Wrap(boolector_zero(c_btor_, boolector_bitvec_sort(c_btor_, width)));
}

 BoolectorNodeWrapper BtorWrapper::bconst(const char *bits) {
  return Wrap(boolector_const(c_btor_, bits));
}

BoolectorNodeWrapper BtorWrapper::bconst(const std::string& bits) {
  return Wrap(boolector_const(c_btor_, bits.c_str()));
}

BoolectorNodeWrapper BtorWrapper::boolVal(bool b) {
  auto ret = Wrap(b ? boolector_true(c_btor_) : boolector_false(c_btor_));
  return ret;
}

BoolectorNodeWrapper BtorWrapper::cint(int i, int width) {
  auto sort = width == 1 ? boolector_bool_sort(c_btor_) : boolector_bitvec_sort(c_btor_, width);
  return Wrap(boolector_int(c_btor_, i, sort));
}

BoolectorNodeWrapper BtorWrapper::var(int width, const std::string& name) {
  if (width < 1) EUFORIA_FATAL("width is not at least 1");
  if (auto loc = bitvecs.find(name); loc != bitvecs.end()) {
    assert(name == loc->second.symbol());
    assert(static_cast<unsigned>(width) == loc->second.width());
    return loc->second;
  }
  
  auto sort = boolector_bitvec_sort(c_btor_, width);
  auto ret = Wrap(boolector_var(c_btor_, sort, name.c_str()));
  bitvecs.insert({name, ret});
  return ret;
}
  

BoolectorNodeWrapper BtorWrapper::boolvar(const std::string& name) {
  if (auto search = bools_.find(name); search != bools_.end()) {
    assert(name == search->second.symbol());
    return search->second;
  }
  auto sort = boolector_bool_sort(c_btor_);
  auto ret = Wrap(boolector_var(c_btor_, sort, name.c_str()));
  bools_.insert({name, ret});
  return ret;
}

BoolectorNodeWrapper BtorWrapper::uf(BoolectorSort s, const string& name) {
  return Wrap(boolector_uf(c_btor_, s, name.c_str()));
}

BoolectorNodeWrapper BtorWrapper::param(BoolectorSort sort, const std::string& name) {
  if (auto loc = params.find(name); loc != params.end()) {
    assert(boolector_is_param(c_btor_, loc->second.c_node_));
    assert(name == loc->second.symbol());
    return loc->second;
  }
  
  auto ret = Wrap(boolector_param(c_btor_, sort, name.c_str()));
  params.insert({name, ret});
  return ret;
}

BoolectorNodeWrapper write(const BoolectorNodeWrapper& arr, const BoolectorNodeWrapper& c_node_, const BoolectorNodeWrapper& val) {
  assert(arr.btor() == c_node_.btor() && c_node_.btor() == val.btor());
//    if (boolector_is_fun_sort(arr.btor(), arr.sort())) {
//      // write is a new fun
//      auto name = "ptr_in" + to_string(++paramCtr);
//      auto ptr_in = BoolectorNodeWrapper(boolector_param(arr.btor(), boolector_fun_get_domain_sort(arr.btor(), arr.c_node_), name.c_str()));
//      vector<BoolectorNodeWrapper> recArg({ptr_in});
//      auto body = ite(ptr_in.eq(c_node_), val, boolector::apply(recArg, arr));
//      BoolectorNode **param = new BoolectorNode*[1];
//      param[0] = ptr_in.c_node_;
//      auto ret = BoolectorNodeWrapper(boolector_fun(arr.btor(), param, 1, body.c_node_));
//      delete[] param;
//      return ret;
//    } else {
    // use boolector_write
    return BoolectorNodeWrapper(arr.btor(), boolector_write(arr.btor(), arr.c_node_, c_node_.c_node_, val.c_node_));
//    }
}

BoolectorNodeWrapper read(const BoolectorNodeWrapper& arr, const BoolectorNodeWrapper& c_node_) {
  assert(arr.btor() == c_node_.btor());
//    if (boolector_is_fun_sort(arr.btor(), arr.sort())) {
//      // read is an apply
//      BoolectorNode **args = new BoolectorNode*[1];
//      args[0] = c_node_.c_node_;
//      auto ret = BoolectorNodeWrapper(boolector_apply(arr.btor(), args, 1, arr.c_node_));
//      delete[] args;
//      return ret;
//    } else {
    return BoolectorNodeWrapper(arr.btor(), boolector_read(arr.btor(), arr.c_node_, c_node_.c_node_));
//    }
}

BoolectorNodeWrapper BtorWrapper::array(const std::string& name, int ptrSize, int valWidth) {
  if (auto loc = arrays.find(name); loc != arrays.end()) {
    assert(name == loc->second.symbol());
    assert(boolector_is_array(loc->second.btor(), loc->second.c_node_));
    return loc->second;
  }
  
  auto sort = boolector_array_sort(c_btor_, boolector_bitvec_sort(c_btor_, ptrSize), boolector_bitvec_sort(c_btor_, valWidth));
  auto ret = Wrap(boolector_array(c_btor_, sort, name.c_str()));
  arrays.insert({name, ret});
  return ret;
}

BoolectorNodeWrapper BtorWrapper::const_array(
    int ptr_size, const BoolectorNodeWrapper& value) {
  int val_size = static_cast<int>(value.width());
  auto sort = boolector_array_sort(c_btor_,
                                   boolector_bitvec_sort(c_btor_, ptr_size),
                                   boolector_bitvec_sort(c_btor_, val_size));
  auto ret = Wrap(boolector_const_array(c_btor_, sort, value.c_node_));
  return ret;
}

BoolectorNodeWrapper BtorWrapper::fun(const std::vector<BoolectorNodeWrapper>& funParams, BoolectorNodeWrapper body) {
  int paramc = static_cast<int>(funParams.size());
  BoolectorNode **paramnodes = new BoolectorNode*[funParams.size()];
  for (int i = 0; i < paramc; i++) {
    paramnodes[i] = funParams[i].c_node_;
  }
  auto ret = Wrap(boolector_fun(c_btor_, paramnodes, paramc, body.c_node_));
  delete[] paramnodes;
  funs.push_back(ret);
  return ret;
}

BoolectorSort BtorWrapper::fun_sort(BoolectorSort *args, uint32_t arity,
                                    BoolectorSort ret) {
  return boolector_fun_sort(c_btor_, args, arity, ret);
}

BoolectorSort BtorWrapper::array_sort(BoolectorSort index,
                                      BoolectorSort element) {
  return boolector_array_sort(c_btor_, index, element);
}

BoolectorSort BtorWrapper::bitvec_sort(uint32_t width) {
  return boolector_bitvec_sort(c_btor_, width);
}

BoolectorSort BtorWrapper::bool_sort() {
  return boolector_bool_sort(c_btor_);
}

BoolectorNodeWrapper apply(const std::vector<BoolectorNodeWrapper>& args, BoolectorNodeWrapper f) {
  int argc = static_cast<int>(args.size());
  BoolectorNode **argnodes = new BoolectorNode*[args.size()];
  for (int i = 0; i < argc; i++) {
    argnodes[i] = args[i].c_node_;
  }
  auto ret = BoolectorNodeWrapper(f.btor(), boolector_apply(f.btor(), argnodes, argc, f.c_node_));
  delete[] argnodes;
  return ret;
}



void BtorWrapper::fixateAssumptions() {
  boolector_fixate_assumptions(c_btor_);
}

void BtorWrapper::resetAssumptions() {
  boolector_reset_assumptions(c_btor_);
}

BtorWrapper::result BtorWrapper::simplify() {
  ScopedTimeKeeper t(&total_simplify_time_);
  auto result = boolector_simplify(c_btor_);
  switch (result) {
    case BOOLECTOR_SAT: return result::kSat;
    case BOOLECTOR_UNSAT: return result::kUnsat;
    case BOOLECTOR_UNKNOWN: return result::kUnknown;
    default:
      EUFORIA_FATAL("bad result from boolector");
  }
}

BtorWrapper::result BtorWrapper::check() {
  ScopedTimeKeeper t(&total_check_time_);
  auto result = boolector_sat(c_btor_);
  assumptions.clear();
  switch (result) {
    case BOOLECTOR_SAT: return result::kSat;
    case BOOLECTOR_UNSAT: return result::kUnsat;
    default: EUFORIA_FATAL("unhandled switch");
  }
}

shared_ptr<BtorAssignment> BtorWrapper::assignment(const BoolectorNodeWrapper& n) {
  assert(n.btor() == c_btor_);
  shared_ptr<BtorAssignment> ret;
  if (n.isArray()) {
    ret = make_shared<BtorArrayAssignment>(*this, n);
  } else {
    assert(n.isBV());
    ret = make_shared<BtorBvAssignment>(*this, n);
  }
  return ret;
}

BoolectorNodeWrapper BtorWrapper::assignmentNode(const BtorAssignment& a) {
  switch (a.kind) {
    case BtorAssignment::kind::BV: {
      auto& val = static_cast<const BtorBvAssignment&>(a);
      return bconst(val.value());
    }

    case BtorAssignment::kind::Array: {
      auto& arrayAss = static_cast<const BtorArrayAssignment&>(a);
      auto arr = array(arrayAss.symbol, arrayAss.ptrSize, arrayAss.valSize);
      for (int i = 0; i < arrayAss.size(); i++) {
        auto& c_node_ = arrayAss.indices()[i];
        auto& val = arrayAss.values()[i];
        auto nptr = bconst(c_node_);
        auto nval = bconst(val);
        arr = write(arr, nptr, nval);
      }
      return arr;
    }
      
    default:
      EUFORIA_FATAL("more imples");
  }

}


BoolectorNodeWrapper BtorWrapper::matchNode(const BoolectorNodeWrapper& n) const {
  return Wrap(boolector_match_node(c_btor_, n.c_node_));
}


BtorWrapper::result BtorWrapper::checkSMT2(const std::string& filename) {
  auto *fp = fopen(filename.c_str(), "r");
  assert(nullptr != fp);
  char *error_msg = nullptr;
  int status = -1;
  auto *outfile = fopen("/tmp/btor_checkSMT2_outfile", "w");
  assert(nullptr != outfile);
  switch (boolector_parse_smt2(c_btor_, fp, filename.c_str(), outfile, &error_msg, &status)) {
    case BOOLECTOR_SAT:
      return result::kSat;
    case BOOLECTOR_UNSAT:
      return result::kUnsat;
    case BOOLECTOR_UNKNOWN:
      return result::kUnknown;
    case BOOLECTOR_PARSE_ERROR:
      EUFORIA_FATAL("checkSMT2: boolector parse error");
  }
  EUFORIA_FATAL("unexpected");
}

void BtorWrapper::setTrace(const std::string& filename) {
  trfp = fopen(filename.c_str(), "w");
  assert(trfp);
  boolector_set_trapi(c_btor_, trfp);
}

void BtorWrapper::printModel() const {
  char fmt[5] = "smt2"; // why is this not const char* 
  boolector_print_model(c_btor_, fmt, stderr);
}

void BtorWrapper::DumpBenchmark(std::ostream& os) const {
  auto *file = wrapostream(os);
  boolector_dump_smt2(c_btor_, file);
  fclose(file);
}

void BtorWrapper::Print(std::ostream& os) const {
  auto *file = wrapostream(os);
  boolector_dump_smt2(c_btor_, file);
  fclose(file);
}

void BtorWrapper::printAssertions() const {
  //    boolector_dump_smt2(c_btor_, wrapostream(cerr));
  //    boolector_dump_smt2(c_btor_, wraplogger(log));
  stringstream ss;
  boolector_dump_smt2(c_btor_, wrapstringstream(&ss));
  logger.Log(4, "boolector assertions:\n{}", ss.str());
  //log->debug("boolector has {} assertions:", assertions.size());
  //size_t num = 0;
  //for (auto assertion : assertions)
  //  log->debug("assertion {}: {}\n", ++num, assertion);
  //log->debug("boolector has {} assumptions:", assumptions.size());
  //num = 0;
  //for (auto assump : assumptions) {
  //  log->debug("assumption {}: {}\n", ++num, assump);
  //}
}

void BtorWrapper::add(BoolectorNode *n) {
  boolector_assert(c_btor_, n);
}

void BtorWrapper::assume(BoolectorNode *n) {
  assumptions.push_back(Wrap(n));
  boolector_assume(c_btor_, n);
}



/*-----------------------------------------------------------------------------------*/
// assignments

BtorArrayAssignment::BtorArrayAssignment(BtorWrapper& b, const BoolectorNodeWrapper& n)
  : BtorAssignment(BtorAssignment::kind::Array, b,
                   boolector_get_symbol(n.btor(), n.c_node_)),
    ptrSize(boolector_get_index_width(n.btor(), n.c_node_)),
    valSize(boolector_get_width(n.btor(), n.c_node_)) {
  assert(b.c_btor_ == n.btor());
  char **i;
  char **v;
  uint32_t size;
  boolector_array_assignment(b.c_btor_, n.c_node_, &i, &v, &size);
  if (size == 1 && i[0][0] == '*') {
    // constant array
    string val(v[0]);
    assert(val.size() == valSize);
    const_value_ = val;
    boolector_free_array_assignment(b.c_btor_, i, v, size);
    return;
  }
  
  indices_.reserve(size);
  values_.reserve(size);
  for (uint32_t j = 0; j < size; j++) {
    string idx(i[j]);
    string val(v[j]);
    assert(idx.size() == ptrSize);
    assert(val.size() == valSize);
    indices_.emplace_back(idx);
    values_.emplace_back(val);
  }
  // Fills the vector idx_val_pairs_ with the corresponding pairs from indices_
  // and values.
  idx_val_pairs_.reserve(size);
  using IdxValTuple = boost::tuple<string&,string&>;
  std::for_each(
      boost::make_zip_iterator(
          boost::make_tuple(indices_.begin(), values_.begin())),
      boost::make_zip_iterator(
          boost::make_tuple(indices_.end(), values_.end())),
      [&](const IdxValTuple& t) {
          idx_val_pairs_.emplace_back(std::make_pair(boost::get<0>(t),
                                                     boost::get<1>(t)));
      });
  assert(idx_val_pairs_.size() == size);
  struct {
    bool operator()(const pair<string,string>& iv0,
                    const pair<string,string>& iv1) {
      return std::get<0>(iv0) < std::get<0>(iv1);
    }
  } compare_on_indices;
  // Sorts the array of pairs so that lambdas are equivalent if they're
  // identical (see AsExpr).
  std::sort(idx_val_pairs_.begin(), idx_val_pairs_.end(), compare_on_indices);
  if (size)
    boolector_free_array_assignment(b.c_btor_, i, v, size);
}

BtorArrayAssignment::~BtorArrayAssignment() = default;



static z3::expr bvValExpr(z3::context& ctx, const std::string& ass) {
  int width = static_cast<int>(ass.size());
  bool bits[width];
  for (int i = 0, j = width-1; i < width; i++, j--) {
    bool bit = bool(ass[i] - '0');
    bits[j] = bit;
  }
  return ctx.bv_val(width, bits);
}


z3::expr BtorArrayAssignment::AsExpr(const z3::expr& arr_in) const {
  if (const_value_) {
    return z3::const_array(arr_in.ctx().bv_sort(ptrSize),
                           bvValExpr(arr_in.ctx(), *const_value_));
  }

  assert(indices_.size() == values_.size());
  // assert(bool(arr_in));
  z3::expr arr(arr_in.ctx());
  unsigned i = 0;
  for (auto&& iv_pair : idx_val_pairs_) {
    auto idx = bvValExpr(arr.ctx(), iv_pair.first);
    auto val = bvValExpr(arr.ctx(), iv_pair.second);
    auto var = arr.ctx().constant(("x" + to_string(i++)).c_str(), idx.get_sort());
    if (!bool(arr)) {
      arr = z3::lambda(var,
                       z3::ite(var == idx, val,
                               arr.ctx().bv_val(0, val.get_sort().bv_size())));
    } else {
      arr = z3::lambda(var, z3::ite(var == idx, val, z3::select(arr, idx)));
    }
  }
  return arr;
}


z3::expr BtorArrayAssignment::AsConstraint(const z3::expr& var) const {
  if (const_value_) {
    return var == AsExpr(var);
  }
  assert(indices_.size() == values_.size());
  z3::expr_vector v(var.ctx());
  ExprVectorInserter out(v);
  for (unsigned i = 0; i < indices_.size(); i++) {
    auto idx = bvValExpr(var.ctx(), indices_[i]);
    auto val = bvValExpr(var.ctx(), values_[i]);
    *out++ = z3::select(var, idx) == val;
  }
  return expr_mk_and(v);
}


static bool bitStringToVal(const std::string& index, uint64_t &val) {
  if (index.size() <= 64) {
    val = static_cast<uint64_t>(strtoll(index.c_str(), nullptr, 2));
    return true;
  }
  return false;
}

void BtorArrayAssignment::print(std::ostream& os) const {
  assert(indices_.size() == values_.size());
  if (symbol) {
    os << symbol;
  }
  os << " btor array: [index] = value" << endl;
  if (const_value_) {
    os << "[*] = " << *const_value_ << ";" << std::endl;
  } else {
    for (unsigned i = 0; i < indices_.size(); i++) {
      auto& idx = indices_[i];
      auto& val = values_[i];
      os << "[" << idx << "] = " << val << ";" << std::endl;
    }
    os << "[ ... else ... ] = 0";
  }
}

z3::expr BtorBvAssignment::AsExpr(const z3::expr& e) const {
  if (e.is_bool()) {
    return e.ctx().bool_val(ass[0] == '1');
  }
  return bvValExpr(e.ctx(), ass);
}
  
z3::expr BtorBvAssignment::AsConstraint(const z3::expr& var) const {
  auto expr = AsExpr(var);
  return expr == var;
}


void BtorBvAssignment::print(ostream& os) const {
  if (symbol && width == 1) {
    if (strcmp(ass, "0") == 0) {
      os << "!";
    }
    os << symbol;
  } else {
    if (symbol)
      os << "<" << width << ">" << symbol << " = " << ass;
    else
      os << "<" << width << "> = " << ass;
  }
}

std::ostream& operator<<(std::ostream& os, const BtorAssignment& a) {
  a.print(os);
  return os;
}


/*-----------------------------------------------------------------------------------*/
// boolector rewriter

Z3ToBtorRewriter::Z3ToBtorRewriter(std::shared_ptr<BtorWrapper> b) : B(b) {}
  
BoolectorNodeWrapper Z3ToBtorRewriter::visitExpr(const z3::expr& n) {
  Z3_decl_kind k;
  // function that does the shift
  function<BoolectorNodeWrapper(const BoolectorNodeWrapper&,
                                const BoolectorNodeWrapper&)> shift =
      [&](const BoolectorNodeWrapper& n,
          const BoolectorNodeWrapper& shift_amount) {
        if (k == Z3_OP_BSHL) { return n.shl(shift_amount); }
        else if (k == Z3_OP_BASHR) { return n.ashr(shift_amount); }
        else if (k == Z3_OP_BLSHR) { return n.lshr(shift_amount); }
        else { EUFORIA_FATAL("unhandled kind: {}", k); }
      };
  // function that does sign/zero extension
  function<BoolectorNodeWrapper(const BoolectorNodeWrapper&, int)> extend =
      [&](const BoolectorNodeWrapper& n, int extend_amount) {
        if (k == Z3_OP_BSHL) { return n.uext(extend_amount); }
        else if (k == Z3_OP_BASHR) { return n.sext(extend_amount); }
        else if (k == Z3_OP_BLSHR) { return n.uext(extend_amount); }
        else { EUFORIA_FATAL("unhandled kind: {}", k); }
      };
  switch ((k = n.decl().decl_kind())) {
    case Z3_OP_BSHL:
    case Z3_OP_BASHR:
    case Z3_OP_BLSHR: {
      BoolectorNodeWrapper ret;
      assert(n.num_args() == 2);
      const auto& val = Arg(n,0);
      const auto& arg1 = Arg(n,1);
      const unsigned val_width = val.width();
      bitset<sizeof(val_width)*8> bits(val_width);
      // Boolector only supports shifting bit vectors of power-of-two size, but
      // Z3 allows you to shift any bit width vector. To express non
      // powers-of-two in Boolector, we extend the BV to the nearest
      // power-of-two size, shift it, and truncate the result.
      if (bits.count() != 1) {
        auto exp = ceil(log2(val_width));
        // Get the next highest power of two size
        auto new_width = pow(2, exp);
        logger.Log(7, "exp {}", exp);
        logger.Log(7, "bits {}", bits);
        logger.Log(7, "val {}", val);
        logger.Log(7, "val_width {}", val_width);
        logger.Log(7, "arg1 {}", arg1);
        logger.Log(7, "new_width {}", new_width);
        // Extends the value, shifts it, then chops off the top bits
        auto val_extended = extend(val, new_width - val_width);
        auto shift_amount = arg1.slice(exp-1, 0);
        ret = shift(val_extended, shift_amount);
        ret = ret.slice(val_width-1, 0);
        logger.Log(7, "ret.width() {}", ret.width());
      } else {
        auto hi = log2pow2(val_width)-1;
        const auto& shift_amount = arg1.slice(hi, 0);
        ret = shift(val, shift_amount);
        assert(ret.width() == n.get_sort().bv_size());
      }
      assert(ret.width() == n.get_sort().bv_size());
      return ret;
      break;
    }

    default:
      break;
  }
  std::ostringstream ss;
  ss << n;
  EUFORIA_FATAL(fmt::format("no generic handling: {}", ss.str()));
}


BoolectorNodeWrapper Z3ToBtorRewriter::visitUNINTERPRETED(const z3::expr& e) {
  const auto decl = e.decl();
  const auto name = decl.name().str();
  if (e.is_bool()) {
    // Boolean variable
    if (e.num_args() == 0) {
      return B->boolvar(e.decl().name().str().c_str());
    }
    EUFORIA_FATAL("unhandled Boolean function");
  } else if (e.is_bv()) {
    // Function returning a bit vector
    if (e.num_args() == 2) {
      // GROSS stuff
      // So Z3 turns perfectly good (bvsrem ...) ops into uninterpreted function calls.
      // This is because division by zero is undefined.
      // By the way it ALSO turns (ite (not (= x 0)) (/ y x) 0) into uninterpreted calls.
      // Anyhow, here we use the real boolector functions.
      if (starts_with(name, "bvsrem")) {
        return Arg(e,0).srem(Arg(e,1));
      } else if (starts_with(name, "bvsmod")) {
        return Arg(e,0).srem(Arg(e,1));
      } else if (starts_with(name, "bvsdiv")) {
        return Arg(e,0) / Arg(e,1);
      } else if (starts_with(name, "bvurem")) {
        return Arg(e,0).urem(Arg(e,1));
      } else if (starts_with(name, "bvudiv")) {
        return Arg(e,0).udiv(Arg(e,1));
      }
    }
    // Bit vector variable
    if (decl.is_const()) {
      return B->var(e.get_sort().bv_size(), name);
    } else {
      // Uninterpreted function returning a BV
      vector<BoolectorSort> param_sorts;
      for (unsigned i = 0; i < decl.arity(); i++) {
        param_sorts.push_back(TranslateSort(decl.domain(i)));
      }
      BoolectorSort ret_sort = TranslateSort(decl.range());
      auto uf_sort = B->fun_sort(param_sorts.data(), param_sorts.size(),
                                 ret_sort);
      return B->uf(uf_sort, name);
    }
  } else if (e.is_array()) {
    return B->array(e.decl().name().str(),
                   e.get_sort().array_domain().bv_size(),
                   e.get_sort().array_range().bv_size());
  }
  EUFORIA_FATAL("unimplemented");
}


BoolectorSort Z3ToBtorRewriter::TranslateSort(const z3::sort& s) const {
  switch (s.sort_kind()) {
    case Z3_BOOL_SORT:
      return B->bool_sort();
    case Z3_BV_SORT:
      return B->bitvec_sort(s.bv_size());
    case Z3_ARRAY_SORT: {
      auto index_sort = TranslateSort(s.array_domain());
      auto value_sort = TranslateSort(s.array_range());
      return B->array_sort(index_sort, value_sort);
    }
    default: {
      EUFORIA_FATAL(fmt::format("Boolector doesn't support this sort: {}",
                                s));
    }
  }
}


//  int uniqParam = 0;
BoolectorNodeWrapper Z3ToBtorRewriter::visitCONST_ARRAY(const z3::expr& e) {
  return B->const_array(e.get_sort().array_domain().bv_size(),
                        Arg(e, 0));

  // use a lambda \x. 0 to send all reads to zero
  // this is currently unsupported by boolector :(
//    auto ptrSort = boolector_bitvec_sort(B->c_btor_, sort.array_domain().bv_size());
//    auto x = B->param(ptrSort, "ptr_in" + to_string(++uniqParam));
//    vector<BoolectorNodeWrapper> params({x});
//    auto zero = B->cint(0, sort.array_range().bv_size());
//    return B->fun(params, zero);
}

BoolectorNodeWrapper Z3ToBtorRewriter::visitDISTINCT(const z3::expr& n) {
  BoolectorNodeWrapper ret;
  for (unsigned i = 0; i < n.num_args(); i++) {
    for (unsigned j = i+1; j < n.num_args(); j++) {
      auto ne = Arg(n, i).ne(Arg(n, j));
      ret = !ret.is_null() ? ret && ne : ne;
    }
  }
  assert(!ret.is_null());
  return ret;
}
BoolectorNodeWrapper Z3ToBtorRewriter::visitAND(const z3::expr& n) {
  BoolectorNodeWrapper ret = Arg(n,0);
  for (unsigned i = 1; i < n.num_args(); i++) {
    ret = ret && Arg(n,i);
  }
  return ret;
}
BoolectorNodeWrapper Z3ToBtorRewriter::visitOR(const z3::expr& n) {
  BoolectorNodeWrapper ret = Arg(n,0);
  for (unsigned i = 1; i < n.num_args(); i++) {
    ret = ret || Arg(n,i);
  }
  return ret;
}

#define BTOR_BINARY_HANDLER(KIND, EXPR) \
BoolectorNodeWrapper Z3ToBtorRewriter::visit##KIND(const z3::expr& n) { \
  assert(n.num_args() == 2); \
  BoolectorNodeWrapper ret(EXPR); \
  assert(ret.width() > 0); \
  assert(!n.is_bv() || (static_cast<unsigned>(ret.width()) == n.get_sort().bv_size())); \
  assert(!n.is_bool() || (ret.width() == 1)); \
  return ret; \
}

#define BTOR_TERNARY_HANDLER(KIND, EXPR) \
BoolectorNodeWrapper Z3ToBtorRewriter::visit##KIND(const z3::expr& n) { \
  assert(n.num_args() == 3); \
  BoolectorNodeWrapper ret(EXPR); \
  assert(ret.width() > 0); \
  assert(!n.is_bv() || (static_cast<unsigned>(ret.width()) == n.get_sort().bv_size())); \
  assert(!n.is_bool() || (ret.width() == 1)); \
  return ret; \
}

#define BTOR_RASSOC_HANDLER(KIND, COP) \
BoolectorNodeWrapper Z3ToBtorRewriter::visit##KIND(const z3::expr& n) { \
  BoolectorNodeWrapper ret(Arg(n,0)); \
  for (unsigned i = 1; i < n.num_args(); i++) { \
    ret = COP(ret, Arg(n,i)); \
  } \
  return ret; \
}

BoolectorNodeWrapper Z3ToBtorRewriter::visitTRUE(const z3::expr&) {
  return B->boolVal(true);
}
BoolectorNodeWrapper Z3ToBtorRewriter::visitFALSE(const z3::expr&) {
  return B->boolVal(false);
}
BoolectorNodeWrapper Z3ToBtorRewriter::visitNOT(const z3::expr& n) {
  assert(n.num_args() == 1);
  return !Arg(n,0);
}

BoolectorNodeWrapper Z3ToBtorRewriter::visitBIT2BOOL(const z3::expr& e) {
  assert(Z3_get_decl_num_parameters(Z3_context(e.ctx()), Z3_func_decl(e.decl())) == 1);
  auto bit_idx = Z3_get_decl_int_parameter(Z3_context(e.ctx()), Z3_func_decl(e.decl()), 0);
  auto tgt = Arg(e, 0);
  auto ret = tgt.slice(bit_idx, bit_idx);
  assert(ret.width() == 1);
  return ret;
}

//  BTOR_BINARY_HANDLER(EQ, Arg(n, 0).eq(Arg(n, 1)));
BoolectorNodeWrapper Z3ToBtorRewriter::visitEQ(const z3::expr& n) {
  assert(n.num_args() == 2);

  BoolectorNodeWrapper ret(Arg(n, 0) == (Arg(n, 1)));

  assert(!n.is_bv() || (ret.width() == n.get_sort().bv_size()));
  assert(!n.is_bool() || (ret.width() == 1));
  return ret;
}



BTOR_BINARY_HANDLER(IFF, Arg(n, 0).iff(Arg(n, 1)));
BTOR_TERNARY_HANDLER(ITE, ite(Arg(n, 0), Arg(n, 1), Arg(n, 2)));
BTOR_BINARY_HANDLER(IMPLIES, Arg(n, 0).implies(Arg(n, 1)));
BTOR_BINARY_HANDLER(XOR, Arg(n, 0) ^ Arg(n, 1));


// *** bit vector

BoolectorNodeWrapper Z3ToBtorRewriter::visitBNUM(const z3::expr& n) {
  string numstr;
  auto b = n.is_numeral(numstr);
  assert(b);
  _unused(b);
  mpz_class num(numstr);
  string binstr = num.get_str(2);
  assert(binstr.size() <= n.get_sort().bv_size());
  string bits(n.get_sort().bv_size(), '0');
  copy(binstr.begin(), binstr.end(),
       bits.begin() + (bits.size() - binstr.size()));
  assert(bits.size() == n.get_sort().bv_size());
  
  //unsigned long long i = 0;
  //b = Z3_get_numeral_uint64(Z3_context(n.ctx()), Z3_ast(n), &i);
  //assert(b == Z3_TRUE);
  //string allBits;
  //for (unsigned j = 0; j < n.get_sort().bv_size(); j++) {
  //  allBits.push_back((i>>j) & 1 ? '1' : '0');
  //}
  //std::reverse(begin(allBits), end(allBits));
  //logger.Log(3, "allbits is {}", allBits);
  //assert(allBits == bits);
  //assert(allBits.size() == n.get_sort().bv_size());
  return B->bconst(bits.c_str());
}

BoolectorNodeWrapper Z3ToBtorRewriter::visitCONCAT(const z3::expr& n) {
  BoolectorNodeWrapper ret = Arg(n,0);
  for (unsigned i = 1; i < n.num_args(); i++) {
    ret = ret.concat(Arg(n,i));
  }
  assert(ret.width() == n.get_sort().bv_size());
  return ret;
}

BoolectorNodeWrapper Z3ToBtorRewriter::visitEXTRACT(const z3::expr& e) {
  // extract in z3 uses "parameters" not "arguments" to specify the hi and lo for extracting
  assert(Z3_get_decl_num_parameters(Z3_context(e.ctx()), Z3_func_decl(e.decl())) == 2);
  auto hi = Z3_get_decl_int_parameter(Z3_context(e.ctx()), Z3_func_decl(e.decl()), 0);
  auto lo = Z3_get_decl_int_parameter(Z3_context(e.ctx()), Z3_func_decl(e.decl()), 1);
  auto tgt = Arg(e, 0);
  auto ret = tgt.slice(hi, lo);
  assert(ret.width() == e.get_sort().bv_size());
  return ret;
}

BoolectorNodeWrapper Z3ToBtorRewriter::visitSIGN_EXT(const z3::expr& e) {
  assert(Z3_get_decl_num_parameters(e.ctx(), e.decl()) == 1);
  auto addedBits = Z3_get_decl_int_parameter((e.ctx()), (e.decl()), 0);
  auto tgt = Arg(e, 0);
  auto ret = tgt.sext(addedBits);
  assert(ret.width() == e.get_sort().bv_size());
  return ret;
}

BoolectorNodeWrapper Z3ToBtorRewriter::visitZERO_EXT(const z3::expr& e) {
  assert(Z3_get_decl_num_parameters(e.ctx(), e.decl()) == 1);
  auto added_bits = Z3_get_decl_int_parameter((e.ctx()), (e.decl()), 0);
  auto tgt = Arg(e, 0);
  auto ret = tgt.uext(added_bits);
  assert(ret.width() == e.get_sort().bv_size());
  return ret;
}

BoolectorNodeWrapper Z3ToBtorRewriter::visitBNOT(const z3::expr& n) {
  assert(n.num_args() == 1);
  BoolectorNodeWrapper ret(Arg(n,0));
  ret = ~ret;
  assert(ret.width() == n.get_sort().bv_size());
  return ret;
}

BoolectorNodeWrapper Z3ToBtorRewriter::visitBNEG(const z3::expr& n) {
  assert(n.num_args() == 1);
  BoolectorNodeWrapper ret(Arg(n,0));
  ret = ret.negate();
  assert(ret.width() == n.get_sort().bv_size());
  return ret;
}

BTOR_BINARY_HANDLER(BSUB, Arg(n, 0) - Arg(n, 1));
BTOR_BINARY_HANDLER(BMUL, Arg(n, 0) * Arg(n, 1));
BTOR_BINARY_HANDLER(BUDIV, Arg(n, 0).udiv(Arg(n, 1)));
BTOR_BINARY_HANDLER(BUDIV_I, Arg(n, 0).udiv(Arg(n, 1)));
BTOR_BINARY_HANDLER(BSDIV, Arg(n, 0) / Arg(n, 1));
BTOR_BINARY_HANDLER(BSDIV_I, Arg(n, 0) / Arg(n, 1));
BTOR_BINARY_HANDLER(BSMOD, Arg(n, 0) % Arg(n, 1));
BTOR_BINARY_HANDLER(BSMOD_I, Arg(n, 0) % Arg(n, 1));
BTOR_BINARY_HANDLER(BSREM, Arg(n, 0).srem(Arg(n, 1)));
BTOR_BINARY_HANDLER(BSREM_I, Arg(n, 0).srem(Arg(n, 1)));
BTOR_BINARY_HANDLER(BUREM, Arg(n, 0).urem(Arg(n, 1)));
BTOR_BINARY_HANDLER(BUREM_I, Arg(n, 0).urem(Arg(n, 1)));
BTOR_BINARY_HANDLER(SLT, Arg(n, 0) < Arg(n, 1));
BTOR_BINARY_HANDLER(SLEQ, Arg(n, 0) <= Arg(n, 1));
BTOR_BINARY_HANDLER(SGT, Arg(n, 0) > Arg(n, 1));
BTOR_BINARY_HANDLER(SGEQ, Arg(n, 0) >= Arg(n, 1));
BTOR_BINARY_HANDLER(ULT, Arg(n, 0).ult(Arg(n, 1)));
BTOR_BINARY_HANDLER(ULEQ, Arg(n, 0).ulte(Arg(n, 1)));
BTOR_BINARY_HANDLER(UGT, Arg(n, 0).ugt(Arg(n, 1)));
BTOR_BINARY_HANDLER(UGEQ, Arg(n, 0).ugte(Arg(n, 1)));
BoolectorNodeWrapper Z3ToBtorRewriter::visitBADD(const z3::expr& n) {
  BoolectorNodeWrapper ret(Arg(n,0));
  for (unsigned i = 1; i < n.num_args(); i++) {
    ret = ret + Arg(n,i);
  }
  assert(!n.is_bv() || (static_cast<unsigned>(ret.width()) == n.get_sort().bv_size()));
  return ret;
}
BoolectorNodeWrapper Z3ToBtorRewriter::visitBXOR(const z3::expr& n) {
  BoolectorNodeWrapper ret(Arg(n,0));
  for (unsigned i = 1; i < n.num_args(); i++) {
    ret = ret ^ Arg(n,i);
  }
  assert(ret.width() == n.get_sort().bv_size());
  return ret;
}
BoolectorNodeWrapper Z3ToBtorRewriter::visitBAND(const z3::expr& n) {
  BoolectorNodeWrapper ret(Arg(n,0));
  for (unsigned i = 1; i < n.num_args(); i++) {
    ret = ret & Arg(n,i);
  }
  assert(ret.width() == n.get_sort().bv_size());
  return ret;
}
BoolectorNodeWrapper Z3ToBtorRewriter::visitBOR(const z3::expr& n) {
  BoolectorNodeWrapper ret(Arg(n,0));
  for (unsigned i = 1; i < n.num_args(); i++) {
    ret = ret | Arg(n,i);
  }
  assert(ret.width() == n.get_sort().bv_size());
  return ret;
}

BTOR_BINARY_HANDLER(SELECT, read(Arg(n,0), Arg(n,1)));
BTOR_TERNARY_HANDLER(STORE, write(Arg(n,0), Arg(n,1), Arg(n,2)));
  
#undef BTOR_BINARY_HANDLER
#undef BTOR_TERNARY_HANDLER
#undef BTOR_RASSOC_HANDLER

}

void mylog(const boolector::BoolectorNodeWrapper& n) {
  cerr << n;
}

