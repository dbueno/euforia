// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#include "supp/mathsat_supp.h"

#include "supp/statistics.h"

using namespace std;

void mylog(const euforia::mathsat::TermWrapper& t) {
  cerr << t;
}

namespace euforia {
namespace mathsat {

std::ostream& operator<<(std::ostream& os, const TermWrapper& t) {
  t.Print(os);
  return os;
}

z3::sort Z3TermRewriter::TranslateType(msat_env env, msat_type ty) {
  size_t bv_width;
  msat_type domain_ty, range_ty;
  if (msat_is_bool_type(env, ty)) {
    return ctx().bool_sort();
  } else if (msat_is_integer_type(env, ty)) {
    return ctx().int_sort();
  } else if (msat_is_bv_type(env, ty, &bv_width)) {
    return ctx().bv_sort(bv_width);
  } else if (msat_is_array_type(env, ty, &domain_ty, &range_ty)) {
    return ctx().array_sort(TranslateType(env, domain_ty),
                            TranslateType(env, range_ty));
  }
  EUFORIA_FATAL("untranslatable mathsat type");
}

z3::expr Z3TermRewriter::VisitTerm(const TermWrapper& t) {
  if (t.IsNumber()) {
    size_t width;
    if (t.IsBvType(&width)) {
      auto n = t.GetNumber(2);
      bool bits[width];
      for (unsigned i = 0; i < width; i++) {
        char bit_char = '0';
        if (i < n.size()) {
          bit_char = n[n.size() - 1 - i];
        }
        bits[i] = bit_char == '1' ? true : false;
      }
      auto ret = ctx().bv_val(static_cast<unsigned>(width), bits);
      return ret;
    }
    EUFORIA_FATAL("unhandled number");
  }

  auto name = t.Name();
  auto sort = TranslateType(t.Env(), t.Type());
  return ctx().constant(name.c_str(), sort);
}

z3::expr Z3TermRewriter::VisitTRUE(const TermWrapper&) {
  return ctx().bool_val(true);
}

z3::expr Z3TermRewriter::VisitFALSE(const TermWrapper&) {
  return ctx().bool_val(false);
}

z3::expr Z3TermRewriter::VisitAND(const TermWrapper& t) {
  z3::expr_vector v(ctx());
  ExprVectorInserter join(v);
  for (size_t i = 0; i < t.NumArgs(); i++) {
    *join++ = Arg(t, i);
  }
  return expr_mk_and(v);
}

z3::expr Z3TermRewriter::VisitOR(const TermWrapper& t) {
  z3::expr_vector v(ctx());
  ExprVectorInserter join(v);
  for (size_t i = 0; i < t.NumArgs(); i++) {
    *join++ = Arg(t, i);
  }
  return expr_mk_or(v);
}

z3::expr Z3TermRewriter::VisitNOT(const TermWrapper& t) {
  return expr_not(Arg(t, 0));
}

z3::expr Z3TermRewriter::VisitIFF(const TermWrapper& t) {
  assert(t.NumArgs() == 2);
  return Arg(t, 0) == Arg(t, 1);
}

z3::expr Z3TermRewriter::VisitPLUS(const TermWrapper& t) {
  z3::expr ret = Arg(t, 0);
  for (size_t i = 1; i < t.NumArgs(); i++) {
    ret = ret + Arg(t, i);
  }
  return ret;
}

z3::expr Z3TermRewriter::VisitTIMES(const TermWrapper& t) {
  z3::expr ret = Arg(t, 0);
  for (size_t i = 1; i < t.NumArgs(); i++) {
    ret = ret * Arg(t, i);
  }
  return ret;
}

z3::expr Z3TermRewriter::VisitDIVIDE(const TermWrapper& t) {
  assert(t.NumArgs() == 2);
  return Arg(t, 0) / Arg(t, 1);
}

z3::expr Z3TermRewriter::VisitLEQ(const TermWrapper& t) {
  assert(t.NumArgs() == 2);
  return Arg(t, 0) <= Arg(t, 1);
}

z3::expr Z3TermRewriter::VisitEQ(const TermWrapper& t) {
  assert(t.NumArgs() == 2);
  return Arg(t, 0) == Arg(t, 1);
}

z3::expr Z3TermRewriter::VisitITE(const TermWrapper& t) {
  return z3::ite(Arg(t, 0), Arg(t, 1), Arg(t, 2));
}

z3::expr Z3TermRewriter::VisitBV_CONCAT(const TermWrapper& t) {
  z3::expr_vector args(ctx());
  for (size_t i = 0; i < t.NumArgs(); i++) {
    args.push_back(Arg(t, i));
  }
  return z3::concat(args);
}

z3::expr Z3TermRewriter::VisitBV_EXTRACT(const TermWrapper& t) {
  size_t msb, lsb;
  auto b = msat_term_is_bv_extract(t.Env(), t.Term(), &msb, &lsb);
  assert(b);
  _unused(b);
  auto arg = Arg(t, 0);
  return arg.extract(msb, lsb);
}

z3::expr Z3TermRewriter::VisitBV_NOT(const TermWrapper& t) {
  return ~Arg(t, 0);
}

z3::expr Z3TermRewriter::VisitBV_AND(const TermWrapper& t) {
  assert(t.NumArgs() == 2);
  return Arg(t, 0) & Arg(t, 1);
}

z3::expr Z3TermRewriter::VisitBV_OR(const TermWrapper& t) {
  assert(t.NumArgs() == 2);
  return Arg(t, 0) | Arg(t, 1);
}

z3::expr Z3TermRewriter::VisitBV_XOR(const TermWrapper& t) {
  assert(t.NumArgs() == 2);
  return Arg(t, 0) ^ Arg(t, 1);
}

z3::expr Z3TermRewriter::VisitBV_ULT(const TermWrapper& t) {
  assert(t.NumArgs() == 2);
  return z3::ult(Arg(t, 0), Arg(t, 1));
}

z3::expr Z3TermRewriter::VisitBV_SLT(const TermWrapper& t) {
  assert(t.NumArgs() == 2);
  return Arg(t, 0) < Arg(t, 1);
}

z3::expr Z3TermRewriter::VisitBV_ULE(const TermWrapper& t) {
  assert(t.NumArgs() == 2);
  return z3::ule(Arg(t, 0), Arg(t, 1));
}

z3::expr Z3TermRewriter::VisitBV_SLE(const TermWrapper& t) {
  assert(t.NumArgs() == 2);
  return Arg(t, 0) <= Arg(t, 1);
}

z3::expr Z3TermRewriter::VisitBV_COMP(const TermWrapper& t) {
  return z3::ite(Arg(t, 0) == Arg(t, 1), ctx().bv_val(1, 1),
                 ctx().bv_val(0, 1));
}

z3::expr Z3TermRewriter::VisitBV_NEG(const TermWrapper& t) {
  return -Arg(t, 0);
}

z3::expr Z3TermRewriter::VisitBV_ADD(const TermWrapper& t) {
  auto ret = Arg(t, 0);
  for (size_t i = 1; i < t.NumArgs(); i++) {
    ret = ret + Arg(t, i);
  }
  return ret;
}

z3::expr Z3TermRewriter::VisitBV_SUB(const TermWrapper& t) {
  auto ret = Arg(t, 0);
  for (size_t i = 1; i < t.NumArgs(); i++) {
    ret = ret - Arg(t, i);
  }
  return ret;
}

z3::expr Z3TermRewriter::VisitBV_MUL(const TermWrapper& t) {
  auto ret = Arg(t, 0);
  for (size_t i = 1; i < t.NumArgs(); i++) {
    ret = ret * Arg(t, i);
  }
  return ret;
}

z3::expr Z3TermRewriter::VisitBV_UDIV(const TermWrapper& t) {
  assert(t.NumArgs() == 2);
  return z3::udiv(Arg(t, 0), Arg(t, 1));
}

z3::expr Z3TermRewriter::VisitBV_SDIV(const TermWrapper& t) {
  assert(t.NumArgs() == 2);
  return Arg(t, 0) / Arg(t, 1);
}

z3::expr Z3TermRewriter::VisitBV_UREM(const TermWrapper& t) {
  assert(t.NumArgs() == 2);
  return z3::urem(Arg(t, 0), Arg(t, 1));
}

z3::expr Z3TermRewriter::VisitBV_SREM(const TermWrapper& t) {
  assert(t.NumArgs() == 2);
  return z3::srem(Arg(t, 0), Arg(t, 1));
}

z3::expr Z3TermRewriter::VisitBV_LSHL(const TermWrapper& t) {
  return z3::shl(Arg(t, 0), Arg(t, 1));
}

z3::expr Z3TermRewriter::VisitBV_LSHR(const TermWrapper& t) {
  return z3::lshr(Arg(t, 0), Arg(t, 1));
}

z3::expr Z3TermRewriter::VisitBV_ASHR(const TermWrapper& t) {
  return z3::ashr(Arg(t, 0), Arg(t, 1));
}

z3::expr Z3TermRewriter::VisitBV_ZEXT(const TermWrapper& t) {
  size_t amount;
  auto b = msat_term_is_bv_zext(t.Env(), t.Term(), &amount);
  assert(b);
  _unused(b);
  return z3::zext(Arg(t, 0), amount);
}

z3::expr Z3TermRewriter::VisitBV_SEXT(const TermWrapper& t) {
  size_t amount;
  auto b = msat_term_is_bv_sext(t.Env(), t.Term(), &amount);
  assert(b);
  _unused(b);
  return z3::sext(Arg(t, 0), amount);
}

z3::expr Z3TermRewriter::VisitARRAY_READ(const TermWrapper& t) {
  stats_.num_array_read_++;
  auto idx = arg(t, 1);
  if (idx.is_numeral()) { stats_.num_array_read_numeral_idx_++; }
  return z3::select(Arg(t, 0), Arg(t, 1));
}

z3::expr Z3TermRewriter::VisitARRAY_WRITE(const TermWrapper& t) {
  stats_.num_array_write_++;
  auto z3_arr = arg(t, 0);
  if (z3_arr.is_app() && z3_arr.decl().decl_kind() == Z3_OP_STORE) {
    stats_.num_store_of_store_++;
  }
  auto z3_idx = arg(t, 1);
  if (z3_idx.is_numeral()) { stats_.num_array_write_numeral_idx_++; }
  auto z3_val = arg(t, 2);
  if (z3_val.is_numeral()) { stats_.num_array_write_numeral_val_++; }
  return z3::store(Arg(t, 0), Arg(t, 1), Arg(t, 2));
}


z3::expr Z3TermRewriter::VisitARRAY_CONST(const TermWrapper& t) {
  auto retty = TranslateType(
      t.Env(), msat_decl_get_return_type(msat_term_get_decl(t.Term())));
  auto constant = Arg(t, 0);
  return z3::const_array(retty.array_domain(), Arg(t, 0));
}


z3::expr Z3TermRewriter::VisitEXISTS(const TermWrapper& t) {
  auto arity = msat_decl_get_arity(t.Decl());
  assert(arity == 2);
  _unused(arity);
  return z3::exists(Arg(t, 0), Arg(t, 1));
}

void Z3TermRewriter::collect_statistics(Statistics *st) const {
  st->Update("num_array_stores", stats_.num_array_write_);
  st->Update("num_array_stores_of_stores", stats_.num_store_of_store_);
  st->Update("num_array_selects", stats_.num_array_read_);
  st->Update("num_array_selects_constant_index", stats_.num_array_read_numeral_idx_);
  st->Update("num_array_stores_constant_index", stats_.num_array_write_numeral_idx_);
  st->Update("num_array_stores_constant_value", stats_.num_array_write_numeral_val_);
}

}
}
