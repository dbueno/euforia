; entry:
; i = 0;
; bb0: do { i += 3; }
; while (i < 5)
; bb1: assert(i < 7)
; bbsafe, bbunsafe

(declare-rel entry ())
(declare-rel bb0 ((_ BitVec 32) ))
(declare-rel bb1 ((_ BitVec 32) ))
(declare-rel bbsafe ())
(declare-rel bbunsafe ())
(declare-var i (_ BitVec 32))
(declare-var x (_ BitVec 32))
(rule entry)
(rule (=> (and entry (= i #x00000000))
          (bb0 i)))
(rule (=> (and (bb0 i) (bvslt i #x00000005) (= x (bvadd i #x00000003)))
          (bb0 x)))
(rule (=> (and (bb0 i) (not (bvslt i #x00000005)))
          (bb1 i)))
(rule (=> (and (bb1 i) (bvslt i #x00000007))
          bbsafe))
(rule (=> (and (bb1 i) (not (bvslt i #x00000007)))
          bbunsafe))
(query bbunsafe)

