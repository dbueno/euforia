; entry:
; i = 0;
; bb0: do { i += 3; }
; while (i < 5)
; bb1: assert(i < 7)
; bbsafe, bbunsafe

(declare-rel entry ())
(declare-rel bb0 (Int ))
(declare-rel bb1 (Int ))
(declare-rel bbsafe ())
(declare-rel bbunsafe ())
(declare-var i Int)
(declare-var x Int)
(rule entry)
(rule (=> (and entry (= i 0))
          (bb0 i)))
(rule (=> (and (bb0 i) (< i 5) (= x (+ i 3)))
          (bb0 x)))
(rule (=> (and (bb0 i) (not (< i 5)))
          (bb1 i)))
(rule (=> (and (bb1 i) (< i 7))
          bbsafe))
(rule (=> (and (bb1 i) (not (< i 7)))
          bbunsafe))
(query bbunsafe)

