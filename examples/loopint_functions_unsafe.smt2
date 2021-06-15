
; entry:
; i = 0;
; bb0: do { i += f(i,3); }
; while (i < 5)
; bb1: assert(i < 7)
; bbsafe, bbunsafe
;
; proc f(i,n):
; r = i
; j = n
; bb2: while (j > 0)
;   r += 1
;   n -= 1
; return r

(declare-rel B (Int ))
(declare-rel F (Int Int))
(declare-rel G (Int Int Int))
(declare-rel D (Int))
(declare-rel U ())
(declare-var i Int)
(declare-var j Int)
(declare-var r Int)
(rule (=> (= i 0)
          (B i)))
(rule (=> (and (B i) (< i 5) (F i r))
          (B r)))
(rule (=> (and (B i) (>= i 5))
          (D i)))
(rule (=> (and (= i r) (= j 0))
          (G i r j)))
(rule (=> (and (G i r j) (< j 3))
          (G i (+ r 1) (+ j 1))))
(rule (=> (and (G i r j) (>= j 3))
          (F i r)))
(rule (=> (and (D i) (>= i 6))
          U))
(query U)

