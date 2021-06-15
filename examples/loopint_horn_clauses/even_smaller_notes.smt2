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
; no constraint on entry+

(rule (=> (and entry (= i 0))
          (bb0 i)))
    ;; transition equations
    (= Int0+ (ite (and entry (= i 0)) i Int0))
    (= bb0+  (ite (and entry (= i 0)) true bb0))

(rule (=> (and (bb0 i) (< i 5) (= x (+ i 3)))
          (bb0 x)))
    ;; transition equations
    (= Int0+ (ite (and bb0 (= i Int0) (< i 5) (= x (+ i 3)))
                  x
                  Int0))
    (= bb0+  (ite (and bb0 (= i Int0) (< i 5) (= x (+ i 3)))
                  true
                  bb0))

(rule (=> (and (bb0 i) (not (< i 5)))
          (bb1 i)))
    ;; transition equations
    (= Int0+ (ite (and bb0 (= Int0 i) (not (< i 5)))
                  i
                  Int0))
    (= bb1+  (ite (and bb0 (= Int0 i) (not (< i 5)))
                  true
                  bb1))

(rule (=> (and (bb1 i) (< i 7))
          bbsafe))
    ;; transition equations
    (= bbsafe+ (ite (and bb1 (= Int0 i) (< i 7))
                    true
                    bbsafe))

(rule (=> (and (bb1 i) (not (< i 7)))
          bbunsafe))
    ;; transition equations
    (= bbunsafe+ (ite (and bb1 (= Int0 i) (not (< i 7)))
                      true
                      bbunsafe))

(query bbunsafe)


;; encoding assuming mutually exclusive bodies for every common head
;; it's important that the base case for the locations is false, the ite's tell
;; you when it's true
(init (not entry) (not bb0) (not bb1) (not bbsafe) (not bbunsafe)
(one-hot entry-bool)
(= entry+ (ite bool-entry true false))
(= bb0+  (ite (and bb0 (= i Int0) (< i 5) (= x (+ i 3)))
              true
              (ite (and entry (= i 0)) true false)))

(= Int0+ (ite (and bb0 (= Int0 i) (not (< i 5)))
              i
              (ite (and bb0 (= i Int0) (< i 5) (= x (+ i 3)))
                   x
                   (ite (and entry (= i 0)) i Int0))))
(= bb1+  (ite (and bb0 (= Int0 i) (not (< i 5)))
              true
              false))
(= bbsafe+ (ite (and bb1 (= Int0 i) (< i 7))
                true
                false))
(= bbunsafe+ (ite (and bb1 (= Int0 i) (not (< i 7)))
                  true
                  false))

;; So this would be better if we substituted any (= <state-var> <input>) terms
;; in the condition and the clause it guerds away. This is probably easier to
;; bake into the encoding than to recover later due to the recursive nature of
;; substitutions creating new substitution opportunities.
(init (not entry) (not bb0) (not bb1) (not bbsafe) (not bbunsafe))
;(one-hot entry-bool)
(= entry+ (ite entry-active true false))
(= bb0+  (ite (and bb0 (< Int0 5)) ;does this work? ;(= x (+ Int0 3)))
              true
              (ite (and entry) true false)))

(= Int0+ (ite (and bb0 (not (< Int0 5)))
              Int0
              (ite (and bb0 (< Int0 5))
                   (+ Int0 3)
                   (ite (and entry) 0 Int0))))
(= bb1+  (ite (and bb0 (not (< Int0 5)))
              true
              false))
(= bbsafe+ (ite (and bb1 (< Int0 7))
                true
                false))
(= bbunsafe+ (ite (and bb1 (not (< Int0 7)))
                  true
                  false))

;; working backward
bbunsafe

bb1 & 
Int0 != 7

bb0 &
Int
