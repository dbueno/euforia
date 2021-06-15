(set-info :original "/benchmarks/rummer_safe.c.bc")
(set-info :authors "SeaHorn v.0.1.0-rc3")
(declare-rel verifier.error (Bool Bool Bool ))
(declare-rel main@entry ())
;; (declare-fun main@entry () Bool)
(declare-rel main@tailrecurse.i.preheader (Int ))
;; (declare-fun main@tailrecurse.i.preheader (Int) Bool)
(declare-rel main@tailrecurse.i (Int ))
;; (declare-fun main@tailrecurse.i (Int) Bool)
(declare-rel main@f.exit.loopexit ())
;; (declare-fun main@f.exit.loopexit () Bool)
(declare-rel main@f.exit (Bool ))
;; (declare-fun main@f.exit (Bool) Bool)
(declare-rel main@f.exit.split ())
;; (declare-fun main@f.exit (Bool) Bool)

;; the following remain Bools and Ints and so on
(declare-var main@%_4_0 Bool )
(declare-var main@%_1_0 Bool )
(declare-var main@%_2_0 Bool )
(declare-var main@%_0_0 Int )
(declare-var main@%accumulator.tr.lcssa.i_0 Bool )
(declare-var main@%n.tr2.i_0 Int )
(declare-var main@%_3_0 Int )
(declare-var main@%n.tr2.i_1 Int )
(rule (verifier.error false false false))
(rule (verifier.error false true true))
(rule (verifier.error true false true))
(rule (verifier.error true true true))

;; I = main@entry
(rule main@entry)

;; rule 1
(rule (=> (and main@entry
         true
         (= main@%_1_0 (> main@%_0_0 (- 1)))
         main@%_1_0
         (= main@%_2_0 (> main@%_0_0 0))
         main@%_2_0)
    (main@tailrecurse.i.preheader main@%_0_0)))
;; rule 2
(rule (=> (and main@entry
         true
         (= main@%_1_0 (> main@%_0_0 (- 1)))
         main@%_1_0
         (= main@%_2_0 (> main@%_0_0 0))
         (not main@%_2_0)
         (= main@%accumulator.tr.lcssa.i_0 true))
    (main@f.exit main@%accumulator.tr.lcssa.i_0)))
;; rule 3
(rule (=> (and (main@tailrecurse.i.preheader main@%_0_0)
         true
         (= main@%n.tr2.i_0 main@%_0_0))
    (main@tailrecurse.i main@%n.tr2.i_0)))
;; rule 4
(rule (=> (and (main@tailrecurse.i main@%n.tr2.i_0)
         true
         (= main@%_3_0 (+ main@%n.tr2.i_0 (- 1)))
         (= main@%_4_0 (> main@%n.tr2.i_0 1))
         main@%_4_0
         (= main@%n.tr2.i_1 main@%_3_0))
    (main@tailrecurse.i main@%n.tr2.i_1)))
;; rule 5
(rule (=> (and (main@tailrecurse.i main@%n.tr2.i_0)
         true
         (= main@%_3_0 (+ main@%n.tr2.i_0 (- 1)))
         (= main@%_4_0 (> main@%n.tr2.i_0 1))
         (not main@%_4_0))
    main@f.exit.loopexit))
;; rule 6
(rule (=> (and main@f.exit.loopexit true (= main@%accumulator.tr.lcssa.i_0 false))
    (main@f.exit main@%accumulator.tr.lcssa.i_0)))


;; rule 7
(rule (=> (and (main@f.exit main@%accumulator.tr.lcssa.i_0)
         true
         (not main@%accumulator.tr.lcssa.i_0))
    main@f.exit.split))

(query main@f.exit.split)

