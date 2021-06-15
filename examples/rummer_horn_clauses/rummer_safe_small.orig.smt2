(set-info :original "/benchmarks/rummer_safe.c.bc")
(set-info :authors "SeaHorn v.0.1.0-rc3")
(declare-rel verifier.error (Bool Bool Bool ))
(declare-rel main@entry ())
(declare-rel main@tailrecurse.i.preheader (Int ))
(declare-rel main@tailrecurse.i (Int Int Int ))
(declare-rel main@f.exit.loopexit (Int Int ))
(declare-rel main@f.exit (Int Int ))
(declare-rel main@f.exit.split ())
(declare-var main@%_6_0 Int )
(declare-var main@%_7_0 Bool )
(declare-var main@%_5_0 Bool )
(declare-var main@%_1_0 Bool )
(declare-var main@%_2_0 Bool )
(declare-var main@%_0_0 Int )
(declare-var main@%accumulator.tr.lcssa.i_0 Int )
(declare-var main@%n.tr2.i_0 Int )
(declare-var main@%accumulator.tr1.i_0 Int )
(declare-var main@%_3_0 Int )
(declare-var main@%_4_0 Int )
(declare-var main@%n.tr2.i_1 Int )
(declare-var main@%accumulator.tr1.i_1 Int )
(declare-var main@%.lcssa_0 Int )
(rule (verifier.error false false false))
(rule (verifier.error false true true))
(rule (verifier.error true false true))
(rule (verifier.error true true true))
(rule main@entry)
(rule (=> (and main@entry
         true
         (= main@%_1_0 (> main@%_0_0 (- 1)))
         main@%_1_0
         (= main@%_2_0 (> main@%_0_0 0))
         main@%_2_0)
    (main@tailrecurse.i.preheader main@%_0_0)))
(rule (=> (and main@entry
         true
         (= main@%_1_0 (> main@%_0_0 (- 1)))
         main@%_1_0
         (= main@%_2_0 (> main@%_0_0 0))
         (not main@%_2_0)
         (= main@%accumulator.tr.lcssa.i_0 1))
    (main@f.exit main@%_0_0 main@%accumulator.tr.lcssa.i_0)))
(rule (=> (and (main@tailrecurse.i.preheader main@%_0_0)
         true
         (= main@%n.tr2.i_0 main@%_0_0)
         (= main@%accumulator.tr1.i_0 1))
    (main@tailrecurse.i main@%_0_0 main@%n.tr2.i_0 main@%accumulator.tr1.i_0)))
(rule (=> (and (main@tailrecurse.i
           main@%_0_0
           main@%n.tr2.i_0
           main@%accumulator.tr1.i_0)
         true
         (= main@%_3_0 (+ main@%n.tr2.i_0 (- 1)))
         (= main@%_4_0 (+ main@%accumulator.tr1.i_0 1))
         (= main@%_5_0 (> main@%n.tr2.i_0 1))
         main@%_5_0
         (= main@%n.tr2.i_1 main@%_3_0)
         (= main@%accumulator.tr1.i_1 main@%_4_0))
    (main@tailrecurse.i main@%_0_0 main@%n.tr2.i_1 main@%accumulator.tr1.i_1)))
(rule (=> (and (main@tailrecurse.i
           main@%_0_0
           main@%n.tr2.i_0
           main@%accumulator.tr1.i_0)
         true
         (= main@%_3_0 (+ main@%n.tr2.i_0 (- 1)))
         (= main@%_4_0 (+ main@%accumulator.tr1.i_0 1))
         (= main@%_5_0 (> main@%n.tr2.i_0 1))
         (not main@%_5_0)
         (= main@%.lcssa_0 main@%_4_0))
    (main@f.exit.loopexit main@%_0_0 main@%.lcssa_0)))
(rule (=> (and (main@f.exit.loopexit main@%_0_0 main@%.lcssa_0)
         true
         (= main@%accumulator.tr.lcssa.i_0 main@%.lcssa_0))
    (main@f.exit main@%_0_0 main@%accumulator.tr.lcssa.i_0)))
(rule (=> (and (main@f.exit main@%_0_0 main@%accumulator.tr.lcssa.i_0)
         true
         (= main@%_6_0 (+ main@%_0_0 1))
         (= main@%_7_0 (= main@%accumulator.tr.lcssa.i_0 main@%_6_0))
         (not main@%_7_0))
    main@f.exit.split))
(query main@f.exit.split)

