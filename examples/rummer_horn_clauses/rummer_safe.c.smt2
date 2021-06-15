(set-info :original "/tmp/sea-t4UdLr/rummer_safe.pp.ms.o.bc")
(set-info :authors "SeaHorn v.0.1.0-rc3")
(declare-rel verifier.error (Bool Bool Bool ))
(declare-rel main@entry ())
(declare-rel main@tailrecurse.i (Int ))
(declare-rel main@f.exit.split ())
(declare-var main@%_4_0 Bool )
(declare-var main@%n.tr2.i_2 Int )
(declare-var main@%_1_0 Bool )
(declare-var main@%_2_0 Bool )
(declare-var main@entry_0 Bool )
(declare-var main@%_0_0 Int )
(declare-var main@tailrecurse.i.preheader_0 Bool )
(declare-var main@tailrecurse.i_0 Bool )
(declare-var main@%n.tr2.i_0 Int )
(declare-var main@%n.tr2.i_1 Int )
(declare-var main@f.exit_0 Bool )
(declare-var main@%accumulator.tr.lcssa.i_0 Bool )
(declare-var main@%accumulator.tr.lcssa.i_1 Bool )
(declare-var main@f.exit.split_0 Bool )
(declare-var main@%_3_0 Int )
(declare-var main@tailrecurse.i_1 Bool )
(declare-var main@f.exit.loopexit_0 Bool )
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
         (=> main@tailrecurse.i.preheader_0
             (and main@tailrecurse.i.preheader_0 main@entry_0))
         (=> (and main@tailrecurse.i.preheader_0 main@entry_0) main@%_2_0)
         (=> main@tailrecurse.i_0
             (and main@tailrecurse.i_0 main@tailrecurse.i.preheader_0))
         main@tailrecurse.i_0
         (=> (and main@tailrecurse.i_0 main@tailrecurse.i.preheader_0)
             (= main@%n.tr2.i_0 main@%_0_0))
         (=> (and main@tailrecurse.i_0 main@tailrecurse.i.preheader_0)
             (= main@%n.tr2.i_1 main@%n.tr2.i_0)))
    (main@tailrecurse.i main@%n.tr2.i_1)))
(rule (=> (and main@entry
         true
         (= main@%_1_0 (> main@%_0_0 (- 1)))
         main@%_1_0
         (= main@%_2_0 (> main@%_0_0 0))
         (=> main@f.exit_0 (and main@f.exit_0 main@entry_0))
         (=> (and main@f.exit_0 main@entry_0) (not main@%_2_0))
         (=> (and main@f.exit_0 main@entry_0)
             (= main@%accumulator.tr.lcssa.i_0 true))
         (=> (and main@f.exit_0 main@entry_0)
             (= main@%accumulator.tr.lcssa.i_1 main@%accumulator.tr.lcssa.i_0))
         (=> main@f.exit_0 (not main@%accumulator.tr.lcssa.i_1))
         (=> main@f.exit.split_0 (and main@f.exit.split_0 main@f.exit_0))
         main@f.exit.split_0)
    main@f.exit.split))
(rule (=> (and (main@tailrecurse.i main@%n.tr2.i_0)
         true
         (= main@%_3_0 (+ main@%n.tr2.i_0 (- 1)))
         (= main@%_4_0 (> main@%n.tr2.i_0 1))
         (=> main@tailrecurse.i_1
             (and main@tailrecurse.i_1 main@tailrecurse.i_0))
         main@tailrecurse.i_1
         (=> (and main@tailrecurse.i_1 main@tailrecurse.i_0) main@%_4_0)
         (=> (and main@tailrecurse.i_1 main@tailrecurse.i_0)
             (= main@%n.tr2.i_1 main@%_3_0))
         (=> (and main@tailrecurse.i_1 main@tailrecurse.i_0)
             (= main@%n.tr2.i_2 main@%n.tr2.i_1)))
    (main@tailrecurse.i main@%n.tr2.i_2)))
(rule (=> (and (main@tailrecurse.i main@%n.tr2.i_0)
         true
         (= main@%_3_0 (+ main@%n.tr2.i_0 (- 1)))
         (= main@%_4_0 (> main@%n.tr2.i_0 1))
         (=> main@f.exit.loopexit_0
             (and main@f.exit.loopexit_0 main@tailrecurse.i_0))
         (=> (and main@f.exit.loopexit_0 main@tailrecurse.i_0) (not main@%_4_0))
         (=> main@f.exit_0 (and main@f.exit_0 main@f.exit.loopexit_0))
         (=> (and main@f.exit_0 main@f.exit.loopexit_0)
             (= main@%accumulator.tr.lcssa.i_0 false))
         (=> (and main@f.exit_0 main@f.exit.loopexit_0)
             (= main@%accumulator.tr.lcssa.i_1 main@%accumulator.tr.lcssa.i_0))
         (=> main@f.exit_0 (not main@%accumulator.tr.lcssa.i_1))
         (=> main@f.exit.split_0 (and main@f.exit.split_0 main@f.exit_0))
         main@f.exit.split_0)
    main@f.exit.split))
(query main@f.exit.split)

