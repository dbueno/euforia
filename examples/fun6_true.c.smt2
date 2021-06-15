(set-info :original "fun5_false.c.ll")
(set-info :authors "SeaHorn v.0.1.0-rc3")
(declare-rel verifier.error (Bool Bool Bool ))
(declare-rel g@_1 ((_ BitVec 32) ))
(declare-rel g@.split ((_ BitVec 32) (_ BitVec 32) ))
(declare-rel g (Bool Bool Bool (_ BitVec 32) (_ BitVec 32) ))
(declare-rel f@_1 ((_ BitVec 32) ))
(declare-rel f@.split ((_ BitVec 32) (_ BitVec 32) ))
(declare-rel f (Bool Bool Bool (_ BitVec 32) (_ BitVec 32) ))
(declare-rel main@_1 ((_ BitVec 32) ))
(declare-rel main@_call3 ())
(declare-rel main@_call4 ())
(declare-var g@%_3_0 (_ BitVec 32) )
(declare-var g@%_4_0 (_ BitVec 32) )
(declare-var |select(g@%_call, @a)_0| (_ BitVec 32) )
(declare-var |select(g@%_store, @a)_0| (_ BitVec 32) )
(declare-var g@_1_0 Bool )
(declare-var g@.split_0 Bool )
(declare-var f@%_3_0 (_ BitVec 32) )
(declare-var f@%_4_0 (_ BitVec 32) )
(declare-var |select(f@%_store, @a)_0| (_ BitVec 32) )
(declare-var |select(f@%_call, @a)_0| (_ BitVec 32) )
(declare-var |select(f@%_call1, @a)_0| (_ BitVec 32) )
(declare-var f@_1_0 Bool )
(declare-var f@.split_0 Bool )
(declare-var @a_0 (_ BitVec 32) )
(declare-var @llvm.used_0 (_ BitVec 32) )
(declare-var |select(main@%_2, @a)_0| (_ BitVec 32) )
(declare-var |select(main@%_store, @a)_0| (_ BitVec 32) )
(declare-var |select(main@%_store1, @a)_0| (_ BitVec 32) )
(declare-var |select(main@%_call, @a)_0| (_ BitVec 32) )
(declare-var |select(main@%_call2, @a)_0| (_ BitVec 32) )
(declare-var main@%_7_0 (_ BitVec 32) )
(declare-var main@%_br_0 Bool )
(declare-var main@_1_0 Bool )
(declare-var main@_call3_0 Bool )
(declare-var main@_call4_0 Bool )
(rule (verifier.error false false false))
(rule (verifier.error false true true))
(rule (verifier.error true false true))
(rule (verifier.error true true true))
(rule (g true true true |select(g@%_call, @a)_0| |select(g@%_store, @a)_0|))
(rule (g false true true |select(g@%_call, @a)_0| |select(g@%_store, @a)_0|))
(rule (g false false false |select(g@%_call, @a)_0| |select(g@%_store, @a)_0|))
(rule (g@_1 |select(g@%_call, @a)_0|))
(rule (=> (and (g@_1 |select(g@%_call, @a)_0|)
         true
         (= g@%_3_0 |select(g@%_call, @a)_0|)
         (= g@%_4_0 (bvadd g@%_3_0 #x00000001))
         (= |select(g@%_store, @a)_0| g@%_4_0)
         (=> g@.split_0 (and g@.split_0 g@_1_0))
         g@.split_0)
    (g@.split |select(g@%_call, @a)_0| |select(g@%_store, @a)_0|)))
(rule (=> (g@.split |select(g@%_call, @a)_0| |select(g@%_store, @a)_0|)
    (g true false false |select(g@%_call, @a)_0| |select(g@%_store, @a)_0|)))
(rule (f true true true |select(f@%_call, @a)_0| |select(f@%_call1, @a)_0|))
(rule (f false true true |select(f@%_call, @a)_0| |select(f@%_call1, @a)_0|))
(rule (f false false false |select(f@%_call, @a)_0| |select(f@%_call1, @a)_0|))
(rule (f@_1 |select(f@%_call, @a)_0|))
(rule (=> (and (f@_1 |select(f@%_call, @a)_0|)
         true
         (= f@%_3_0 |select(f@%_call, @a)_0|)
         (= f@%_4_0 (bvadd f@%_3_0 #x00000001))
         (= |select(f@%_store, @a)_0| f@%_4_0)
         (g true
            false
            false
            |select(f@%_store, @a)_0|
            |select(f@%_call1, @a)_0|)
         (=> f@.split_0 (and f@.split_0 f@_1_0))
         f@.split_0)
    (f@.split |select(f@%_call, @a)_0| |select(f@%_call1, @a)_0|)))
(rule (=> (f@.split |select(f@%_call, @a)_0| |select(f@%_call1, @a)_0|)
    (f true false false |select(f@%_call, @a)_0| |select(f@%_call1, @a)_0|)))
(rule (main@_1 |select(main@%_2, @a)_0|))
(rule (=> (and (main@_1 |select(main@%_2, @a)_0|)
         true
         (bvugt @a_0 #x00000000)
         (bvugt @llvm.used_0 #x00000000)
         (= |select(main@%_store, @a)_0| #x00000000)
         (= |select(main@%_store1, @a)_0| #x00000000)
         (f true
            false
            false
            |select(main@%_store1, @a)_0|
            |select(main@%_call, @a)_0|)
         (f true
            false
            false
            |select(main@%_call, @a)_0|
            |select(main@%_call2, @a)_0|)
         (= main@%_7_0 |select(main@%_call2, @a)_0|)
         (= main@%_br_0 (= main@%_7_0 #x00000004))
         (=> main@_call3_0 (and main@_call3_0 main@_1_0))
         main@_call3_0
         (=> (and main@_call3_0 main@_1_0) (not main@%_br_0)))
    main@_call3))
(rule (=> (and (main@_1 |select(main@%_2, @a)_0|)
         true
         (bvugt @a_0 #x00000000)
         (bvugt @llvm.used_0 #x00000000)
         (= |select(main@%_store, @a)_0| #x00000000)
         (= |select(main@%_store1, @a)_0| #x00000000)
         (f true
            false
            false
            |select(main@%_store1, @a)_0|
            |select(main@%_call, @a)_0|)
         (f true
            false
            false
            |select(main@%_call, @a)_0|
            |select(main@%_call2, @a)_0|)
         (= main@%_7_0 |select(main@%_call2, @a)_0|)
         (= main@%_br_0 (= main@%_7_0 #x00000004))
         (=> main@_call4_0 (and main@_call4_0 main@_1_0))
         main@_call4_0
         (=> (and main@_call4_0 main@_1_0) main@%_br_0))
    main@_call4))
(query main@_call4)

