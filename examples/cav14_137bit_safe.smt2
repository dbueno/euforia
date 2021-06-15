(declare-fun X () (_ BitVec 137))
(declare-fun X+ () (_ BitVec 137))
(declare-fun Y () (_ BitVec 137))
(declare-fun Y+ () (_ BitVec 137))
(declare-fun MAXINT () (_ BitVec 137))
; :next defs for state vars
(define-fun .def0 () (_ BitVec 137) (! X :next X+))
(define-fun .def1 () (_ BitVec 137) (! Y :next Y+))
; initial state
(define-fun .def7 () Bool (= X #b00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))
(define-fun .def8 () Bool (= Y #b00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))
(define-fun .def9 () Bool (and .def7 .def8))
(define-fun .def10 () Bool (! .def9 :init true))
; transition relation
(define-fun .def14 () Bool (= MAXINT #b11111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111))
(define-fun .def15 () Bool 
            (= X+ (ite (bvugt Y X) X
                       (ite (or (= Y X) (not (= X MAXINT))) (bvadd X #b00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001)
                            Y))))
(define-fun .def16 () Bool
            (= Y+ (ite (= Y X) (bvadd Y #b00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001)
                       (ite (or (bvugt Y X) (not (= X MAXINT))) Y
                            X))))
(define-fun .def17 () Bool (and .def14 .def15 .def16))
(define-fun .def18 () Bool (! .def17 :trans true))
; property
(define-fun .def19 () Bool (bvule Y X))
(define-fun .def20 () Bool (! .def19 :invar-property 0))
(assert true)
