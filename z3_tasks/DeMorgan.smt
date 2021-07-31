;##################################################################
;   VUT, FIT, IAM, DU2: DeMorgan prove
;   Author:             David Mihola
;   Date:               4. 3. 2021
;   Usage:              z3 -smt2 DeMorgan.smt
;##################################################################

(declare-const x Bool)
(declare-const y Bool)
(define-fun DeMorgan () Bool
    (= (not 
         (or 
            (not x) (not y)
         )
       )
       (and x y)
    )
)
(assert (not DeMorgan)) ; UNSAT if DeMorgan law applies 
(check-sat)
