;##################################################################
;   VUT, FIT, IAM, DU2: Kinematic equation
;   Author:             David Mihola
;   Date:               4. 3. 2021
;   Usage:              z3 -smt2 Kinematic.smt
;##################################################################

(declare-const v Real)
(declare-const a Real)
(declare-const t Real)

(assert (= v 30))
(assert (= a 8))

(assert (= v (* a t)))
(define-fun Distance () Real
    (/
        (*
            a 
            (* 
                t t
            )
        )
        2
    )
)
(check-sat)
(get-model)
