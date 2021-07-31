; run with
;
;   $ z3 -smt2 queens.smt
 
; declare the sorts of pos --- pos represents the chessboard (an 8x8 array) ,
; indexed by "(pos row column)":
; true  --- a queen is on [row, column]
; false --- a queen is not on [row, column]
(declare-fun pos (Int Int) Bool)
 
; a helper function that checks that 1 <= x <= 8
(define-fun is-in-range ((x Int)) Bool (and (> x 0) (<= x 8)))

; Sorry, I made it more readable for me as a beginner

; first, we say that in all rows, there is at least one queen 
(assert 
    (
        forall ((i Int)) 
        (
            => (is-in-range i) 
            (
                exists ((j Int)) 
                (
                    and (is-in-range j) (pos i j)
                ) 
            )
        )
    )
)
; second, we say that if a queen is on [k; l], then there is no queen on any [m; l] (for m != k) and on any [k; m] (for m != l)
(assert 
    (
        forall ((k Int)) 
        (
            forall ((l Int)) 
            (
                => (is-in-range k) 
                (
                    => (pos k l) 
                    (
                        forall ((m Int)) 
                        (
                            => (is-in-range m) (and 
                            (
                                => (not (= m k)) (not (pos m l))) 
                                (
                                    => (not (= m l)) (not (pos k m))
                                )
                            )
                        )
                    )
                )
            )
        )
    )
)
 
; ADD YOUR CONSTRAINTS HERE
;============================= START ==============

; third, we say that if a queen is on [k; l], then there is no queen on any [k - m; l + m],
; i. e. there is no other queen on all diagonals in a direction from right upper coner to left lower corner
(assert 
    (
        forall ((k Int)) 
        (
            forall ((l Int))
            (
                forall ((m Int))
                (
                    => 
                    (
                        and (is-in-range k) (is-in-range l) (is-in-range m)
                    ) 
                    (
                        => (pos k l)
                        (
                            =>
                            (
                                and (is-in-range (- k m)) (is-in-range (+ l m))
                            )
                            (
                                not (pos (- k m) (+ l m))
                            )
                        )
                    )
                )
            )
        )
    )
)

; finaly, we say that if a queen is on [k; l], then there is no queen on any [k + m; l + m],
; i. e. there is no other queen on all diagonals in a direction from left upper coner to right lower corner
(assert 
    (
        forall ((k Int)) 
        (
            forall ((l Int))
            (
                forall ((m Int))
                (
                    => 
                    (
                        and (is-in-range k) (is-in-range l) (is-in-range m)
                    )
                    (
                        => (pos k l)
                        (
                            =>
                            (
                                and (is-in-range (+ k m)) (is-in-range (+ l m))
                            )
                            (
                                not (pos (+ k m) (+ l m))
                            )
                        )
                    )
                )
            )
        )
    )
)

;============================= END ================
 
(declare-const y-pos-a Int)
(declare-const y-pos-b Int)
(declare-const y-pos-c Int)
(declare-const y-pos-d Int)
(declare-const y-pos-e Int)
(declare-const y-pos-f Int)
(declare-const y-pos-g Int)
(declare-const y-pos-h Int)
 
(assert (and (is-in-range y-pos-a) (pos 1 y-pos-a)))
(assert (and (is-in-range y-pos-b) (pos 2 y-pos-b)))
(assert (and (is-in-range y-pos-c) (pos 3 y-pos-c)))
(assert (and (is-in-range y-pos-d) (pos 4 y-pos-d)))
(assert (and (is-in-range y-pos-e) (pos 5 y-pos-e)))
(assert (and (is-in-range y-pos-f) (pos 6 y-pos-f)))
(assert (and (is-in-range y-pos-g) (pos 7 y-pos-g)))
(assert (and (is-in-range y-pos-h) (pos 8 y-pos-h)))
 
(check-sat)
(get-model)