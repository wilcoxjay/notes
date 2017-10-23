(declare-const x Real)

(assert (< (* x x) 0.0))

(check-sat)

; (declare-fun sqrt (Real) Real)
; ; (assert (forall ((x Real)) (=> (>= x 0.0) (= (* (sqrt x) (sqrt x)) x))))
; (declare-const x Real)
; (assert (= x (sqrt 2.0)))
; 
; 
; (assert (= (* x x) 2.0))
; 
; (check-sat-using qfnra-nlsat)
; (get-model)
