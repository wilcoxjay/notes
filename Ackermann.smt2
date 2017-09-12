(declare-fun ackermann (Int Int) Int)

(assert (forall ((m Int) (n Int))
                (= (ackermann m n)
                   (ite (= m 0) (+ n 1)
                        (ite (= n 0) (ackermann (- m 1) 1)
                             (ackermann (- m 1) (ackermann m (- n 1))))))))

(declare-const m Int)
(declare-const n Int)

(assert (>= m 0))
(assert (>= n 0))

; Here's the induction hypothesis
(assert (forall ((ihm Int) (ihn Int))
                (=> (and (<= 0 ihm) (<= 0 ihn)
                         (or (< ihm m) (and (= ihm m) (< ihn n))))
                    (>= (ackermann ihm ihn) 0))))

(assert (not (>= (ackermann m n) 0)))
(check-sat) ; reports unsat as desired



