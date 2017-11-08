(set-option :RLIMIT 500000)

(declare-sort Matrix 0)

;; A matrix is specified by its dimensions and the data at each in-bounds entry.

(declare-fun Matrix.rows (Matrix) Int)
(declare-fun Matrix.cols (Matrix) Int)

(declare-fun Matrix.get (Matrix Int Int) Real)


;; For example, we can define the identity matrix as a function of the dimension.

(declare-fun Matrix.id (Int Int) Matrix)

;; To "define" such a thing in this style, we say what its dimensions are and
;; what its data are.

;; The dimensions of the identity matrix are given by the arguments.

(assert
 (forall
  ((m Int) (n Int))
  (! (= (Matrix.rows (Matrix.id m n)) m)
     :pattern (Matrix.rows (Matrix.id m n)))))

(assert
 (forall
  ((m Int) (n Int))
  (! (= (Matrix.cols (Matrix.id m n)) n)
     :pattern (Matrix.rows (Matrix.id m n)))))

;; The data of the identity matrix by giving a formula in terms of the indices:
;;     diagonal entries are 1, off-diagonal are 0.

(assert
 (forall
  ((m Int) (n Int) (i Int) (j Int))
  (=> (<= 0 i) (< i m)
     (<= 0 j) (< j n)
     (= (Matrix.get (Matrix.id m n) i j)
        (ite (= i j) 1.0 0.0)))))


;; We can also define what it means to be a diagonal matrix:
;;     all off-diagonal entries are 0.


(declare-fun Matrix.diagonal? (Matrix) Bool)

(assert
 (forall
  ((M Matrix))
  (= (Matrix.diagonal? M)
     (forall
      ((i Int) (j Int))
      (=> (<= 0 i) (< i (Matrix.rows M))
         (<= 0 j) (< j (Matrix.cols M))
         (not (= i j))
         (= (Matrix.get M i j) 0.0))))))

;; We can prove a trivial theorem: the identity matrix (of any dimension) is diagonal.
(push)
(assert (not (forall ((n Int) (m Int)) (Matrix.diagonal? (Matrix.id n m)))))
(check-sat)  ; UNSAT
(pop)


