; ;;; a bit of lockserv
; 
; (declare-sort node)
; 
; (declare-fun lock-msg (node) Bool)
; (declare-fun grant-msg (node) Bool)
; (declare-fun unlock-msg (node) Bool)
; (declare-fun holds-lock (node) Bool)
; (declare-fun server-holds-lock () Bool)
; 
; (push)
; (assert
;  (not
;   (=> (and (forall ((N node)) (not (lock-msg N)))
;           (forall ((N node)) (not (grant-msg N)))
;           (forall ((N node)) (not (unlock-msg N)))
;           (forall ((N node)) (not (holds-lock N)))
;           server-holds-lock)
;      (and (forall ((N1 node) (N2 node))
;                   (=> (and (holds-lock N1) (holds-lock N2))
;                      (= N1 N2)))))))
; 
; (check-sat)  ; hope for unsat
; (pop)
; 
; ;;; a bit of paxos
; 
; (declare-sort quorum)
; 
; (declare-fun member (node quorum) Bool)
; 
; (define-fun my-fun ((n node) (q1 quorum) (q2 quorum)) Bool
;   (and (member n q1)
;        (member n q2)))
; 
; (assert
;  (forall ((q1 quorum) (q2 quorum))
;          (exists ((n node))
;             (my-fun n q1 q2))))
; 



;;; bank account

; (declare-sort account)
; 
; (declare-fun balance (account) Int)
; (declare-fun balance-new (account) Int)
; 
; (define-fun deposit () Bool
;   (exists ((a account) (amount Int))
;      (and (>= amount 0)
;           (forall ((A account))
;                   (= (balance-new A)
;                      (ite (= A a)
;                           (+ (balance a) amount)
;                           (balance A)))))))
; 
; (define-fun withdraw () Bool
;   (exists ((a account) (amount Int))
;      (and (>= amount 0)
;           (<= amount (balance a))
;           (forall ((A account))
;                   (= (balance-new A)
;                      (ite (= A a)
;                           (- (balance a) amount)
;                           (balance A)))))))
; 
; (push)
; (assert
;  (not
;   (=> (and (forall ((a account)) (>= (balance a) 0))
;           (or deposit withdraw))
;      (forall ((a account)) (>= (balance-new a) 0)))))
; (check-sat)
; (pop)


;;; bank account replicated

(declare-sort node)
(declare-sort account)
(define-sort event () Bool)
(declare-sort event-set)

(declare-fun history (node) event-set)
(declare-fun member (event event-set) Bool)
(declare-fun balance (node account) Int)

; (define-fun deposit () Bool
;   (exists ((a account) (amount Int))
;      (and (>= amount 0)
;           (forall ((A account))
;                   (= (balance-new A)
;                      (ite (= A a)
;                           (+ (balance a) amount)
;                           (balance A)))))))
; 
; (define-fun withdraw () Bool
;   (exists ((a account) (amount Int))
;      (and (>= amount 0)
;           (<= amount (balance a))
;           (forall ((A account))
;                   (= (balance-new A)
;                      (ite (= A a)
;                           (- (balance a) amount)
;                           (balance A)))))))

; (push)
; (assert
;  (not
;   (=> (and (forall ((a account)) (>= (balance a) 0))
;           (or deposit withdraw))
;      (forall ((a account)) (>= (balance-new a) 0)))))
; (check-sat)
; (pop)
