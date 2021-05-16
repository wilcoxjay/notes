#lang racket

(require net/url)

(define the-url "http://jamesrwilcox.com/words.txt")

(define (fetch)
  (port->string (get-pure-port (string->url the-url))))

(define words (list->set (string-split (fetch))))

(define (check-word word)
  (set-member? words word))

(define (check-document document)
  (for ([word (in-list (string-split document))])
    (unless (check-word word)
      (printf "potential error: '~a'\n" word)))) 

;; (check-document "what attributes of this function are important to you? channeling my advisor, my first thought would be to copy paste my machine’s /usr/share/dict/words file into the function itself. hashtag zero-install.")
;; potential error: 'attributes'
;; potential error: 'you?'
;; potential error: 'advisor,'
;; potential error: 'machine’s'
;; potential error: '/usr/share/dict/words'
;; potential error: 'itself.'
;; potential error: 'hashtag'
;; potential error: 'zero-install.'
