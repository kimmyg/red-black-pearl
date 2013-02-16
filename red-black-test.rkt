#lang racket/base
(require "red-black.rkt")

(define black-node?
  (match-lambda
    [(L) #t]
    [(N 'B _ _ _) #t]
    [_ #f]))

(define local-invariant?
  (match-lambda
    [(L) #t]
    [(N 'R a _ b)
     (and (black-node? a)
          (black-node? b)
          (local-invariant? a)
          (local-invariant? b))]
    [(N 'B a _ b)
     (and (local-invariant? a)
          (local-invariant? b))]))

(define global-invariant?
  (match-lambda
    [(L) 1]
    [(N (? (or/c 'R 'B) c) a _ b)
     (let ([a-length (global-invariant? a)]
           [b-length (global-invariant? b)])
       (and a-length
            b-length
            (= a-length b-length)
            (+ a-length (if (eq? c 'B) 1 0))))]
    [_ #f]))

(define (random-tree h [red-ok? #t])
  (if (and red-ok? (zero? (random 2)))
      (N 'R
         (random-tree h #f)
         #f
         (random-tree h #f))
      (if (= h 1)
          (L)
          (N 'B
             (random-tree (sub1 h) #t)
             #f
             (random-tree (sub1 h) #t)))))

(define (number-tree t [n 1])
  (match t
    [(L)
     (values t n)]
    [(N c l _ r)
     (let*-values ([(l n) (number-tree l n)]
                   [(v) n]
                   [(r n) (number-tree r (add1 n))])
       (values (N c l v r) n))]))

(define ts
  (list (N 'B (L) 1 (N 'R (L) 2 (L)))
        (N 'B (L) 1 (L))
        (N 'B (N 'R (L) 1 (L)) 2 (N 'R (L) 3 (L)))
        (N 'R (N 'B (L) 1 (L)) 2 (N 'B (L) 3 (N 'R (L) 4 (L))))))

;(random-numbered-tree 2)

(define (test-tree t)
  (for/and ([x (members t)])
    (with-handlers ([exn:fail? (λ (e)
                                 (print t)
                                 (newline)
                                 (print x)
                                 (newline)
                                 (raise e))])
      (let ([t- (delete t x <)])
        (and (not (member? t- x <))
             (or (global-invariant? t-) (error 'global "removing ~a from ~a to get ~a" x t t-))
             (or (local-invariant? t-) (error 'local "removing ~a from ~a to get ~a" x t t-)))))))




#;(for/and ([t ts])
  (test-tree t))

(define-syntax-rule (for/max ((ids es) ...) body ...)
  (for/fold ([m 0])
    ((ids es) ...)
    (max m (begin body ...))))

(for/and ([n 7])
  (let ([k (expt 2 (* (add1 n) 2))])
    (printf "testing trees of height ~a (~a times)..." (add1 n) k)
    (displayln (for/max ([i k])
                        (let-values ([(t n) (number-tree (random-tree (add1 n)))])
                          (test-tree t)
                          n)))
    (printf "done~n")))


(let/ec escape
  (displayln "deterministic insert")
  (for/and ([i 1000])
    (let ([t (for/fold ([t (L)])
               ([j i])
               (insert t j <))])
      (or (invariant? t)
          (escape t))))
  (displayln "passed"))

(let/ec escape
  (displayln "nondeterministic insert")
  (for/and ([i 1000])
    (let ([t (for/fold ([t (L)])
               ([j i])
               (insert t (random 1000) <))])
      (or (invariant? t)
          (escape t))))
  (displayln "passed"))

(let/ec escape
  (displayln "deterministic delete")
  (for/and ([i 100])
    (let ([t (for/fold ([t (L)])
               ([j i])
               (insert t j <))])
      (for/fold ([t t])
        ([j i])
        (let ([t- (delete-min t)])
          (if (invariant? t-)
              t-
              (escape t))))))
  (displayln "passed"))
