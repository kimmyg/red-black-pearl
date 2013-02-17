#lang racket/base
(require racket/contract
         racket/list
         racket/match
         racket/port)

(provide empty-tree
         member?
         members
         min
         delete)

(struct RB-tree () #:transparent)
(struct L RB-tree () #:transparent)
(struct BB RB-tree () #:transparent)
(struct N RB-tree (color left-child value right-child) #:transparent)

(define empty-tree (L))

(define-syntax switch-compare
  (syntax-rules (= < >)
    [(_ (cmp e0 e1)
        [< rlt ...]
        [= req ...]
        [> rgt ...])
     (let ([v0 e0]
           [v1 e1])
       (cond
         [(cmp v0 v1)
          rlt ...]
         [(cmp v1 v0)
          rgt ...]
         [else
          req ...]))]))


(define (member? t v cmp)
  (match t
    [(L) #f]
    [(N _ a x b)
     (switch-compare
      (cmp v x)
      [< (member? a v cmp)]
      [= #t]
      [> (member? b v cmp)])]))

(define members
  (match-lambda
    [(L)
     empty]
    [(N _ a x b)
     (append (members a) (list x) (members b))]))

(define balance
  (match-lambda
    [(or (B! (R! (R! a x b) y c) z d)
         (B! (R! a x (R! b y c)) z d)
         (B! a x (R! (R! b y c) z d))
         (B! a x (R! b y (R! c z d))))
     (R! (B! a x b) y (B! c z d))]
    [(or (BB! (R! (R! a x b) y c) z d)
         (BB! (R! a x (R! b y c)) z d)
         (BB! a x (R! (R! b y c) z d))
         (BB! a x (R! b y (R! c z d))))
     (N 'B (B! a x b) y (B! c z d))]
    [t t]))

(define (insert t v cmp)
  (define (ins t v cmp)
    (match t
      [(L)
       (R! (L) v (L))]
      [(N c a x b)
       (switch-compare
        (cmp v x)
        [< (balance (N c (ins a v cmp) x b))]
        [= t]
        [> (balance (N c a x (ins b v cmp)))])]))
  (blacken (ins t v cmp)))

(define min
  (match-lambda
    [(L) (error 'min "empty tree")]
    [(N _ (L) x _) x]
    [(N _ a _ _) (min a)]))

(define-match-expander BB!
  (syntax-rules ()
    [(_ a) (or (and (BB) a)
               (and (N 'BB _ _ _) a))]
    [(_ a x b) (N 'BB a x b)])
  (syntax-rules ()
    [(_ a x b) (N 'BB a x b)]))

(define-match-expander B!
  (syntax-rules ()
    [(_ a) (or (and (L) a)
               (and (N 'B _ _ _) a))]
    [(_ a x b) (N 'B a x b)])
  (syntax-rules ()
    [(_ a x b) (N 'B a x b)]))

(define-match-expander R!
  (syntax-rules ()
    [(_ a) (and (N 'R _ _ _) a)]
    [(_ a x b) (N 'R a x b)])
  (syntax-rules ()
    [(_ a x b) (N 'R a x b)]))

(define -B
  (match-lambda
    [(BB) (L)]
    [(BB! a x b) (B! a x b)]
    [a (error '-B "unsupported node ~a" a)]))

(define rotate
  (match-lambda
    [(R! (BB! a) x (B! b y c))
     (balance (B! (R! (-B a) x b) y c))]
    [(R! (B! a x b) y (BB! c))
     (balance (B! a x (R! b y (-B c))))]
    
    [(B! (BB! a) x (B! b y c))
     (balance (BB! (R! (-B a) x b) y c))]
    [(B! (B! a x b) y (BB! c))
     (balance (BB! a x (R! b y (-B c))))]
    
    [(B! (R! (B! a) x (B! b y c)) z (BB! d))
     (B! a x (balance (B! b y (R! c z (-B d)))))]
    [(B! (BB! a) x (R! (B! b y c) z (B! d)))
     (B! (balance (B! (R! (-B a) x b) y c)) z d)]
    
    [t t]))

(define blacken
  (match-lambda
    [(R! (R! a) x b)
     (B! a x b)]
    [(R! a x (R! b))
     (B! a x b)]
    [t t]))

(define redden
  (match-lambda
    [(B! (B! a) x (B! b))
     (R! a x b)]
    [t t]))

(define (delete t v cmp)
  (define (del t v cmp)
    (match t
      [(L) (L)]
      [(R! (L) (== v) (L))
       (L)]
      [(B! (L) (== v) (L))
       (BB)]
      [(B! (R! a x b) (== v) (L))
       (B! a x b)]
      [(N c a x b)
       (switch-compare
        (cmp v x)
        [< (rotate (N c (del a v cmp) x b))]
        [= (let ([v (min b)])
             (rotate (N c a v (del b v cmp))))]
        [> (rotate (N c a x (del b v cmp)))])]))
  (del (redden t) v cmp))

(module+ test
  (define black-node?
    (match-lambda
      [(B! _) #t]
      [_ #f]))
  
  (define local-invariant?
    (match-lambda
      [(L) #t]
      [(R! a _ b)
       (and (black-node? a)
            (black-node? b)
            (local-invariant? a)
            (local-invariant? b))]
      [(B! a _ b)
       (and (local-invariant? a)
            (local-invariant? b))]))
  
  (define global-invariant?
    (match-lambda
      [(L) 1]
      [(N c a _ b)
       (let ([a-length (global-invariant? a)]
             [b-length (global-invariant? b)])
         (and a-length
              b-length
              (= a-length b-length)
              (+ a-length (if (eq? c 'B) 1 0))))]
      [_ #f]))
  
  (define (ordered? t)
    (let ([xs (members t)])
      (or (< (length xs) 2) (apply < xs))))
  
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
  
  (define (time-tree t)
    (let ([xs (members t)])
      (displayln (regexp-match
                  #px#""
                  (with-output-to-string
                   (λ ()
                     (time
                      (for ([x xs])
                        (delete t x <)))))))
      (time
       (for/fold ([t t])
         ([x xs])
         (delete t x <)))))
  
  (define (test-tree t)
    (let ([xs (members t)])
      (and (for/and ([x (members t)])
             (with-handlers ([exn:fail? (λ (e)
                                          (print t)
                                          (newline)
                                          (print x)
                                          (newline)
                                          (raise e))])
               (let ([t- (delete t x <)])
                 (and (not (member? t- x <))
                      (or (ordered? t) (error 'ordered "removing ~a from ~a to get ~a" x t t-))
                      (or (global-invariant? t-) (error 'global "removing ~a from ~a to get ~a" x t t-))
                      (or (local-invariant? t-) (error 'local "removing ~a from ~a to get ~a" x t t-))))))
           (L? (for/fold ([t t])
                 ([x xs])
                 (let ([t- (delete t x <)])
                   (and (not (member? t- x <))
                        (or (ordered? t) (error 'ordered "removing ~a from ~a to get ~a" x t t-))
                        (or (global-invariant? t-) (error 'global "removing ~a from ~a to get ~a" x t t-))
                        (or (local-invariant? t-) (error 'local "removing ~a from ~a to get ~a" x t t-))
                        t-)))))))
  
  
  
  
  #;(for/and ([t ts])
      (test-tree t))
  
  (define-syntax-rule (for/max ((ids es) ...) body ...)
    (for/fold ([m 0])
      ((ids es) ...)
      (max m (begin body ...))))
  
  (define (mean-removal-time t)
    (let ([xs (members t)])
      (let ([ms (string->number
                 (second
                  (regexp-match
                   #px"cpu time: (\\d+) "
                   (with-output-to-string
                    (λ ()
                      (time
                       (for ([i 100])
                         (for ([x xs])
                           (delete t x <)))))))))]
            [n (length xs)])
        (/ (/ (* ms 1000) 100) n))))
  
  #;(for ([i 7])
    (let* ([avg-k (exact->inexact
                 (/ (for/sum ([j 100])
                      (let-values ([(t n) (number-tree (random-tree (+ 2 i)))])
                        (/ (mean-removal-time t) (/ (log n) (log 2)))))
                    100))])
        (printf "~a ~a~n" (+ 2 i) avg-k)))
  
  (for/and ([n 7])
      (let ([k (expt 2 (* (add1 n) 2))])
        (printf "testing trees of height ~a (~a times)..." (add1 n) k)
        (displayln (for/max ([i k])
                            (let-values ([(t n) (number-tree (random-tree (add1 n)))])
                              (test-tree t)
                              n)))
        (printf "done~n")))
  
  #;(for ([i 10])
      (let*-values ([(t n) (number-tree (random-tree (add1 i)))]
                    [(xs) (members t)])
        (displayln n)
        (let ([start (current-milliseconds)])
          (for ([j 200])
            (for ([x xs])
              (delete t x <)))
          (let ([end (current-milliseconds)])
            (displayln (- end start))
            (displayln (log (/ (- end start) (log n))))))))
  
  #;(let/ec escape
      (displayln "deterministic insert")
      (for/and ([i 1000])
        (let ([t (for/fold ([t (L)])
                   ([j i])
                   (insert t j <))])
          (or (invariant? t)
              (escape t))))
      (displayln "passed"))
  
  #;(let/ec escape
      (displayln "nondeterministic insert")
      (for/and ([i 1000])
        (let ([t (for/fold ([t (L)])
                   ([j i])
                   (insert t (random 1000) <))])
          (or (invariant? t)
              (escape t))))
      (displayln "passed"))
  
  #;(let/ec escape
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
      (displayln "passed")))
