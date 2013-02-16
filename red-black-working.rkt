#lang racket/base
(require racket/list
         racket/match)

(struct RB-tree () #:transparent)
(struct L RB-tree () #:transparent)
(struct BB RB-tree () #:transparent)
(struct N RB-tree (color left-child value right-child) #:transparent)


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
    [(or (N 'B (N 'R (N 'R a x b) y c) z d)
         (N 'B (N 'R a x (N 'R b y c)) z d)
         (N 'B a x (N 'R (N 'R b y c) z d))
         (N 'B a x (N 'R b y (N 'R c z d))))
     (N 'R (N 'B a x b) y (N 'B c z d))]
    [t t]))

(define blacken
  (match-lambda
    [(BB) (L)]
    [(N _ l v r)
     (N 'B l v r)]
    [t t]))

(define (insert t v cmp)
  (define (insert-inner t v cmp)
    (match t
      [(L)
       (N 'R (L) v (L))]
      [(N c lc nv rc)
       (switch-compare
        (cmp v nv)
        [< (balance (N c (insert-inner lc v cmp) nv rc))]
        [= t]
        [> (balance (N c lc nv (insert-inner rc v cmp)))])]))
  (blacken (insert-inner t v cmp)))

(define min
  (match-lambda
    [(L) (error 'min "empty tree")]
    [(N _ (L) x _) x]
    [(N _ a _ _) (min a)]))

(define rotate
  (match-lambda
    [(N 'B (L) x (L)) (N 'B (L) x (L))]
    [(N 'B (L) x (N 'R (L) y (L))) (N 'B (L) x (N 'R (L) y (L)))]
    [(N 'B (N 'R (L) x (L)) y (L)) (N 'B (N 'R (L) x (L)) y (L))]
    [(N 'R (N 'B a x b) y (N 'B c z d)) (N 'R (N 'B a x b) y (N 'B c z d))]
    [(N 'B (N 'B a x b) y (N 'R c z d)) (N 'B (N 'B a x b) y (N 'R c z d))]
    [(N 'B (N 'R a x b) y (N 'B c z d)) (N 'B (N 'R a x b) y (N 'B c z d))]
    [(N 'B (N 'R a x b) y (N 'R c z d)) (N 'B (N 'R a x b) y (N 'R c z d))]
    [(N 'B (N 'B a x b) y (N 'B c z d)) (N 'B (N 'B a x b) y (N 'B c z d))]
    [(N 'R (BB) x (N 'B a y b))
     (N 'B (N 'R (L) x a) y b)]
    [(N 'R (N 'B a x b) y (BB))
     (N 'B a x (N 'R b y (L)))]
    [(N 'B (BB) x (N 'R a y b))
     (N 'B (N 'R (L) x a) y b)]
    [(N 'B (N 'R a x b) y (BB))
     (N 'B a x (N 'R b y (L)))]
    [(N 'B (BB) x (N 'B (L) y (L)))
     (N 'BB (L) x (N 'R (L) y (L)))]
    [(N 'B (N 'B (L) x (L)) y (BB))
     (N 'BB (N 'R (L) x (L)) y (L))]
    [(N 'B (N 'B (L) x (N 'R (L) y (L))) z (BB))
     (N 'B (N 'B (L) x (L)) y (N 'B (L) z (L)))]
    [(N 'B (N 'B (N 'R (L) x (L)) y (L)) z (BB))
     (N 'B (N 'B (L) x (L)) y (N 'B (L) z (L)))]
    [(N 'B (BB) x (N 'B (N 'R (L) y (L)) z (L)))
     (N 'B (N 'B (L) x (L)) y (N 'B (L) z (L)))]
    [(N 'B (BB) x (N 'B (L) y (N 'R (L) z (L))))
     (N 'B (N 'B (L) x (L)) y (N 'B (L) z (L)))]
    [(N 'B (BB) w (N 'B (N 'R (L) x (L)) y (N 'R (L) z (L))))
     (N 'B (N 'B (L) w (N 'R (L) x (L))) y (N 'B (L) z (L)))]
    [(N 'B (N 'B (N 'R (L) w (L)) x (N 'R (L) y (L))) z (BB))
     (N 'B (N 'B (L) w (L)) x (N 'B (N 'R (L) y (L)) z (L)))]
    [(N 'R (N 'BB a x b) y (N 'B c z d))
     (N 'B (N 'R (N 'B a x b) y c) z d)]
    [(N 'R (N 'B a x b) y (N 'BB c z d))
     (N 'B a x (N 'R b y (N 'B c z d)))]
    [t (error 'rotate "unhandled tree ~a" t)]))



(define blacken-if-needed
  (match-lambda
    [(BB) (L)]
    [(N 'R (N 'R a x b) y c)
     (N 'B (N 'R a x b) y c)]
    [(N 'R a x (N 'R b y c))
     (N 'B a x (N 'R b y c))]
    [t t]))

(define redden-if-possible
  (match-lambda
    [(N 'B (N 'B a x b) y (N 'B c z d))
     (N 'R (N 'B a x b) y (N 'B c z d))]
    [(N 'B (L) x (L))
     (N 'R (L) x (L))]
    [t t]))

(define (delete t v cmp)
  (define (delete-inner t v cmp)
    (match t
      [(L) (L)]
      [(N 'R (L) (== v) (L))
       (L)]
      [(N 'B (L) (== v) (L))
       (BB)]
      [(N 'B (L) (== v) (N 'R (L) x (L)))
       (N 'B (L) x (L))]
      [(N 'B (N 'R (L) x (L)) (== v) (L))
       (N 'B (L) x (L))]
      [(N c a x b)
       (switch-compare
        (cmp v x)
        [< (balance (rotate (N c (delete-inner a v cmp) x b)))]
        [= (let ([v (min b)])
             (balance (rotate (N c a v (delete-inner b v cmp)))))]
        [> (balance (rotate (N c a x (delete-inner b v cmp))))])]))
  (blacken-if-needed (delete-inner (redden-if-possible t) v cmp)))

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
    [(N c a _ b)
     (let ([a-length (global-invariant? a)]
           [b-length (global-invariant? b)])
       (and a-length
            b-length
            (= a-length b-length)
            (+ a-length (if (eq? c 'B) 1 0))))]))

(define (invariant? t)
  (and (local-invariant? t)
       (global-invariant? t)
       #t))

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

(define (random-numbered-tree h)
  (let-values ([(t n) (number-tree (random-tree h))])
    t))

(define ts
  (list (N 'B (L) 1 (N 'R (L) 2 (L)))
        (N 'B (L) 1 (L))
        (N 'B (N 'R (L) 1 (L)) 2 (N 'R (L) 3 (L)))
        (N 'R (N 'B (L) 1 (L)) 2 (N 'B (L) 3 (N 'R (L) 4 (L))))))

;(random-numbered-tree 2)

#;(for ([t ts])
  (for ([x (members t)])
    (with-handlers ([exn:fail? (λ (e)
                                 (print t)
                                 (newline)
                                 (print x)
                                 (newline)
                                 (raise e))])
      (let ([t- (delete t x <)])
        (and (not (member? t- x <))
             (or (global-invariant? t) (error 'global "removing ~a from ~a to get ~a" x t t-))
             (or (local-invariant? t) (error 'local "removing ~a from ~a to get ~a" x t t-))
             #t)))))

(for ([n 5])
  (for ([i 100])
    (let ([t (random-numbered-tree (add1 n))])
      (for ([x (members t)])
        (with-handlers ([exn:fail? (λ (e)
                                     (print t)
                                     (newline)
                                     (print x)
                                     (newline)
                                     (raise e))])
          (let ([t- (delete t x <)])
            (and (not (member? t- x <))
                 (or (global-invariant? t) (error 'global "removing ~a from ~a to get ~a" x t t-))
                 (or (local-invariant? t) (error 'local "removing ~a from ~a to get ~a" x t t-))
                 #t)))))))