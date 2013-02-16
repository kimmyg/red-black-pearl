#lang racket/base
(require racket/contract
         racket/list
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
    [(or (N 'BB (N 'R (N 'R a x b) y c) z d)
         (N 'BB (N 'R a x (N 'R b y c)) z d)
         (N 'BB a x (N 'R (N 'R b y c) z d))
         (N 'BB a x (N 'R b y (N 'R c z d))))
     (N 'B (N 'B a x b) y (N 'B c z d))]
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
  (blacken-if-needed (insert-inner t v cmp)))

(define min
  (match-lambda
    [(L) (error 'min "empty tree")]
    [(N _ (L) x _) x]
    [(N _ a _ _) (min a)]))

(define rotate
  (match-lambda
    [(N 'R (BB) x (N 'B a y b))
     (N 'B (N 'R (L) x a) y b)]
    [(N 'R (N 'BB a x b) y (N 'B c z d))
     (N 'B (N 'R (N 'B a x b) y c) z d)]
    [(N 'R (N 'B a x b) y (BB))
     (N 'B a x (N 'R b y (L)))]
    [(N 'R (N 'B a x b) y (N 'BB c z d))
     (N 'B a x (N 'R b y (N 'B c z d)))]
    
    [(N 'B (BB) x (N 'B (L) y (L))) ;1
     (N 'BB (N 'R (L) x (L)) y (L))]
    [(N 'B (BB) w (N 'B (N 'R (L) x (L)) y (N 'R (L) z (L)))) ;2
     (N 'B (N 'B (L) w (N 'R (L) x (L))) y (N 'B (L) z (L)))]
    [(N 'B (N 'BB a x b) y (N 'B c z d)) ;3
     (N 'BB (N 'R (N 'B a x b) y c) z d)]
    [(N 'B (N 'B (L) x (L)) y (BB)) ;1r
     (N 'BB (L) x (N 'R (L) y (L)))]
    [(N 'B (N 'B (N 'R (L) w (L)) x (N 'R (L) y (L))) z (BB)) ;2r
     (N 'B (N 'B (L) w (L)) x (N 'B (N 'R (L) y (L)) z (L)))]
    [(N 'B (N 'B a x b) y (N 'BB c z d)) ;3r
     (N 'BB a x (N 'R b y (N 'B c z d)))]
    
    [(or (N 'B (N 'B (L) x (N 'R (L) y (L))) z (BB))
         (N 'B (N 'B (N 'R (L) x (L)) y (L)) z (BB)))
     (N 'B (N 'B (L) x (L)) y (N 'B (L) z (L)))]
    [(or (N 'B (BB) x (N 'B (N 'R (L) y (L)) z (L)))
         (N 'B (BB) x (N 'B (L) y (N 'R (L) z (L)))))
     (N 'B (N 'B (L) x (L)) y (N 'B (L) z (L)))]
    
    [(N 'B (N 'R (N 'B a w b) x (N 'B c y d)) z (BB))
     (N 'B (N 'B a w b) x (balance (N 'B c y (N 'R d z (L)))))]
    [(N 'B (N 'R (N 'B a v b) w (N 'B c x d)) y (N 'BB e z f))
     (N 'B (N 'B a v b) w (balance (N 'B c x (N 'R d y (N 'B e z f)))))]
    [(N 'B (BB) w (N 'R (N 'B a x b) y (N 'B c z d)))
     (N 'B (balance (N 'B (N 'R (L) w a) x b)) y (N 'B c z d))]
    [(N 'B (N 'BB a v b) w (N 'R (N 'B c x d) y (N 'B e z f)))
     (N 'B (balance (N 'B (N 'R (N 'B a v b) w c) x d)) y (N 'B e z f))]
    [t t]))

(define blacken-if-needed
  (match-lambda
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
      [(N 'B (N 'R a x b) (== v) (L))
       (N 'B a x b)]
      [(N c a x b)
       (switch-compare
        (cmp v x)
        [< (balance (rotate (N c (delete-inner a v cmp) x b)))]
        [= (let ([v (min b)])
             (balance (rotate (N c a v (delete-inner b v cmp)))))]
        [> (balance (rotate (N c a x (delete-inner b v cmp))))])]))
  (blacken-if-needed (delete-inner (redden-if-possible t) v cmp)))


