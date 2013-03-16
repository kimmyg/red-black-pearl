#lang racket/base
(require racket/list
         racket/match)

(provide empty-tree
         member?
         members
         min
         delete)

(struct RB-tree (data) #:transparent)
(struct L-tree RB-tree () #:transparent)
(struct L2 RB-tree () #:transparent)
(struct N-tree RB-tree (color left-child value right-child) #:transparent)

(define N-data RB-tree-data)
(define N-color N-tree-color)
(define N-value N-tree-value)
(define L? L-tree?)

(define-syntax-rule (define-match id cases ...)
  (define id
    (match-lambda
      cases ...)))

(define-match-expander N
  (syntax-rules ()
    [(_ c a x b) (N-tree _ c a x b)]
    [(_ d c a x b) (N-tree d c a x b)])
  (syntax-rules ()
    [(_ c a x b)   (N-tree #f c a x b)]
    [(_ d c a x b) (N-tree d c a x b)]))

(define-match-expander L
  (syntax-rules ()
    [(_) (L-tree _)]
    [(_ d) (L-tree d)])
  (syntax-rules ()
    [(_) (L-tree #f)]
    [(L d) (L-tree d)]))

(define-match-expander B
  (syntax-rules ()
    [(_)       (L)]
    [(_ a x b) (N 'B a x b)])
  (syntax-rules ()
    [(_)       (L)]
    [(_ a x b) (N 'B a x b)]))

(define-match-expander B?
  (syntax-rules ()
    [(_ a) (and (or (B)
                    (B _ _ _))
                a)])
  (syntax-rules ()
    [(_ a) (match a
             [(B? _) #t]
             [_      #f])]))

(define-match-expander R
  (syntax-rules ()
    [(_ a x b) (N 'R a x b)])
  (syntax-rules ()
    [(_ a x b) (N 'R a x b)]))

(define-match-expander R?
  (syntax-rules ()
    [(_ a) (and (R _ _ _) a)])
  (syntax-rules ()
    [(_ a) (match a
             [(R? _) #t]
             [_      #f])]))

(define-match-expander BB
  (syntax-rules ()
    [(_)       (L2 _)]
    [(_ a x b) (N 'BB a x b)])
  (syntax-rules ()
    [(_) (L2 #f)]
    [(_ a x b) (N 'BB a x b)]))

(define-match-expander BB?
  (syntax-rules ()
    [(_ a) (and (or (BB)
                    (BB _ _ _))
                a)])
  (syntax-rules ()
    [(_ a) (match a
             [(BB? _) #t]
             [_       #f])]))

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

(define-match members
  [(L)
   empty]
  [(N _ a x b)
   (append (members a) (list x) (members b))])

(define-match balance
  [(or (B (R (R a x b) y c) z d)
       (B (R a x (R b y c)) z d)
       (B a x (R (R b y c) z d))
       (B a x (R b y (R c z d))))
   (R (B a x b) y (B c z d))]
  [(or (BB (R a x (R b y c)) z d)
       (BB a x (R (R b y c) z d)))
   (B (B a x b) y (B c z d))]
  [t t])

(define (insert t v cmp)
  (define (ins t v cmp)
    (match t
      [(L)
       (R (L) v (L))]
      [(N c a x b)
       (switch-compare
        (cmp v x)
        [< (balance (N c (ins a v cmp) x b))]
        [= t]
        [> (balance (N c a x (ins b v cmp)))])]))
  (blacken (ins t v cmp)))

(define-match min
  [(L) (error 'min "empty tree")]
  [(N _ (L) x _) x]
  [(N _ a _ _) (min a)])

(define-match -B
  [(BB) (L)]
  [(BB a x b) (B a x b)]
  [a (error '-B "unsupported node ~a" a)])

(define-match rotate
  [(R (BB? a-x-b) y (B c z d))
   (balance (B (R (-B a-x-b) y c) z d))]
  [(R (B a x b) y (BB? c-z-d))
   (balance (B a x (R b y (-B c-z-d))))]
  
  [(B (BB? a-x-b) y (B c z d))
   (balance (BB (R (-B a-x-b) y c) z d))]
  [(B (B a x b) y (BB? c-z-d))
   (balance (BB a x (R b y (-B c-z-d))))]
  
  [(B (BB? a-w-b) x (R (B c y d) z e))
   (B (balance (B (R (-B a-w-b) x c) y d)) z e)]
  [(B (R a w (B b x c)) y (BB? d-z-e))
   (B a w (balance (B b x (R c y (-B d-z-e)))))]
  
  [t t])

(define-match blacken
  [(or (R (R? a) x b)
       (R a x (R? b)))
   (B a x b)]
  [t t])

(define-match redden
  [(B (B? a) x (B? b))
   (R a x b)]
  [t t])

(define (delete t v cmp)
  (define (del t v cmp)
    (match t
      [(L) (L)]
      [(R (L) (== v) (L))
       (L)]
      [(B (L) (== v) (L))
       (BB)]
      [(B (R a x b) (== v) (L))
       (B a x b)]
      [(N c a x b)
       (switch-compare
        (cmp v x)
        [< (rotate (N c (del a v cmp) x b))]
        [= (let ([v (min b)])
             (rotate (N c a v (del b v cmp))))]
        [> (rotate (N c a x (del b v cmp)))])]))
  (del (redden t) v cmp))

(module+ benchmark
  (require racket/set)
  
  (define-match min-del
    [(L) (error 'min-del "empty tree")]
    [(R (L) x (L)) (values x (L))]
    [(B (L) x (L)) (values x (BB))]
    [(B (L) x (R a y b)) (values x (B a y b))]
    [(N c a x b) (let-values ([(v a) (min-del a)])
                   (values v (rotate (N c a x b))))])
  
  (define (min/delete t)
    (min-del (redden t)))
  
  (define (delete-alt t v cmp)
    (define (del t v cmp)
      (match t
        [(L) (L)]
        [(R (L) (== v) (L))
         (L)]
        [(B (L) (== v) (L))
         (BB)]
        [(B (R a x b) (== v) (L))
         (B a x b)]
        [(N c a x b)
         (switch-compare
          (cmp v x)
          [< (rotate (N c (del a v cmp) x b))]
          [= (let-values ([(v b) (min-del b)])
               (rotate (N c a v b)))]
          [> (rotate (N c a x (del b v cmp)))])]))
    (del (redden t) v cmp))
  
  (define root-value
    (match-lambda
      [(L) (error 'root-value "empty tree")]
      [(N _ _ x _) x]))
  
  (define-syntax-rule (time body ...)
    (begin
      (collect-garbage)
      (let ([start (current-milliseconds)]
            [dummy (begin body ...)]
            [end (current-milliseconds)])
        (- end start))))
  
  (define (insert* t cmp vs)
    (for/fold ([t t])
      ([v vs])
      (insert t v cmp)))
  
  (define (random-list n k)
    (if (zero? n)
        empty
        (cons (random k) (random-list (sub1 n) k))))
  
  (displayln "comparing two implementations of delete")
  
  (displayln "aggregate deletion time")
  (for ([i 20])
    (let* ([n (expt 2 (add1 i))]
           [xs (random-list n n)]
           [t (insert* empty-tree < xs)])
      (let ([imp1-time (time
                        (for ([x xs])
                          (delete t x <)))]
            [imp2-time (time
                        (for ([x xs])
                          (delete-alt t x <)))])
        (printf "size ~a, standard ~ams, alternate ~ams~n" n imp1-time imp2-time))))
  
  (displayln "deletion time without replacement")
  (for ([i 20])
    (let* ([n (expt 2 (add1 i))]
           [xs (random-list n n)]
           [t (insert* empty-tree < xs)])
      (let ([imp1-time (time
                        (for/fold ([t t])
                          ([x xs])
                          (delete t x <)))]
            [imp2-time (time
                        (for/fold ([t t])
                          ([x xs])
                          (delete-alt t x <)))])
        (printf "size ~a, standard ~ams, alternate ~ams~n" n imp1-time imp2-time))))
  
  (displayln "root deletion time")
  (for ([i 20])
    (let* ([n (expt 2 (add1 i))]
           [xs (random-list n n)]
           [t (insert* empty-tree < xs)]
           [x (root-value t)])
      (let ([imp1-time (time
                        (for ([j n])
                          (delete t x <)))]
            [imp2-time (time
                        (for ([j n])
                          (delete-alt t x <)))])
        (printf "size ~a, standard ~ams, alternate ~ams~n" n imp1-time imp2-time))))
  
  (displayln "comparison against persistent sets")
  
  (displayln "insertion")
  (for ([i 20])
    (let* ([n (expt 2 (add1 i))]
           [xs (random-list n n)])
      (let ([set-time (time
                       (for/fold ([s (set)])
                         ([x xs])
                         (set-add s x)))]
            [rbt-time (time
                       (for/fold ([t empty-tree])
                         ([x xs])
                         (insert t x <)))])
        (printf "size ~a, set ~ams, tree ~ams~n" n set-time rbt-time))))
  
  (displayln "deletion with replacement")
  (for ([i 20])
    (let* ([n (expt 2 (add1 i))]
           [xs (random-list n n)]
           [s (apply set xs)]
           [t (insert* empty-tree < xs)])
      (let ([set-time (time
                       (for ([x xs])
                         (set-remove s x)))]
            [rbt-time (time
                       (for ([x xs])
                         (delete-alt t x <)))])
        (printf "size ~a, set ~ams, tree ~ams~n" n set-time rbt-time))))
  
  (displayln "deletion without replacement")
  (for ([i 20])
    (let* ([n (expt 2 (add1 i))]
           [xs (random-list n n)]
           [s (apply set xs)]
           [t (insert* empty-tree < xs)])
      (let ([set-time (time
                       (for/fold ([s s])
                         ([x xs])
                         (set-remove s x)))]
            [rbt-time (time
                       (for/fold ([t t])
                         ([x xs])
                         (delete-alt t x <)))])
        (printf "size ~a, set ~ams, tree ~ams~n" n set-time rbt-time))))
  
  (define (mean-removal-time t)
    (define k 100)
    (let ([xs (members t)])
      (let ([ms (time
                 (for ([i k])
                   (for ([x xs])
                     (delete t x <))))]
            [n (length xs)])
        (/ ms (* n k)))))
  
  #;(for ([i 7])
      (let ([avg-k (exact->inexact
                    (/ (for/sum ([j 100])
                         (let-values ([(t n) (number-tree (random-tree (+ 2 i)))])
                           (/ (mean-removal-time t) (/ (log n) (log 2)))))
                       100))])
        (printf "~a ~a~n" (+ 2 i) avg-k)))
  )

(module+ test
  (require racket/port
           racket/set)
  
  (define-match local-invariant?
    [(L) #t]
    [(R a _ b)
     (and (B? a)
          (B? b)
          (local-invariant? a)
          (local-invariant? b))]
    [(B a _ b)
     (and (local-invariant? a)
          (local-invariant? b))])
  
  (define-match global-invariant?
    [(L) 1]
    [(N c a _ b)
     (let ([a-length (global-invariant? a)]
           [b-length (global-invariant? b)])
       (and a-length
            b-length
            (= a-length b-length)
            (+ a-length (if (eq? c 'B) 1 0))))]
    [_ #f])
  
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
  
  (define (number-tree t [n 0])
    (match t
      [(L)
       (values t n)]
      [(N c l _ r)
       (let*-values ([(l n) (number-tree l n)]
                     [(v) n]
                     [(r n) (number-tree r (add1 n))])
         (values (N c l v r) n))]))
  
  
  
  (define (test-tree t)
    (let ([xs (members t)])
      (and (for/and ([x xs])
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
                          (or (local-invariant? t-) (error 'local "removing ~a from ~a to get ~a" x t t-))
                          t-))))))))
  
  (define-syntax-rule (for/max ((ids es) ...) body ...)
    (for/fold ([m 0])
      ((ids es) ...)
      (max m (begin body ...))))
  
  (for/and ([n 7])
    (let ([k (expt 2 (* (add1 n) 2))])
      (printf "testing ~a random trees of height ~a...~n" k (add1 n))
      (printf "all passed (max size was ~a)~n"
              (for/max ([i k])
                       (let-values ([(t n) (number-tree (random-tree (add1 n)))])
                         (test-tree t)
                         n)))))
  
  #;(for ([i 10])
      (let*-values ([(t n) (number-tree (random-tree (add1 i)))]
                    [(xs) (members t)])
        (let ([ms (time
                   (for ([j 200])
                     (for ([x xs])
                       (delete t x <))))])
          (displayln (log (/ ms (log n)))))))
  
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
      (displayln "passed"))
  )

(module+ diagram
  (require racket/class
           racket/draw
           racket/set)
  
  (struct renderable () #:transparent)
  (struct tree renderable (tree) #:transparent)
  (struct hc-append renderable (gap renderables) #:transparent)
  (struct vc-append renderable (gap renderables) #:transparent)
  (struct right-arrow renderable (body-length body-half-width head-length head-extent) #:transparent)
  (struct down-arrow renderable (body-length body-half-width head-length head-extent) #:transparent)
  
  (define width
    (match-lambda
      [(tree t)
       (width-tree t)]
      [(hc-append gap rs)
       (+ (apply + (map width rs))
          (* gap (sub1 (length rs))))]
      [(vc-append gap rs)
       (apply max (map width rs))]
      [(right-arrow bl _ hl _)
       (+ bl hl)]
      [(down-arrow _ bw _ he)
       (* (+ he bw) 2)]))
  
  (define height
    (match-lambda
      [(tree t)
       (height-tree t)]
      [(hc-append _ rs)
       (apply max (map height rs))]
      [(vc-append gap rs)
       (+ (apply + (map height rs))
          (* gap (sub1 (length rs))))]
      [(right-arrow _ bhw _ e)
       (* 2 (+ bhw e))]
      [(down-arrow bl _ hl _)
       (+ bl hl)]))
  
  
  (define fixed-render? (make-parameter #f))
  
  (define outline-color "black")
  (define outline-width 2)
  
  
  (define (render r name)
    (define inset 8)
    (define (render-inner r ctx)
      (match r
        [(tree t)
         (render-tree t ctx)]
        [(hc-append gap rs)
         (let ([h (height r)])
           (letrec ([go (λ (rs acc)
                          (if (empty? rs)
                              (send ctx translate (- acc) 0)
                              (let ([r (first rs)]
                                    [rs (rest rs)])
                                (let ([y-offset (/ (- h (height r)) 2)]
                                      [x-offset (+ (width r) gap)])
                                  (send ctx translate 0 y-offset)
                                  (render-inner r ctx)
                                  (send ctx translate 0 (- y-offset))
                                  (send ctx translate x-offset 0)
                                  (go rs (+ acc x-offset))))))])
             (go rs 0)))]
        [(vc-append gap rs)
         (let ([w (width r)])
           (letrec ([go (λ (rs acc)
                          (if (empty? rs)
                              (send ctx translate 0 (- acc))
                              (let ([r (first rs)]
                                    [rs (rest rs)])
                                (let ([x-offset (/ (- w (width r)) 2)]
                                      [y-offset (+ (height r) gap)])
                                  (send ctx translate x-offset 0)
                                  (render-inner r ctx)
                                  (send ctx translate (- x-offset) 0)
                                  (send ctx translate 0 y-offset)
                                  (go rs (+ acc y-offset))))))])
             (go rs 0)))]
        [(right-arrow bl bhw hl he)
         (let ([outline (new dc-path%)])
           (send outline move-to 0 (+ he bhw))
           (send outline line-to 0 he)
           (send outline line-to bl he)
           (send outline line-to bl 0)
           (send outline line-to (+ bl hl) (+ he bhw))
           (send outline line-to bl (* 2 (+ he bhw)))
           (send outline line-to bl (+ he (* 2 bhw)))
           (send outline line-to 0 (+ he (* 2 bhw)))
           (send outline line-to 0 (+ he bhw))
           (send outline close)
           (send ctx set-pen "black" 0 'transparent)
           (send ctx set-brush "black" 'solid)
           (send ctx draw-path outline))]
        [(down-arrow bl bhw hl he)
         (let ([outline (new dc-path%)])
           (send outline move-to (+ he bhw) 0)
           (send outline line-to he 0)
           (send outline line-to he bl)
           (send outline line-to 0 bl)
           (send outline line-to (+ he bhw) (+ bl hl))
           (send outline line-to (* 2 (+ he bhw)) bl)
           (send outline line-to (+ he (* 2 bhw)) bl)
           (send outline line-to (+ he (* 2 bhw)) 0)
           (send outline line-to (+ he bhw) 0)
           (send outline close)
           (send ctx set-pen "black" 0 'transparent)
           (send ctx set-brush "black" 'solid)
           (send ctx draw-path outline))]))
    (let ([ctx (new pdf-dc%
                    [interactive #f]
                    [width (floor (* 0.8 (+ inset (width r) inset)))]
                    [height (floor (* 0.8 (+ inset (height r) inset)))]
                    [output (format "~a.pdf" name)])])
      (send ctx start-doc (symbol->string (gensym 'doc)))
      (send ctx start-page)
      (send ctx set-text-mode 'transparent)
      (send ctx translate inset inset)
      (render-inner r ctx)
      (send ctx end-page)
      (send ctx end-doc)))
  
  (define unit 32)
  (define unit/2 (/ unit 2))
  (define unit/4 (/ unit 4))
  (define unit/8 (/ unit 8))
  
  (define longer (make-parameter #f))
  
  (define dx
    (match-lambda
      [(or (L) (BB))
       (* 3/8 unit)]
      [(label _)
       (* 3/8 unit)]
      [(N _ _ _ _)
       (if (longer)
           (* 7/8 unit)
           (* 5/8 unit))]))
  
  (define dy
    (match-lambda
      [(or (L) (BB))
       (* 3/4 unit)]
      [(label _)
       (* 3/4 unit)]
      [(N _ _ _ _)
       (if (longer)
           (* 7/4 unit)
           (* 5/4 unit))]))
  
  (define label-h/2 unit/8)
  (define leaf-h/2 unit/8)
  (define label-height unit/4)
  
  (define leaf-width 8)
  (define leaf-height 8)
  (define node-width 32)
  (define node-height 32)
  
  (define (render-tree t ctx)
    (define (node-pen n)
      (new pen%
           [color outline-color]
           [width outline-width]
           [style (if (N-color n)
                      (if (and (N-data n)
                               (set-member? (N-data n) 'emphasize))
                          'short-dash
                          'solid)
                      'transparent)]))
    (define (node-brush n)
      (new brush%
           [color (match n
                    [(B? _)  "black"]
                    [(R? _)  "red"]
                    [(BB? _) "white"]
                    [(N #f _ _ _) "white"])]
           [style 'solid]))
    (define text-color
      (match-lambda
        [(B? _)  "white"]
        [(R? _)  "white"]
        [(BB? _) "black"]
        [(N #f _ _ _) "black"]))
    (define (render-node n ctx)
      (let ([pen (node-pen n)]
            [brush (node-brush n)]
            [text-color (text-color n)]
            [text (format "~a" (N-value n))])
        (send ctx set-pen pen)
        (send ctx set-brush brush)
        (send ctx draw-ellipse (- (/ node-width 2)) (- (/ node-height 2)) node-width node-height)
        (let-values ([(width height descender-height extra) (send ctx get-text-extent text)])
          (send ctx set-text-foreground text-color)
          (send ctx draw-text text (- (/ width 2)) (- (- (/ (- height descender-height) 2)) 2)))))
    (define (render-leaf l ctx)
      (let ([brush (node-brush l)])
        (send ctx set-pen outline-color outline-width 'solid)
        (send ctx set-brush brush)
        (send ctx draw-ellipse (- (/ leaf-width 2)) (- (/ leaf-height 2)) leaf-width leaf-height)))
    (define (render-label l ctx)
      (send ctx set-pen "white" 0 'transparent)
      (send ctx set-brush "white" 'solid)
      (send ctx draw-ellipse (- (/ leaf-width 2)) (- (/ leaf-height 2)) leaf-width leaf-height)
      (let-values ([(width height descender-height extra) (send ctx get-text-extent l)])
        (send ctx set-text-foreground "black")
        (send ctx draw-text l (- (/ width 2)) (- (/ (- height descender-height) 2)))))
    (define (render-tree-inner t ctx)
      (match t
        [(or (L) (BB))
         (render-leaf t ctx)]
        [(label l)
         (render-label l ctx)]
        [(N d _ a x b)
         (when a
           (parameterize ([longer (or (and d (set-member? d 'longer)) (longer))])
             (let ([dx (if (fixed-render?)
                           (dx a)
                           (+ (width-tree-right a) unit/8))]
                   [dy (dy a)])
               (send ctx set-pen outline-color outline-width 'solid)
               (send ctx draw-line 0 0 (- dx) dy)
               (send ctx translate (- dx) dy)
               (render-tree-inner a ctx)
               (send ctx translate dx (- dy)))))
         (when b
           (parameterize ([longer (or (and d (set-member? d 'longer)) (longer))])
             (let ([dx (if (fixed-render?)
                           (dx b)
                           (+ unit/8 (width-tree-left b)))]
                   [dy (dy b)])
               (send ctx set-pen outline-color outline-width 'solid)
               (send ctx draw-line 0 0 dx dy)
               (send ctx translate dx dy)
               (render-tree-inner b ctx)
               (send ctx translate (- dx) (- dy)))))
         (render-node t ctx)]))
    (let ([x-offset (width-tree-left t)]
          [y-offset (height-tree-top t)])
      (send ctx translate x-offset y-offset)
      (render-tree-inner t ctx)
      (send ctx translate (- x-offset) (- y-offset))))
  
  (define-match-expander label
    (syntax-rules ()
      [(_ l) (? string? l)]))
  
  (define width-tree-left
    (match-lambda
      [(or (L) (BB))
       (/ leaf-width 2)]
      [(label _)
       (/ leaf-width 2)]
      [(N _ _ a _ _)
       (max (/ node-width 2)
            (or (and a (if (fixed-render?)
                           (+ (width-tree-left a) (dx a))
                           (+ (width-tree a) unit/8))) 0))]))
  
  (define width-tree-right
    (match-lambda
      [(or (L) (BB))
       (/ leaf-width 2)]
      [(label _)
       (/ leaf-width 2)]
      [(N _ _ _ _ b)
       (max (/ node-width 2)
            (or (and b (if (fixed-render?)
                           (+ (dx b) (width-tree-right b))
                           (+ (width-tree b) unit/8))) 0))]))
  
  (define (width-tree t)
    (+ (width-tree-left t)
       (width-tree-right t)))
  
  (define height-tree-top
    (match-lambda
      [(or (L) (BB))
       (/ leaf-height 2)]
      [(label _)
       (/ leaf-height 2)]
      [(N _ _ _ _)
       (/ node-height 2)]))
  
  (define height-tree-bottom
    (match-lambda
      [(or (L) (BB))
       (/ leaf-height 2)]
      [(label _)
       (/ leaf-height 2)]
      [(N _ a _ b)
       (max (or (and a (+ (dy a) (height-tree-bottom a))) 0)
            (/ node-height 2)
            (or (and b (+ (dy b) (height-tree-bottom b))) 0))]))
  
  (define (height-tree t)
    (+ (height-tree-top t)
       (height-tree-bottom t)))
  
  (define right-> (right-arrow 32 2 16 3))
  (define down-> (down-arrow 12 6 12 6))
  
  (parameterize ([fixed-render? #t])
    #;(render (hc-append 16 (list (tree (B (R (R "a" "x" "b") "y" "c") "z" "d"))
                                  (tree (B (R "a" "x" (R "b" "y" "c")) "z" "d"))
                                  (tree (B "a" "x" (R (R "b" "y" "c") "z" "d")))
                                  (tree (B "a" "x" (R "b" "y" (R "c" "z" "d"))))))
              "four-cases")
    
    #;(render (tree (R (B "a" "x" "b") "y" (B "c" "z" "d")))
              "four-cases-resolved")
    
    (render (vc-append 16 (list (hc-append 16 (list (tree (B (R (R "a" "x" "b") "y" "c") "z" "d"))
                                                    (tree (B (R "a" "x" (R "b" "y" "c")) "z" "d"))
                                                    (tree (B "a" "x" (R (R "b" "y" "c") "z" "d")))
                                                    (tree (B "a" "x" (R "b" "y" (R "c" "z" "d"))))))
                                down->
                                (tree (R (B "a" "x" "b") "y" (B "c" "z" "d")))))
            "balance")
    
    (render (tree (B (L) "x" (R "a" "y" "b")))
            "black-red-right-subtree-unbounded")
    
    (render (tree (B (L) "x" (R (L) "y" (L))))
            "black-red-right-subtree-bounded")
    
    (render (tree (R (L) "x" (B "a" "y" "b")))
            "red-black-right-subtree")
    
    (render (hc-append 16 (list (tree (L))
                                right->
                                (tree (L))))
            "empty-step")
    
    (render (hc-append 16 (list (tree (R (L) "v" (L)))
                                right->
                                (tree (L))))
            "single-red-step")
    
    (render (tree (R (B "a" "x" "b") "v" (L)))
            "red-black-left-subtree")
    
    (render (hc-append 16 (list (tree (B (R "a" "x" "b") "v" (L)))
                                right->
                                (tree (B "a" "x" "b"))))
            "black-red-left-subtree-step")
    
    (render (tree (B (L) "v" (L)))
            "single-black")
    
    (render (tree (BB "a" "x" "b"))
            "double-black-tree")
    
    (render (tree (BB))
            "double-black-leaf")
    
    (render (hc-append 16 (list (tree (B (L) "v" (L)))
                                right->
                                (tree (BB))))
            "single-black-step")
    
    (render (hc-append 16 (list (tree (R (BB "a" "x" "b") "y" (B "c" "z" "d")))
                                right->
                                (tree (B (R (B "a" "x" "b") "y" "c") "z" "d"))))
            "BB-R-B")
    
    (render (hc-append 16 (list (tree (B (BB "a" "x" "b") "y" (B "c" "z" "d")))
                                right->
                                (tree (BB (R (B "a" "x" "b") "y" "c") "z" "d"))))
            "BB-B-B")
    
    (render (tree (B (BB "a" "x" "b") "y" (R "c" "z" "d")))
            "BB-B-R")
    
    (render (hc-append 16 (list (tree (B (BB "a" "w" "b") "x" (N (seteq 'longer) 'R (B "c" "y" "d") "z" "e")))
                                right->
                                (tree (B (B (R (B "a" "w" "b") "x" "c") "y" "d") "z" "e"))))
            "BB-B-R-B")
    
    (render (hc-append 16 (list (tree (BB (R "a" "x" (R "b" "y" "c")) "z" "d"))
                                (tree (BB "a" "x" (R (R "b" "y" "c") "z" "d")))))
            "two-cases-extended")
    
    (render (tree (B (B "a" "x" "b") "y" (B "c" "z" "d")))
            "two-cases-extended-resolved")
    
    (render (tree (BB (L) "v" (BB (L) "x" (BB (L) "y" "..."))))
            "right-cascade"))
  
  (render (tree (N #f (R (BB "a" "x" "b") "y" (B "c" "z" "d")) "..." #f))
          "test-tree")
  
  (define (number-tree t)
    (define (number-tree-inner t n)
      (match t
        [(L)
         (values t n)]
        [(N c l _ r)
         (let*-values ([(l n) (number-tree-inner l n)]
                       [(v) n]
                       [(r n) (number-tree-inner r (add1 n))])
           (values (N c l v r) n))]))
    (let-values ([(t n) (number-tree-inner t 1)])
      t))
  
  (define (random-tree h)
    (define (random-tree-inner h [red-ok? #t])
      (if (and red-ok? (zero? (random 6)))
          (N 'R
             (random-tree-inner h #f)
             #f
             (random-tree-inner h #f))
          (if (= h 1)
              (L)
              (N 'B
                 (random-tree-inner (sub1 h) #t)
                 #f
                 (random-tree-inner (sub1 h) #t)))))    
    (number-tree (random-tree-inner h)))
  
  (struct tree-context () #:transparent)
  (struct E-context () #:transparent)
  (struct L-context tree-context (color value sibling context) #:transparent)
  (struct R-context tree-context (color value sibling context) #:transparent)
  
  (define (compose e t)
    (match e
      [(E-context) t]
      [(L-context c v s e)
       (compose e (N c t v s))]
      [(R-context c v s e)
       (compose e (N c s v t))]))
  
  (define context (make-parameter #f))  
  
  (define emphasize
    (match-lambda
      [(L d) (L (set-add (or d (seteq)) 'emphasize))]
      [(BB) (L2 #t)]
      [(N d c a x b) (N (set-add (or d (seteq)) 'emphasize) c a x b)]))
  
  (define prefix (make-parameter ""))
  
  
  
  (define (delete t v cmp)
    (define counter 0)
    (define (step t)
      (render (tree (compose (context) (emphasize t)))
              (format "~a-~a" (prefix) counter))
      (set! counter (add1 counter))
      t)
    (define redden
      (match-lambda
        [(B (B? a) x (B? b))
         (step (R a x b))]
        [t t]))
    (define-match balance
      [(or (B (R (R a x b) y c) z d)
           (B (R a x (R b y c)) z d)
           (B a x (R (R b y c) z d))
           (B a x (R b y (R c z d))))
       (step (R (B a x b) y (B c z d)))]
      [(or (BB (R a x (R b y c)) z d)
           (BB a x (R (R b y c) z d)))
       (step (B (B a x b) y (B c z d)))]
      [t t])
    
    (define-match rotate
      [(R (BB? a-x-b) y (B c z d))
       (balance (step (B (R (-B a-x-b) y c) z d)))]
      [(R (B a x b) y (BB? c-z-d))
       (balance (step (B a x (R b y (-B c-z-d)))))]
      
      [(B (BB? a-x-b) y (B c z d))
       (balance (step (BB (R (-B a-x-b) y c) z d)))]
      [(B (B a x b) y (BB? c-z-d))
       (balance (step (BB a x (R b y (-B c-z-d)))))]
      
      [(B (BB? a-w-b) x (R (B c y d) z e))
       (parameterize ([context (L-context 'B z e (context))])
         (B (balance (step (B (R (-B a-w-b) x c) y d))) z e))]
      [(B (R a w (B b x c)) y (BB? d-z-e))
       (parameterize ([context (R-context 'B w a (context))])
         (B a w (balance (step (B b x (R c y (-B d-z-e)))))))]
      
      [t t])
    (define (del t v cmp)
      (match t
        [(L) (L)]
        [(R (L) (== v) (L))
         (step (L))]
        [(B (L) (== v) (L))
         (step (BB))]
        [(B (R a x b) (== v) (L))
         (step (B a x b))]
        [(N c a x b)
         (step (N c a x b))
         (switch-compare
          (cmp v x)
          [< (let* ([t (parameterize ([context (L-context c x b (context))])
                         (N c (del a v cmp) x b))])
               (rotate (step t)))]
          [= (let* ([v (min b)]
                    [t (parameterize ([context (R-context c v a (context))])
                         (N c a v (del b v cmp)))])
               (rotate (step t)))]
          [> (let* ([t (parameterize ([context (R-context c x a (context))])
                         (N c a x (del b v cmp)))])
               (rotate (step t)))])]))
    (parameterize ([context (E-context)])
      (del (redden (step t)) v cmp)))
  
  
  (delete (number-tree (let* ([l1 (L)]
                              [l2 (B l1 #f l1)]
                              [l3 (B l2 #f l2)]
                              [l4 (B l3 #f l3)])
                         (B l4 #f (R l4 #f l4))))
          4
          <)
  
  #;(for ([i 100])
    (parameterize ([prefix (number->string i)])
      (let* ([t (random-tree 4)])
        (delete t (N-value t) <))))
  
  #;(for ([i 50])
      (render (tree (random-tree (add1 (floor (/ (log (add1 i)) (log 2))))))
              (number->string i))))