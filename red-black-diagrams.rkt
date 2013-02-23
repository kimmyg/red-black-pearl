#lang racket
(require racket/draw)

(struct renderable () #:transparent)
(struct tree renderable (tree) #:transparent)
(struct hc-append renderable (renderables) #:transparent)

(define width
  (match-lambda
    [(tree t)
     (width-tree t)]
    [(hc-append rs)
     (apply + (map width rs))]))

(define height
  (match-lambda
    [(tree t)
     (height-tree t)]
    [(hc-append es)
     (apply max (map height es))]))

(define (render r name)
  (define inset 8)
  (define (render-inner r ctx)
    (match r
      [(tree t)
       (render-tree t ctx)]
      [(hc-append rs)
       (letrec ([go (λ (rs acc)
                      (if (empty? rs)
                          (send ctx translate (- acc) 0)
                          (let ([r (first rs)]
                                [rs (rest rs)])
                            (render-inner r ctx)
                            (let ([width (width r)])
                              (send ctx translate width 0)
                              (go rs (+ acc width))))))])
         (go rs 0))]))
  (let ([ctx (new pdf-dc%
                  [interactive #f]
                  [width (+ inset (width r) inset)]
                  [height (+ inset (height t) inset)]
                  [output (format "~a.pdf" name)])])
    (send ctx start-doc (symbol->string (gensym 'doc)))
    (send ctx start-page)
    (send ctx set-text-mode 'transparent)
    (send ctx translate (+ inset (tree-left-width t)) (+ inset (n-e/2 t)))
    (draw-tree t ctx)
    (send ctx end-page)
    (send ctx end-doc)))

(define unit 32)
(define unit/2 (/ unit 2))
(define unit/4 (/ unit 4))
(define unit/8 (/ unit 8))

(define outline-width 2)

(define dx
  (match-lambda
    [`(label ,x) (+ unit/4 unit/8)]
    ['(L)        (+ unit/4 unit/8)]
    [_           (+ unit/2 unit/4)]))

(define dy
  (match-lambda
    [`(label ,x) (+ unit/2 unit/4)]
    ['(L)        (+ unit/2 unit/4)]
    [_           (+ unit unit/2)]))

(define label-h/2 unit/8)
(define leaf-h/2 unit/8)
(define label-height unit/4)

(define n-e/2
  (match-lambda
    [`(label ,x) unit/8]
    ['(L)        unit/8]
    [`(,c ,a ,x ,b) unit/2]))


(define tree-height
  (match-lambda
    [`(label ,x)    unit/4]
    ['(L)           unit/4]
    [`(,c ,a ,x ,b) (+ unit/2 (max (+ (dy a) (- (tree-height a) (n-e/2 a)))
                                   (+ (dy b) (- (tree-height b) (n-e/2 b)))))]))

(define tree-left-width
  (match-lambda
    [(and `(,c ,a ,x ,b) t)
     (max (n-e/2 t)
          (+ (tree-left-width a) (dx a)))]
    [t
     (n-e/2 t)]))

(define tree-right-width
  (match-lambda
    [(and `(,c ,a ,x ,b) t)
     (max (n-e/2 t)
          (+ (dx b) (tree-right-width b)))]
    [t
     (n-e/2 t)]))

(define (tree-width t)
  (+ (tree-left-width t)
     (tree-right-width t)))

(define fill-color
  (match-lambda
    ['B  "black"]
    ['R  "red"]
    ['BB "white"]))

(define label-color
  (match-lambda
    ['B  "white"]
    ['R  "white"]
    ['BB "black"]))

(define (draw-node color label ctx)
  (let ([fill-color (fill-color color)]
        [label-color (label-color color)])
    (send ctx set-brush fill-color 'solid)
    (send ctx draw-ellipse (- unit/2) (- unit/2) unit unit)
    (let-values ([(width height descender-height extra) (send ctx get-text-extent label)])
      (send ctx set-text-foreground label-color)
      (send ctx draw-text label (- (/ width 2)) (- (- (/ (- height descender-height) 2)) 2)))))

(define (draw-leaf color ctx)
  (let-values ([fill-color (fill-color color)])
    (send ctx set-pen "black" outline-width 'solid)
    (send ctx set-brush fill-color 'solid)
    (send ctx draw-ellipse (- unit/8) (- unit/8) unit/4 unit/4)))

(define (render-tree t ctx)
  (define (render-tree-inner t ctx)
    (match t
    [`(label ,l)
     (let ([pen (send ctx get-pen)]
           [brush (send ctx get-brush)])
       (send ctx set-pen "white" 1 'solid)
       (send ctx set-brush "white" 'solid)
       (send ctx draw-ellipse (- (/ label-height 2)) (- (/ label-height 2)) label-height label-height)
       (let ([text (format "~a" l)])
         (let-values ([(width height descender-height extra) (send ctx get-text-extent text)])
           (send ctx set-text-foreground "black")
           (send ctx draw-text text (- (/ width 2)) (- (/ (- height descender-height) 2)))))
       (send ctx set-pen pen)
       (send ctx set-brush brush))]
    ['(L)
     (draw-leaf 'B ctx)]
    ['(BB)
     (draw-leaf 'BB ctx)]
    [`(B ,a ,x ,b)
     (send ctx set-pen "black" outline-width 'solid)
     
     (let ([dx (dx a)]
           [dy (dy a)])
       (send ctx draw-line 0 0 (- dx) dy)
       
       (send ctx translate (- dx) dy)
       (draw-tree a ctx)
       (send ctx translate dx (- dy)))
     
     (let ([dx (dx b)]
           [dy (dy b)])
       (send ctx draw-line 0 0 dx dy)
       
       (send ctx translate dx dy)
       (draw-tree b ctx)
       (send ctx translate (- dx) (- dy)))
     
     (draw-node 'B (format "~a" x) ctx)]
    [`(R ,a ,x ,b)
     (send ctx set-pen "black" outline-width 'solid)
     
     (let ([dx (dx a)]
           [dy (dy a)])
       (send ctx draw-line 0 0 (- dx) dy)
       
       (send ctx translate (- dx) dy)
       (draw-tree a ctx)
       (send ctx translate dx (- dy)))
     
     (let ([dx (dx b)]
           [dy (dy b)])
       (send ctx draw-line 0 0 dx dy)
       
       (send ctx translate dx dy)
       (draw-tree b ctx)
       (send ctx translate (- dx) (- dy)))
     
     (draw-node 'R (format "~a" x) ctx)]
    [`(BB ,a ,x ,b)
     (send ctx set-pen "black" outline-width 'solid)
     
     (let ([dx (dx a)]
           [dy (dy a)])
       (send ctx draw-line 0 0 (- dx) dy)
       
       (send ctx translate (- dx) dy)
       (draw-tree a ctx)
       (send ctx translate dx (- dy)))
     
     (let ([dx (dx b)]
           [dy (dy b)])
       (send ctx draw-line 0 0 dx dy)
       
       (send ctx translate dx dy)
       (draw-tree b ctx)
       (send ctx translate (- dx) (- dy)))
     
     (draw-node 'BB (format "~a" x) ctx)]))
  (send ctx translate (+ inset (tree-left-width t)) (+ inset (n-e/2 t)))
  (render-tree-inner t ctx))

(define inset 8)

(define (render-tree t name)
  (let ([ctx (new pdf-dc%
                  [interactive #f]
                  [width (+ inset (tree-width t) inset (- inset))]
                  [height (+ inset (tree-height t) inset (- inset))]
                  [output (format "~a.pdf" name)])])
    (send ctx start-doc (symbol->string (gensym 'doc)))
    (send ctx start-page)
    (send ctx set-text-mode 'transparent)
    (send ctx translate (+ inset (tree-left-width t)) (+ inset (n-e/2 t)))
    (draw-tree t ctx)
    (send ctx end-page)
    (send ctx end-doc)))

(render-tree '(L)
             "empty")

(render-tree '(R (L) "x" (L))
             "single-red")

(render-tree '(R (B (label "a") "x" (label "b")) "y" (L))
             "red-black-left-subtree")

(render-tree '(B (R (label "a") "x" (label "b")) "y" (L))
             "black-red-left-subtree")

(render-tree '(B (L) "x" (L))
             "single-black")

#;(render-tree '(R (BB (label "a") "x" (label "b")) "y" (B (label "c") "z" (label "d")))
               "red-top-before")

#;(render-tree '(B (R (B (label "a") "x" (label "b")) "y" (label "c")) "z" (label "d"))
               "red-top-after")

#;(render-tree '(B (BB (label "a") "v" (label "b"))
                   "w"
                   (R (B (label "c") "x" (label "d"))
                      "y"
                      (B (label "e") "z" (label "f"))))
               "black-top-red-sibling-before")

