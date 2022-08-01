#lang racket
(require data/heap)
(provide sim? wire?
         (contract-out
          [make-sim        (-> sim?)]
          [sim-wait!       (-> sim? positive? void?)]
          [sim-time        (-> sim? real?)]
          [sim-add-action! (-> sim? positive? (-> any/c) void?)]

          [make-wire       (-> sim? wire?)]
          [wire-on-change! (-> wire? (-> any/c) void?)]
          [wire-value      (-> wire? boolean?)]
          [wire-set!       (-> wire? boolean? void?)]

          [bus-value (-> (listof wire?) natural?)]
          [bus-set!  (-> (listof wire?) natural? void?)]

          [gate-not  (-> wire? wire? void?)]
          [gate-and  (-> wire? wire? wire? void?)]
          [gate-nand (-> wire? wire? wire? void?)]
          [gate-or   (-> wire? wire? wire? void?)]
          [gate-nor  (-> wire? wire? wire? void?)]
          [gate-xor  (-> wire? wire? wire? void?)]

          [wire-not  (-> wire? wire?)]
          [wire-and  (-> wire? wire? wire?)]
          [wire-nand (-> wire? wire? wire?)]
          [wire-or   (-> wire? wire? wire?)]
          [wire-nor  (-> wire? wire? wire?)]
          [wire-xor  (-> wire? wire? wire?)]

          [flip-flop (-> wire? wire? wire? void?)]))

(define (bus-set! wires value)
  (match wires
    ['() (void)]
    [(cons w wires)
     (begin
       (wire-set! w (= (modulo value 2) 1))
       (bus-set! wires (quotient value 2)))]))

(define (bus-value ws)
  (foldr (lambda (w value) (+ (if (wire-value w) 1 0) (* 2 value)))
         0
         ws))

(define (flip-flop out clk data)
  (define sim (wire-sim data))
  (define w1  (make-wire sim))
  (define w2  (make-wire sim))
  (define w3  (wire-nand (wire-and w1 clk) w2))
  (gate-nand w1 clk (wire-nand w2 w1))
  (gate-nand w2 w3 data)
  (gate-nand out w1 (wire-nand out w3)))

(struct sim ([time #:mutable] [action-queue #:mutable]))
(struct wire ([value #:mutable] [actions #:mutable] sim))

; global variables
(define gate-delay 1)
(define xor-delay 2)


(define (empty-heap? h)
  (if (= (heap-count h) 0)
      #t
      #f))
      
(define (make-sim)
  (sim 0 (make-heap (lambda (x y) (< (car x) (car y))))))

(define (sim-wait! simulation dt)
  (define end-t (+ {sim-time simulation} dt))
  (process-sim-actions simulation end-t))

(define (process-more-actions? sim-heap end-t)
  (cond [(empty-heap? sim-heap) #f]
        [(> {car (heap-min sim-heap)} end-t) #f]
        [else #t]))

(define (process-sim-actions simulation end-t)
 
  (define sim-heap (sim-action-queue simulation))
  (if (process-more-actions? sim-heap end-t)
      (begin
        (let* ([first-action (heap-min sim-heap)]
               [action-time (car first-action)]
               [action-function (cadr first-action)])
          (begin
            (heap-remove-min! sim-heap)
            (set-sim-time! simulation action-time)
            (action-function)
            (process-sim-actions simulation end-t))))
      (begin
        (set-sim-time! simulation end-t)
        (void))))
             

(define (sim-add-action! simulation dt action)
  (define new-action (list {+ (sim-time simulation) dt} action))
  (heap-add! (sim-action-queue simulation) new-action))
;=======================WIRE===================

(define (make-wire simulation)
  (wire #f '() simulation))

(define (wire-on-change! wire_ action)
  (begin
    (action)
    (set-wire-actions! wire_ (cons action (wire-actions wire_)))))

(define (call-actions actions)
  (match actions
    ['() (void)]
    [(cons action rest-actions)
     (begin
       (action)
       (call-actions rest-actions))]))

(define (wire-set! wire_ new-value)
  (if (eq? new-value (wire-value wire_))
      (void)
      (begin
        (set-wire-value! wire_ new-value)
        (call-actions (wire-actions wire_)))))

;======================GATES==================
(define (same-sim? w1 w2)
  (if (eq? (wire-sim w1) (wire-sim w2))
      #t
      #f))
;NOT GATE
(define (gate-not w-res w1)
  (if (same-sim? w1 w-res)  
      (let [(not-action
             (lambda () (sim-add-action! (wire-sim w-res)
                                         gate-delay
                                         (lambda () (wire-set! w-res (not (wire-value w1)))))))]
        (wire-on-change! w1 not-action))
      (error 'gate-not "connected wires must be in the same simulation")))
      
;AND GATE
(define (gate-and w-res w1 w2)
  (if (and (same-sim? w1 w2) (same-sim? w2 w-res))
      (let  [(and-action
              (lambda ()(sim-add-action! (wire-sim w-res)
                                         gate-delay
                                         (lambda () (wire-set! w-res (and (wire-value w1) (wire-value w2)))))))]
        (wire-on-change! w1 and-action)
        (wire-on-change! w2 and-action))
      (error 'gate-and "connected wires must be in the same simulation")))

;NAND GATE
(define (gate-nand w-res w1 w2)
  (if (and (same-sim? w1 w2) (same-sim? w2 w-res))
      (let [(nand-action
             (lambda () (sim-add-action! (wire-sim w-res)
                                         gate-delay
                                         (lambda () (wire-set! w-res (not (and (wire-value w1) (wire-value w2))))))))]
        (wire-on-change! w1 nand-action)
        (wire-on-change! w2 nand-action))
      (error 'gate-nand "connected wires must be in the same simulation")))

;OR GATE
(define (gate-or w-res w1 w2)
  (if (and (same-sim? w1 w2) (same-sim? w2 w-res))
      (let [(or-action
             (lambda ()(sim-add-action! (wire-sim w-res)
                                        gate-delay
                                        (lambda () (wire-set! w-res (or (wire-value w1) (wire-value w2)))))))]
        (wire-on-change! w1 or-action)
        (wire-on-change! w2 or-action))
      (error 'gate-or "connected wires must be in the same simulation")))

;NOR GATE
(define (gate-nor w-res w1 w2)
  (if (and (same-sim? w1 w2) (same-sim? w2 w-res))
      (let [(nor-action
             (lambda () (sim-add-action! (wire-sim w-res)
                                         gate-delay
                                         (lambda () (wire-set! w-res (not (or (wire-value w1) (wire-value w2))))))))]
        (wire-on-change! w1 nor-action)
        (wire-on-change! w2 nor-action))
      (error 'gate-nor "connected wires must be in the same simulation")))
       

;XOR GATE
(define (gate-xor w-res w1 w2)
  (if (and (same-sim? w1 w2) (same-sim? w2 w-res))
      (let [(xor-action
             (lambda () (sim-add-action! (wire-sim w-res)
                                         xor-delay
                                         (lambda () (wire-set! w-res (not (eq? (wire-value w1) (wire-value w2))))))))]
        (wire-on-change! w1 xor-action)
        (wire-on-change! w2 xor-action))
      (error 'gate-xor "connected wires must be in the same simulation")))

(define (wire-not w1 )
  (define w (make-wire (wire-sim w1)))
  (gate-not w w1)
  w)

(define (wire-nand w1 w2)
  (if (same-sim? w1 w2)
      (let [(w (make-wire (wire-sim w1)))]
        (gate-nand w w1 w2)
        w)
      (error 'wire-nand "connected wires must be in the same simulation")))

(define (wire-and w1 w2)
  (if (same-sim? w1 w2)
      (let [(w (make-wire (wire-sim w1)))]
        (gate-and w w1 w2)
        w)
      (error 'wire-and "connected wires must be in the same simulation")))

(define (wire-or w1 w2)
  (if (same-sim? w1 w2)   
      (let [(w (make-wire (wire-sim w1)))]
        (gate-or w w1 w2)
        w)
      (error 'wire-or "connected wires must be in the same simulation")))

(define (wire-nor w1 w2)
  (if (same-sim? w1 w2) 
      (let [(w (make-wire (wire-sim w1)))]
        (gate-nor w w1 w2)
        w)
      (error 'wire-nor "connected wires must be in the same simulation")))

(define (wire-xor w1 w2)
  (if (same-sim? w1 w2)
      (let [(w (make-wire (wire-sim w1)))]
        (gate-xor w w1 w2)
        w)
      (error 'wire-xor "connected wires must be in the same simulation")))
