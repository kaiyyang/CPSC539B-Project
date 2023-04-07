#lang racket
(require rosette)
(require rackunit)

;; ============================= Langauge Design =====================================
;
; Term
; e ::=               terms:
;   num               constant
;   x                 variables
;   (let x e e)       let bindings
;   (lambda x T e)    functions
;   (e x)             application
;   (e : T)           type-annotation
;
; v ::=               values:
;   num               constant
;   True | False      boolean constants
;   (lambda x T e)    abstraction value
;
; b ::=               Atomic primitive type
;   Int               Integer
;   Bool              Boolean
;
; T ::=               types:
;   b                 atomic primitive type
;   T -> T            Funciton Type
;  (Refi b x p)       Refinement Type

; p, q::=                Predicate
;  x                     variable
;  True | False          Boolean
;  Num
;  (< | <= | >= | >  p q)
;  (and p ...)
;  (or p ...)
;  (not q)
;  (if p then p else p)
;
; c ::=                  Constraints
;   (forall x b p c)     implication
;   (and c c)            conjunction
;   p                    predicates
;
;ctx ::=                 contexts
;   '()                  empty context
;   (dict-ref ctx x T)   term variable binding

;; ================================= Bidirectional Type Checking ===================================
(define (type-check v expected-type ctx)
  (match v
    ; CHK-LAM
    [`(lambda ,x ,T ,t)
     (match expected-type
       [`(,T-in -> ,T-out)
        (let ([T-term (type-check t (dict-set ctx x T) T-out)])
          `(,T-in -> ,T-term))]
       [_
        (error 'type-check "type mismatch: expected ~a, got lambda" expected-type)])]
    ; CHECK-LET
    [`(let ,x1 ,e1 ,e2)
     (let ([T1 (type-infer e1 ctx)])
       (type-check e2 expected-type (dict-set ctx x1 T1)))]
    [`(,e : ,T)
     (let ([T-e (type-check e T ctx)])
       (if (subtype? T-e T)
           T
           (error 'type-check "type mismatch: expected ~a, got ~a" T T-e)))]
    [`(,t1 ,t2)
     (let* ([T1 (type-check t1 expected-type ctx)]
            [T2 (type-check t2 T1 ctx)])
       T2)]
    ; CHK-SYN
    [x
     (let ([actual-type (type-infer x ctx)])
       (if (subtype? actual-type expected-type)
           expected-type
           (error 'type-check "actual type: ~a is not a subtype of expected type: ~a" actual-type expected-type)))]
    ))

(define (type-infer e ctx)
  (match e
    [`(,e : ,T)    ; SYN-ANN
     (if (and (check-type-wellness T) (type-check e T ctx))
         T
         (error 'type-infer "~a can not ascribe with type ~a" e T))]

    [v             ; SYN-CON
     #:when (is-primitive? v)
     (get-primitive-type v)]
    [`(lambda ,x ,T ,t)
     (let* ([_ (check-type-wellness T)]
            [T2 (type-infer t (dict-set ctx x T))])
       `(,T -> ,T2))]
    [`(,t1 ,t2)    ; (SYN-APP)
     (let ([T1 (type-infer t1 ctx)])
       (match T1
         [`(,T11 -> ,T12)
          (if (not (false? (type-check t2 T11 ctx)))
              T12
              (error 'type-infer "type infer error, SYN-APP fails type check"))]))]
    [`(let ,x ,e1 ,e2)
     (let ([T1 (type-infer e1 ctx)])
       (type-infer e2 (dict-set ctx x T1)))]
    [x              ; SYN-VAR
     (if (dict-has-key? ctx x)
         (dict-ref ctx x)
         (error 'type-infer "variable ~a not found in context" x))]))


;; ============================ Helper functions =============================
; value -> Boolean
; check if the given value is primitive value
(define (is-primitive? v)
  (match v
    ['True #t]
    ['False #t]
    [v #:when(number? v) #t]
    [_ #f]))

(define (is-refi-type? type)
  (match type
    [`(Refi ,b ,x ,p) #t]
    [_ #f]))

; value -> Base Type
; check if the given primitive value is primitive type
; (define (get-primitive-type v)
;   (match v
;     [v #:when (number? v)'Int]
;     ['True 'Bool]
;     ['False 'Bool]
;     [_ (error 'primitive-type "invalid primitive type ~a" v)]))

(define (get-primitive-type v)
  (match v
    [v #:when (number? v) `(Refi Int x (= x ,v))]
    ['True `(Refi Bool x True)]
    ['False `(Refi Bool x False)]
    [_ (error 'primitive-type "invalid primitive type ~a" v)]))

(define (check-type-wellness type)
  (match type
    ['Int #t]
    ['Bool #t]
    [`(Refi ,b ,x ,p)
     (match b
       ['Int #t]
       ['Bool #t]
       [_ (error 'check-type-wellness "invalid type ~a" type)])]
    [_ #f]))
; check if T1 is a subtype of T2
; T T -> Bool
(define (subtype? T1 T2)
  (match (cons T1 T2)
    ; a refinement type will be a subtype of its base type
    [`( ,T1 . ,T2)
     #:when (and (is-refi-type? T1) (is-primitive? T2))
     (match T1 [`(Refi ,x ,b ,p) (eq? b T2)])]
    [`(Int . ,T2) (eq? T2 'Int)] ; Int is only a subtype of Int
    [`(Bool . ,T2) (eq? T2 'Bool)] ; Bool is only a subtype of Bool
    [`((,T1i1 -> ,T1i2) . (,T2i1 -> ,T2i2))
     ;T1 <: S1  S2 <: T2 ; S1 -> S2 <: T1 -> T2
     (and (subtype? T2i1 T1i1) (subtype? T1i2 T2i2))] ; T1 is a function type and T2 is also a function type, and the argument and return types of T1 are subtypes of those of T2
    [`((Refi ,b1 ,x1 ,p1) . (Refi ,b2 ,x2 ,p2))
     ; SUB-BASE
     (if (eq? b1 b2)
         ;  Generate the VC and check the Constraints
         (check-constraint `(forall ,x2 ,b2 ,p2 ,(subst-pred x2 x1 p1)) '())
         #f)]
    [_ #f]))

; substitude all instance of v2 with v1
(define (subst-pred v1 v2 pred)
  (match pred
    ['True 'True]
    ['False 'False]
    [p #:when (eq? p v2) v1]
    [p #:when (or (number? p) (symbol? p)) p]
    [`(= ,p1 ,p2) `(= ,(subst-pred v1 v2 p1) ,(subst-pred v1 v2 p2))]
    [`(<= ,p1 ,p2) `(<= ,(subst-pred v1 v2 p1) ,(subst-pred v1 v2 p2))]
    [`(< ,p1 ,p2) `(< ,(subst-pred v1 v2 p1) ,(subst-pred v1 v2 p2))]
    [`(> ,p1 ,p2) `(> ,(subst-pred v1 v2 p1) ,(subst-pred v1 v2 p2))]
    [`(>= ,p1 ,p2) `(>= ,(subst-pred v1 v2 p1) ,(subst-pred v1 v2 p2))]
    [`(not ,p1) `(not ,(subst-pred v1 v2 p1))]
    [`(and ,p ...) `(and ,@(map (lambda (p) (subst-pred v1 v2 p)) p))]
    [`(or ,p ...) `(or ,@(map (lambda (p) (subst-pred v1 v2 p)) p))]
    [`(if ,p1 ,p2 ,p3) `(if ,(subst-pred v1 v2 p1) ,(subst-pred v1 v2 p2) ,(subst-pred v1 v2 p3))]
    [`(+ ,p1 ,p2) `(+ ,(subst-pred v1 v2 p1) ,(subst-pred v1 v2 p2))]
    [`(- ,p1 ,p2) `(+ ,(subst-pred v1 v2 p1) ,(subst-pred v1 v2 p2))]
    [_ (error 'subst-pred "invalid predicate ~a" pred)]))


; Use Rosette (z3) to check the constraints
(define (check-constraint c ctx)
  (define (define-symbolic-ctx ctx)
    (for ([key (in-dict-keys ctx)])
      (define symbolic-type (dict-ref ctx key))
      (match symbolic-type
        ['Int (eval `(define-symbolic ,key integer?))]
        ['Bool (eval `(define-symbolic ,key boolean?))]
        [_ (error "Unsupported type ~a" symbolic-type)])))
  (begin (define-symbolic-ctx ctx) (sat? (solve (eval `(assert ,(compile-constraint c ctx)))))))

(define (define-symbolic-func x T)
  (match T
    ['Int (eval `(define-symbolic ,x integer?))]
    ['Bool (eval `(define-symbolic ,x boolean?))]
    [_ (error "Unsupported type ~a" T)]))

; TODO: Compile the predicate to pass to rosette solver
(define (compile-predicate p)
  (match p
    ['True #t]
    ['False #f]
    [p #:when (or (number? p) (symbol? p)) p]
    [`(= ,p1 ,p2) `(= ,(compile-predicate p1) ,(compile-predicate p2))]
    [`(<= ,p1 ,p2) `(<= ,(compile-predicate p1) ,(compile-predicate p2))]
    [`(< ,p1 ,p2) `(< ,(compile-predicate p1) ,(compile-predicate p2))]
    [`(> ,p1 ,p2) `(> ,(compile-predicate p1) ,(compile-predicate p2))]
    [`(>= ,p1 ,p2) `(>= ,(compile-predicate p1) ,(compile-predicate p2))]
    [`(not ,p1) `(not ,(compile-predicate p1))]
    [`(and ,p ...) `(and ,@(map compile-predicate p))]
    [`(or ,p ...) `(or ,@(map compile-predicate p))]
    [`(if ,p1 ,p2 ,p3) `(if ,(compile-predicate p1) ,(compile-predicate p2) ,(compile-predicate p3))]
    [`(+ ,p1 ,p2) `(+ ,(compile-predicate p1) ,(compile-predicate p2))]
    [`(- ,p1 ,p2) `(+ ,(compile-predicate p1) ,(compile-predicate p2))]
    [_ (error 'check-constraint "invalid predicate ~a" p)]))

(define (compile-constraint c ctx)
  (match c
    [`(forall ,x ,T ,p ,c^) #:when (memq T '(Int Bool))
                            (let ([ctx^ (begin (define-symbolic-func x T) (dict-set ctx x T))])
                              `(and ,(compile-predicate p) ,(compile-constraint c^ ctx^)))]
    [`(forall ,x ,T ,p ,c) #:when !(memq T '(Int Bool))
                           (error 'check-constraint "invalid forall constraints on Non-Basic Type: ~a" T)]
    [`(and ,c1 ,c2) `(and ,(compile-constraint c1 ctx) ,(compile-constraint c2 ctx))]
    [p (compile-predicate p)]
    [_ (error 'check-constraint "invalid constraint ~a" c)]))


;; ===========================  Test Cases ===============================



(define ctx1 '((x . Int)))
(define ctx2 '((x . Int) (y . Int)))
(define ctx3 '((x . Int) (y . Int) (z . Int)))
(define cst0 '(forall x Int (= x 5) (forall y Int (= y (+ 1 x)) (and (>= x 0) (< y x)))))
(define cst1 '(forall x Int (= x 5) (forall y Int (= y (+ 1 x)) (and (>= x 0) (> y x)))))
(define test-cases
  (test-suite
   "Sample test cases for check-constraint function"
   (check-equal? (check-constraint '(and (<= x 10) (>= x 0)) ctx1) #t "x is in range [0, 10]")
   (check-equal? (check-constraint '(and (< x 10) (> x 0)) ctx1) #t "x is in range (0, 10)")
   (check-equal? (check-constraint '(and (<= x 0) (>= x 10)) ctx1) #f "x is in contradictory range")
   (check-equal? (check-constraint '(and (<= x 10) (>= y 0)) ctx2) #t "x is in range [0, 10] and y is in range [0, +inf)")
   (check-equal? (check-constraint '(and (<= x 10) (>= x 0) (>= y 5)) ctx2) #t "x is in range [0, 10] and y is in range [5, +inf)")
   (check-equal? (check-constraint '(and (<= x y) (>= y z) (>= x 0)) ctx3) #t "x <= y, y >= z, x >= 0")
   (check-equal? (check-constraint '(and (< x y) (> y z) (> x 0)) ctx3) #t "x < y, y > z, x > 0")
   (check-equal? (check-constraint cst0 '()) #f "x = 5, y = x + 1, x >= 0 && y < x")
   (check-equal? (check-constraint cst1 '()) #t "x = 5, y = x + 1, x >= 0 && y > x")))
(run-test test-cases)

(define val-T 'True)
(define val-F 'False)
(define val-fn-id-bool `(lambda x Bool x))
(define val-fn-id-int `(lambda x Int x))
(define add-fun `(((lambda x (Refi Int x (>= x 0)) (lambda y (Refi Int y (= y 1)) (add x y))) 1) 0))



(define refi-prog0-bad '((lambda x (Refi Int x (<= x 0)) x) 5))
(define refi-prog0-good '((lambda x (Refi Int x (<= x 0)) x) -5))
(define refi-prog1-good '((lambda x (Refi Bool x x) x) True))
(define refi-prog1-bad '((lambda x (Refi Bool x (and x False)) x) True))

(define tests-basic
  (test-suite "test for basic type infer on STLC"
              (check-equal? (type-infer val-F '()) '(Refi Bool x False) "False")
              (check-equal? (type-infer val-T '()) '(Refi Bool x True) "True")
              (check-equal? (type-infer val-fn-id-bool '()) '(Bool -> Bool) "boolean identity")
              (check-equal? (type-infer val-fn-id-int '()) '(Int -> Int) "boolean identity")
              (check-equal? (type-infer '(lambda x (Refi Int x (<= x 0)) x) '()) '((Refi Int x (<= x 0)) -> (Refi Int x (<= x 0))) "Basic lambda on refinment type")
              (check-equal? (type-infer '(lambda x (Refi Int x (<= x 0)) x) '()) '((Refi Int x (<= x 0)) -> (Refi Int x (<= x 0))) "Basic lambda on refinment type")
              (check-equal? (type-infer '(lambda x (Refi Int x (<= x 0)) x) '()) '((Refi Int x (<= x 0)) -> (Refi Int x (<= x 0))) "Basic lambda on refinment type")
              (check-equal? (type-infer refi-prog0-good '()) '(Refi Int x (<= x 0)) "refinement type good")
              (check-equal? (type-infer refi-prog1-good '()) '(Refi Bool x x) "refinement type good")))

(run-test tests-basic)