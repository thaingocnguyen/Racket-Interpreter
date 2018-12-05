#lang plai

;<RCFAE> ::= <num>
;        | {+ <RCFAE> <RCFAE>}
;        | {* <RCFAE> <RCFAE>}
;        | <id>
;        | {fun {<id>} <RCFAE>}
;        | {<RCFAE> <RCFAE>}
;        | {if0 <RCFAE> <RCFAE> <RCFAE>}
;        | {rec {<id> <RCFAE>} <RCFAE>}

(define-type RCFAE
  [num (n number?)]
  [add (lhs RCFAE?) (rhs RCFAE?)]
  [mult (lhs RCFAE?) (rhs RCFAE?)]
  [id (name symbol?)]
  [fun (param symbol?) (body RCFAE?)]
  [app (fun-expr RCFAE?) (arg RCFAE?)]
  [if0 (if-expr RCFAE?) (then-expr RCFAE?) (else-expr RCFAE?)]
  [rec (fun-name symbol?) (fun-def RCFAE?) (body RCFAE?)])

(define *reserved-symbols* '(id + * with app fun if0))

(define (valid-identifier? sym)
  (and (symbol? sym)
       (not (member sym *reserved-symbols*))))

;(define-type FunDef
;  [fundef (fun-name symbol?)
;          (arg-name symbol?)
;          (body RCFAE?)])
;
;(define (lookup-fundef fun-name fundefs)
;  (cond
;    [(empty? fundefs) (error fun-name "function not found")]
;    [else (if (symbol=? fun-name (fundef-fun-name (first fundefs)))
;              (first fundefs)
;              (lookup-fundef fun-name (rest fundefs)))]))


(define-type RCFAE-Value
  [numV (n number?)]
  [closureV (param symbol?)
            (body RCFAE?)
            (env Env?)]
  #;[exprV (expr RCFAE?)
         (env Env?)
         (cache boxed-boolean/RCFAE-Value?)])

(define (boxed-RCFAE-Value? v)
  (and (box? v)
       (RCFAE-Value? (unbox v))))

(define-type Env
  [mtSub]
  [aSub (name symbol?)
        (value RCFAE-Value?)
        (env Env?)]
  [aRecSub (name symbol?)
             (value boxed-RCFAE-Value?)
             (env Env?)])

(define (lookup name env)
  (type-case Env env
    [mtSub () (error 'lookup "no binding for identifier")]
    [aSub (bound-name bound-value rest-env)
          (if (symbol=? bound-name name)
              bound-value
              (lookup name rest-env))]
    [aRecSub (bound-name boxed-bound-value rest-env)
             (if (symbol=? bound-name name)
                 (unbox boxed-bound-value)
                 (lookup name rest-env))]))


#;(define (boxed-boolean/RCFAE-Value? v)
  (and (box? v)
       (or (boolean? (unbox v))
           (numV? (unbox v))
           (closureV? (unbox v)))))

;================= PARSER ==========================

(define (parse exp)
  (match exp
    [(? number?) (num exp)]
    [(? valid-identifier?) (id exp)]
    [(list '+ lhs rhs) (add (parse lhs) (parse rhs))]
    [(list '* lhs rhs) (mult (parse lhs) (parse rhs))]
    [(list f-expr a-expr)
     (app (parse f-expr) (parse a-expr))]
    [(list 'fun (list (and (? valid-identifier?) param)) fbody)
     (fun param (parse fbody))]
    [(list 'with (list (and (? valid-identifier?) name) named-expr) body)
     (app (fun name (parse body)) (parse named-expr))]
    [(list 'if0 ifexp texp fexp)
     (if0 (parse ifexp) (parse texp) (parse fexp))]
    [(list 'rec (list (and (? valid-identifier?) fun-name) named-expr) body)
     (rec fun-name (parse named-expr) (parse body))]
    ))

;(define (subst expr sub-id val)
;  (type-case RCFAE expr
;    [num (n) expr]
;    [add (l r) (add (subst l sub-id val)
;                    (subst r sub-id val))]
;    [id (v) (if (symbol=? v sub-id)
;                val
;                expr)]
;    [app (fun-name arg-expr)
;         (app fun-name (subst arg-expr sub-id val))]
;    [fun (bound-id bound-body)
;         (if (symbol=? bound-id sub-id)
;             (fun bound-id bound-body)
;             (fun bound-id (subst bound-body sub-id val)))]
;    ))
;============ INTERPRETER ===========================

(define (assert-type pred value)
  (if (pred value)
      value
      (error "Received a value of the wrong type")))





;; interp : RCFAE -> RCFAE
;; evaluates RCFAE expressions by reducing them to their corresponding values
;; return values are either num or fun 
(define (interp expr)
  (local [
          ;; strict : RCFAE-Value -> RCFAE-Value [excluding exprV]
          #;(define (strict e)
            (type-case RCFAE-Value e
              [exprV (expr env cache)
                     (local [(define the-value (strict (helper expr env)))]
                       (if (boolean? (unbox cache))
                           (begin ;(printf "Forcing exprV to ~a~n" the-value)
                                  (set-box! cache the-value)
                                  the-value)
                           (begin
                             ;(printf "Using cached values ~n")
                             (unbox cache))))]
              [else e]))

          (define (cyclically-bind-and-interp bound-id named-expr env)
            (local ([define value-holder (box (numV 1729))]
                    [define new-env (aRecSub bound-id value-holder env)]
                    [define named-expr-val (helper named-expr new-env)])
              (begin
                (set-box! value-holder named-expr-val)
                new-env)))
          (define (add-numbers lhs rhs)
            (numV (+ (numV-n lhs) (numV-n rhs))))
          (define (mult-numbers lhs rhs)
            (numV (* (numV-n lhs) (numV-n rhs))))

          (define (helper expr env)
            (type-case RCFAE expr
              [num (n) (numV n)]
              [add (l r) (add-numbers (helper l env) (helper r env))]
              [mult (l r) (mult-numbers (helper l env) (helper r env))]
              [id (v) (lookup v env)]
              [fun (bound-id bound-body)
                   (closureV bound-id bound-body env)]
              [app (fun-expr arg-expr)
                   (local [(define fun-val (helper fun-expr env))
                           #;(define arg-val (exprV arg-expr env (box false)))]
          
                     (helper (closureV-body fun-val)
                             (aSub (closureV-param fun-val)
                                   (helper arg-expr env)
                                   (closureV-env fun-val))))]
              [if0 (ie te fe)
                   (if (zero? (numV-n (helper ie env)))
                       (helper te env)
                       (helper fe env))]
              [rec (bound-id named-expr bound-body)
                (helper bound-body
                        (cyclically-bind-and-interp bound-id
                                                    named-expr
                                                    env))]
              ))]
    (helper expr (mtSub))))



;(test (interp (parse '5)) 5)
;(test (interp (parse '{+ 5 5})) 10)
;(test (interp (parse '{with {x {+ 5 5}} {+ x x}})) 20)
;(test (interp (parse '{with {x 5} {+ x x}})) 10)
;(test (interp (parse '{with {x {+ 5 5}} {with {y {- x 3}} {+ y y}}})) 14)
;(test (interp (parse '{with {x 5} {with {y {- x 3}} {+ y y}}})) 4)
;(test (interp (parse '{with {x 5} {+ x {with {x 3} 10}}})) 15)
;(test (interp (parse '{with {x 5} {+ x {with {x 3} x}}})) 8)
;(test (interp (parse '{with {x 5} {+ x {with {y 3} x}}})) 10)
;(test (interp (parse '{with {x 5} {with {y x} y}})) 5)
;(test (interp (parse '{with {x 5} {with {x x} x}})) 5)

;(interp (parse '{with {n 5} {f 10}}) (list (fundef 'f 'p (id 'n))) (mtSub))

;(interp (parse '{with {x 3}
;                      {with {f {fun {y} {+ x y}}}
;                            {with {x 5}
;                                  {f 4}}}})
;        (mtSub))
;
;(interp (parse '{with {x 3}
;                      {fun {y} {+ x y}}})
;        (mtSub))
(interp (parse '{with {x 3} x}))
(interp (parse '{with {x 3} {+ x x}}))
;(interp (parse '{with {f {undef x}} 4}))
(interp (parse '{with {x {+ 4 5}}
                      {with {y {+ x x}}
                            {with {z y}
                                  {with {x 4}
                                        z}}}}))
;{with {y {+ {+ 4 5} {+ 4 5}}}
;      {with {z y}
;            {with {x 4}
;                  z}}}
;{with {z {+ {+ 4 5} {+ 4 5}}}
;      {with {x 4}
;            z}}


(interp (parse '{if0 {+ 5 -5}
                     1
                     2}))
(interp (parse '{rec {fac {fun {n}
                                {if0 n
                                     1
                                     {* n {fac {+ n -1}}}}}}
                      {fac 5}}))

