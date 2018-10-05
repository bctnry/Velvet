#lang racket
;; velvet.
;; (c) sebastian lin. 2018

#|
"fac"
    "fac_iter:n,res"
        n <1 or:=1
        ifTrue:[res]
        ifFalse:[
          n res * name:res pop   // n * res -> res, leaving the stack with n on the top
          n -1 name:n pop    // n - 1 -> n
          fac_iter:n,res
        ]
    ;
    fac_iter:?,1
;
=>
(def fac ()
  (def fac_iter (n res)
    n (< 1) (or (= 1))
    (ifTrue (quoted res))
    (ifFalse (quoted
      n res * (name res) pop
      n (- 1) (name n) pop
      (fac_iter n res))))
  (fac_iter ? 1))
|#

(struct MachineState (localEnv stack) #:transparent)
(define (toValues machineState)
  (values (MachineState-localEnv machineState)
          (MachineState-stack machineState)))
(struct Env (parentEnv binding) #:transparent)
(define (lookup varSymbol env)
  (if env
      (let ([preres (lookUp-singl varSymbol (Env-binding env))])
        (if preres
            preres
            (lookup varSymbol (Env-parentEnv env))))
      #f))
(define (lookUp-singl varSymbol env)
  (hash-ref env varSymbol #f))
(define (make-bindingEnv)
  (make-immutable-hash))
(define (bind-singl varSymbol value env)
  (hash-set env varSymbol value))
(define (bind-env varSymbol value env)
  (Env (Env-parentEnv env) (bind-singl varSymbol value (Env-binding env))))
(struct QuotedValue (env cmdList) #:transparent)
(struct DefinedValue (env name argList body) #:transparent #:mutable)
;; TODO:
;; 3. complete _call & other primitives.

;; _dup :: {}[x:Any] -> [x:Any, x:Any]
(define _dup
  (λ (evaluator state)
    (let-values ([(localEnv stack) (toValues state)])
      (MachineState localEnv (cons (car stack) stack)))))
;; _pop :: {}[x:Any] -> []
(define _pop
  (λ (evaluator state)
    (let-values ([(localEnv stack) (toValues state)])
      (MachineState localEnv (cdr stack)))))
;; _swap :: {}[x:Any, y:Any] -> [y:Any, x:Any]
(define _swap
  (λ (evaluator state)
    (let-values ([(localEnv stack) (toValues state)])
      (MachineState localEnv (cons (cadr stack) (cons (car stack) (cddr stack)))))))
;; _quoted :: {cmdlist:Meta(Listof(Command))}[] -> [cmdlist:QuotedVal]
(define-syntax-rule (_quoted x)
  (λ (evaluator state)
    (let-values ([(localEnv stack) (toValues state)])
      (MachineState localEnv (cons (QuotedValue localEnv x) stack)))))

;; _prj :: {n:Integer}[x:QuotedValue(l of List)] -> [elem:QuotedValue(e), x:QuotedValue(l of List)]
;;      where e = Typeof (nth n l)
(define (_prj n)
  (λ (evaluator state)
    (let-values ([(localEnv stack) (toValues state)])
      (MachineState localEnv
                    (cons (QuotedValue (QuotedValue-env (car stack))
                                       (aux/nth n (QuotedValue-cmdList (car stack))))
                          stack)))))
;; _exec :: {}[x:QuotedValue(A->B), A] -> [B]
(define _exec
  (λ (evaluator state)
    (let-values ([(localEnv stack) (toValues state)])
      (let ([evaluatedState
             (evaluator (MachineState (Env localEnv (QuotedValue-env (car stack)))
                                      (cdr stack))
                        (QuotedValue-cmdList (car stack)))])
      (MachineState (Env-parentEnv (MachineState-localEnv evaluatedState))
                    (MachineState-stack evaluatedState))))))
;; _branch :: {iftrue:QuotedValue(A->B), iffalse:QuotedValue(A->C)}[cond:Boolean, A]
;;         -> [B] or [C]
(define (_branch x y)
  (λ (evaluator state)
    (let-values ([(localEnv stack) (toValues state)])
      (let ([consumedState (MachineState localEnv (cdr stack))])
        (if (car stack)
            (evaluator consumedState x)
            (evaluator consumedState y))))))
;; _name :: {x:Meta(Symbol)}[] -> []
(define (_name x)
  (λ (evaluator state)
    (let-values ([(localEnv stack) (toValues state)])
      (MachineState (bind-env x (car stack) localEnv) stack))))
;; _load :: {x:Meta(Symbol)}[] -> [value:Meta(TypeOfName(x))]
(define (_load x)
  (λ (evaluator state)
    (let-values ([(localEnv stack) (toValues state)])
      (let ([lookupRes (lookup x localEnv)])
        (if lookupRes
            (MachineState localEnv (cons lookupRes stack))
            (begin (raise "Fail to lookup in the current environment.") state))))))
(define _begin
  (λ (evaluator state)
    (let-values ([(localEnv stack) (toValues state)])
      (MachineState (Env localEnv (make-bindingEnv)) stack))))
(define _end
  (λ (evaluator state)
    (let-values ([(localEnv stack) (toValues state)])
      (MachineState (Env-parentEnv localEnv) stack))))
;; _define :: {x:Meta(Symbol), y:Meta(Listof(Symbol))}[body:QuotedValue]
;;         -> []
(define (_define name argList)
  (λ (evaluator state)
    (let-values ([(localEnv stack) (toValues state)])
      ;; here, we need a little side effect to cope this...
      (let ([preDefVal (DefinedValue localEnv name argList (car stack))])
        (begin (set-DefinedValue-env! preDefVal (Env localEnv (bind-singl name preDefVal (make-bindingEnv))))
               (MachineState (bind-env name preDefVal localEnv)
                             (cdr stack)))))))
;; _lit :: {x:Any}[] -> [x:Any]
(define (_lit literal)
  (λ (evaluator state)
    (let-values ([(localEnv stack) (toValues state)])
      (MachineState localEnv (cons literal stack)))))
(define (_immediate . cmdList)
  (λ (evaluator state)
    (let-values ([(localEnv stack) (toValues state)])
      (evaluator (MachineState localEnv stack) cmdList))))
(define (_call name . argList)
  (λ (evaluator state)
    (let-values ([(localEnv stack) (toValues state)])
      (let* ([bound-values
              (let ([stack stack])
                (for/list ([i (in-list argList)])
                  (if (equal? i '?)
                      (let ([arg (car stack)]) (begin (set! stack (cdr stack)) arg))
                      (let ([evaluatedState (evaluator state (list i))])
                        (car (MachineState-stack evaluatedState))))))]
             [called-func (lookup name localEnv)]
             [called-func-arglist (DefinedValue-argList called-func)]
             [bound-env (aux/multibind called-func-arglist bound-values (make-bindingEnv))])
        ;; TODO: handle the case where argList is smaller than the arglist defined in the env.
        (evaluator (MachineState (Env localEnv bound-env) stack)
                   (append (QuotedValue-cmdList (DefinedValue-body called-func))
                           (list _end)))))))
;; _dec :: {}[x:Number] -> [result:Number]
(define _dec
  (λ (evaluator state)
    (let-values ([(localEnv stack) (toValues state)])
      (MachineState localEnv (cons (- (car stack) 1) (cdr stack))))))
;; _lt :: {x:Number}[y:Number] -> [result:Boolean,y:Number]
(define (_lt x)
  (λ (evaluator state)
    (let-values ([(localEnv stack) (toValues state)])
      (MachineState localEnv (cons (< (car stack) x) stack)))))
;; _eq :: {x:Number}[y:Number] -> [result:Boolean,y:Number]
(define (_eq x)
  (λ (evaluator state)
    (let-values ([(localEnv stack) (toValues state)])
      (MachineState localEnv (cons (equal? x (car stack)) stack)))))

(define (aux/fromrkt fun argn)
  (λ (evaluator state)
    (let-values ([(localEnv stack) (toValues state)])
      (let-values ([(args rst) (split-at stack argn)])
        (MachineState localEnv (cons (apply fun args) rst))))))

;; primitives for numbers. 
(define _mult (aux/fromrkt * 2))
(define _plus (aux/fromrkt + 2))
(define _minus
  (λ (evaluator state)
    (let-values ([(localEnv stack) (toValues state)])
      (MachineState localEnv (cons (- (cadr stack) (car stack)) (cddr stack))))))
(define _div
  (λ (evaluator state)
    (let-values ([(localEnv stack) (toValues state)])
      (MachineState localEnv (cons (/ (cadr stack) (car stack)) (cddr stack))))))
(define _intdiv
  (λ (evaluator state)
    (let-values ([(localEnv stack) (toValues state)])
      (MachineState localEnv (cons (quotient (cadr stack) (car stack)) (cddr stack))))))
(define _mod
  (λ (evaluator state)
    (let-values ([(localEnv stack) (toValues state)])
      (MachineState localEnv (cons (modulo (cadr stack) (car stack)) (cddr stack))))))
  

(define (aux/fromrkt* fun argn)
  (λ (evaluator state)
    (let-values ([(localEnv stack) (toValues state)])
      (let-values ([(args rst) (split-at stack argn)])
        (MachineState localEnv (cons (apply fun args) stack))))))

;; predicates.
(define _isstring (aux/fromrkt* string? 1))
(define _isquoted (aux/fromrkt* QuotedValue? 1))
(define _isboolean (aux/fromrkt* boolean? 1))
(define _isinteger (aux/fromrkt* exact-integer? 1))
(define _isfloat (aux/fromrkt* (λ (x) (and (not (exact-integer? x)) (real? x))) 1))

;; predicate combinators.
(define (_and x . rst)
  (λ (evaluator state)
    (let-values ([(localEnv stack) (toValues state)])
      (MachineState localEnv (cons
                              (for/and ([i (in-list (cons x rst))])
                                (let ([evaluatedState (evaluator state (list i))])
                                  (car (MachineState-stack evaluatedState))))
                              stack)))))
(define (_or x . rst)
  (λ (evaluator state)
    (let-values ([(localEnv stack) (toValues state)])
      (MachineState localEnv (cons
                              (for/or ([i (in-list (cons x rst))])
                                (let ([evaluatedState (evaluator state (list i))])
                                  (car (MachineState-stack evaluatedState))))
                              stack)))))
(define (_not x)
  (λ (evaluator state)
    (let-values ([(localEnv stack) (toValues state)])
      (let ([evaluatedState (evaluator state (list x))])
        (MachineState localEnv (cons (not (car (MachineState-stack evaluatedState))) stack))))))
;; primitives for boolean values.
(define _notbool (aux/fromrkt (λ (x) (not x)) 1))
(define _andbool (aux/fromrkt (λ (x y) (and x y)) 2))
(define _orbool (aux/fromrkt (λ (x y) (or x y)) 2))


;; primitives for quoted values.
(define _putbefore
  (λ (evaluator state)
    (let-values ([(localEnv stack) (toValues state)])
      (let ([quotedVal (cadr stack)]
            [addedVal (car stack)]
            [rst (cddr stack)])
        (MachineState localEnv (cons (QuotedValue (QuotedValue-env quotedVal)
                                                  (cons (_lit addedVal) (QuotedValue-cmdList quotedVal)))
                                     rst))))))
(define _putafter
  (λ (evaluator state)
    (let-values ([(localEnv stack) (toValues state)])
      (let ([quotedVal (cadr stack)]
            [addedVal (car stack)]
            [rst (cddr stack)])
        (MachineState localEnv (cons (QuotedValue (QuotedValue-env quotedVal)
                                                  (append (QuotedValue-cmdList quotedVal)
                                                          (list (_lit addedVal))))
                                     rst))))))
(define _removebefore
  (λ (evaluator state)
    (let-values ([(localEnv stack) (toValues state)])
      (let ([quotedVal (car stack)]
            [rst (cdr stack)])
        (MachineState localEnv (cons (QuotedValue (QuotedValue-env quotedVal)
                                                  (cdr (QuotedValue-cmdList quotedVal)))
                                     rst))))))
(define _removeafter
  (λ (evaluator state)
    (let-values ([(localEnv stack) (toValues state)])
      (let ([quotedVal (cadr stack)]
            [addedVal (car stack)]
            [rst (cddr stack)])
        (MachineState localEnv (cons (QuotedValue (QuotedValue-env quotedVal)
                                                  (drop-right (QuotedValue-cmdList quotedVal) 1))
                                     rst))))))
(define (_substr start end)
  (λ (evaluator state)
    (let-values ([(localEnv stack) (toValues state)])
      (MachineState localEnv (cons (substring (car stack) start end) stack)))))
(define _strappend
  (λ (evaluator state)
    (let-values ([(localEnv stack) (toValues state)])
      (MachineState localEnv (cons (string-append (cadr stack) (car stack)) (cddr stack))))))

(define _debug
  (λ (evaluator state)
    (displayln state)
    state))
                     
(define (evaluator state cmdList)
  (cond ((null? cmdList) state)
        ((= (length cmdList) 1) ((car cmdList) evaluator state))
        (#t
         (let ([evaluatedState ((car cmdList) evaluator state)])
           (evaluator evaluatedState (cdr cmdList))))))
(define (aux/nth n list)
  (cond ((= n 1) (car list))
        (#t
         (aux/nth (- n 1) (cdr list)))))
(define (aux/multibind nameList valueList env)
  (begin (for ([name (in-list nameList)] [value (in-list valueList)])
           (set! env (hash-set env name value)))
         env))
(define emptyEnv (Env #f (make-bindingEnv)))
(define st (MachineState emptyEnv '()))
#|
(velvet-evaluator
 st
 `(,(_quoted `(,(_load 'x) ,_dup))
   ,(_define 'mydup '(x))
   ,(_quoted
     `(,(_load 'x)
       ,(_lt 2)
       ,(_branch
         `(,_pop ,(_lit 1))
         `(,(_call 'factorial (_immediate (_load 'x) _dec))
           ,_mult
           ))))
   ,(_define 'factorial '(x))
   ,(_lit 5)
   ,(_call 'factorial '?)
   ))
|#
(evaluator
 st
 `(,(_lit 3)
   ,(_and (_or (_lt 3) (_lt 6)))
   ,(_quoted `(,(_lit 3)))
   ,(_lit 3)
   ,_putbefore
   ))
#|
(velvet-evaluator
 st
 `(,(_quoted `(,_swap ,_dup))
   ,(_branch
     `(,(_lit 3))
     `(,(_lit 4)))))

|#
