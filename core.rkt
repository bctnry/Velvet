#lang racket

;; velvet.
;; (c) sebastian lin. 2018

(require compatibility/defmacro)

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


;; rules:
;; 1. every primitive takes arguments (or takes no arguments)  & perform transformations on stack.
;; 2. all arguments are commands that will be evaluated on the stack of the calling machine state.
;;    when the evaluation is done, the top of the stack is taken as the result value.

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

;; to construct a primitive.
(defmacro define-primitive (calling x)
  `(define ,calling
     (λ (evaluator state)
       (let-values ([(env stack) (toValues state)])
         ,x))))

;; _dup :: {}[x:Any] -> [x:Any, x:Any]
(define-primitive _dup
  (MachineState env (cons (car stack) stack)))

;; _pop :: {}[x:Any] -> []
(define-primitive _pop
  (MachineState env (cdr stack)))

;; _swap :: {}[x:Any, y:Any] -> [y:Any, x:Any]
(define-primitive _swap
  (MachineState env (append (list (cadr stack) (car stack)) (cddr stack))))

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
(define-primitive (_branch x y)
  (let ([consumedState (MachineState env (cdr stack))])
    (evaluator consumedState (if (car stack) x y))))

;; _name :: {x:Meta(Symbol)}[] -> []
(define-primitive (_name x)
  (MachineState (bind-env x (car stack) env) stack))

;; _load :: {x:Meta(Symbol)}[] -> [value:Meta(TypeOfName(x))]
(define-primitive (_load x)
  (let ([lookupRes (lookup x env)])
    (if lookupRes
        (MachineState env (cons lookupRes stack))
        (begin (raise "Fail to lookup in the current environment.") state))))

(define-primitive _begin
  (MachineState (Env env (make-bindingEnv)) stack))

(define-primitive _end
  (MachineState (Env-parentEnv env) stack))

;; _define :: {x:Meta(Symbol), y:Meta(Listof(Symbol))}[body:QuotedValue]
;;         -> []
(define-primitive (_define name argList)
  (let ([predefval (DefinedValue env name argList (car stack))])
    (begin (set-DefinedValue-env! predefval (Env env (bind-singl name predefval (make-bindingEnv))))
           (MachineState (bind-env name predefval env) (cdr stack)))))

;; _lit :: {x:Any}[] -> [x:Any]
(define-primitive (_lit literal)
  (MachineState env (cons literal stack)))

(define-primitive (_immediate . cmdList)
  (evaluator state cmdList))

;; turn a QuotedValue into an anonymous (name equals to '?) DefinedValue.
(define-primitive (_abs . argList)
  (let ([quotedVal (car stack)])
    (let ([qenv (QuotedValue-env quotedVal)]
          [qbody (QuotedValue-cmdList quotedVal)])
      (MachineState env (cons (DefinedValue qenv '? argList qbody) (cdr stack))))))

;; turn a DefinedValue into a QuotedValue
(define-primitive _deabs
  (let ([definedVal (car stack)])
    (let ([denv (DefinedValue-env definedVal)]
          [dcmdList (DefinedValue-body definedVal)])
      (MachineState env (cons (QuotedValue denv dcmdList) (cdr stack))))))

(define-primitive (_call name . argList)
  (let* ([called-func (if (equal? name '?) (car stack) (lookup name env))]
         [called-func-arglist (DefinedValue-argList called-func)]
         [bound-values
          (let* ([lenArg (length argList)]
                 [lenDefArg (length called-func-arglist)]
                 [argList
                  (if (< lenArg lenDefArg)
                      (append argList
                              (for/list ([i (in-list (take stack (- lenDefArg lenArg)))])
                                (_lit i)))
                      argList)])
            (for/list ([i (in-list argList)])
              (if (equal? i '?)
                  (let ([arg (car stack)]) (begin (set! stack (cdr stack)) arg))
                  (let ([evaluatedState (evaluator state (list i))])
                    (car (MachineState-stack evaluatedState))))))]
         [bound-env (aux/multibind called-func-arglist bound-values (make-bindingEnv))])
    (evaluator (MachineState (Env env bound-env) stack)
               (append (QuotedValue-cmdList (DefinedValue-body called-func))
                       (list _end)))))

(define (aux/fromrkt fun argn leaving)
  (λ (evaluator state)
    (let-values ([(localEnv stack) (toValues state)])
      (let ([args (take stack argn)]
            [rst (drop stack (- argn leaving))])
        (MachineState localEnv (cons (apply fun args) rst))))))
(define (aux/fromrkt^ fun argn leaving)
  (λ (evaluator state)
    (let-values ([(localEnv stack) (toValues state)])
      (let ([args (take stack argn)]
            [rst (drop stack (- argn leaving))])
        (MachineState localEnv (cons (apply fun (reverse args)) rst))))))
(define (aux/fromrkt.vararg fun leaveval?)
  (λ argList
    (λ (evaluator state)
      (let-values ([(localEnv stack) (toValues state)])
        (let ([valList (for/list ([i (in-list argList)])
                         (car (MachineState-stack (evaluator state (list i)))))])
          (MachineState localEnv (cons (apply fun valList) (if leaveval? stack (cdr stack)))))))))
;; primitives for numbers.
(define _mult (aux/fromrkt * 2 0))
(define _plus (aux/fromrkt + 2 0))
(define _minus (aux/fromrkt^ - 2 0))
(define _div (aux/fromrkt^ / 2 0))
(define _intdiv (aux/fromrkt^ quotient 2 0))
(define _mod (aux/fromrkt^ modulo 2 0))
(define _bitand (aux/fromrkt bitwise-and 2 0))
(define _bitor (aux/fromrkt bitwise-ior 2 0))
(define _bitxor (aux/fromrkt bitwise-xor 2 0))
(define _bitnot (aux/fromrkt bitwise-not 1 0))
(define _multiplus (aux/fromrkt.vararg + #f))
(define _multimult (aux/fromrkt.vararg * #f))


;; predicates.
(define _isstring (aux/fromrkt string? 1 1))
(define _isquoted (aux/fromrkt QuotedValue? 1 1))
(define _isboolean (aux/fromrkt boolean? 1 1))
(define _isinteger (aux/fromrkt exact-integer? 1 1))
(define _isfloat (aux/fromrkt (λ (x) (and (not (exact-integer? x)) (real? x))) 1 1))

;; for making binary predicates
(define (aux/fromrkt.binpred fun newval?)
  (λ (evaluator state)
    (let-values ([(localEnv stack) (toValues state)])
      (MachineState localEnv (cons (fun (cadr stack) (car stack)) (if newval? stack (cdr stack)))))))
;; _lt :: {}[y:Number,x:Number] -> [result:Boolean,x:Number]
(define _lt (aux/fromrkt.binpred < #f))
(define _lt* (aux/fromrkt.binpred < #t))
(define (_lt/1 x)
  (λ (evaluator state)
    (let-values ([(localEnv stack) (toValues state)])
      (let ([evaluated (evaluator state (list x))])
        (MachineState localEnv (cons (< (car stack) (car (MachineState-stack evaluated))) stack))))))
;; TODO:
;; 2. complete _le(/1) and _ge(/1).
(define _le (aux/fromrkt.binpred <= #f))
(define _le* (aux/fromrkt.binpred <= #t))
(define-primitive (_le/1 x)
  (let ([evaluated (evaluator state (list x))])
    (MachineState env (cons (<= (car stack) (car (MachineState-stack evaluated))) stack))))
(define _ge (aux/fromrkt.binpred >= #f))
(define _ge* (aux/fromrkt.binpred >= #t))
(define-primitive (_ge/1 x)
  (let ([evaluated (evaluator state (list x))])
    (MachineState env (cons (>= (car stack) (car (MachineState-stack evaluated))) stack))))
;; _eq :: {}[y:Number,x:Number] -> [result:Boolean,x:Number]
(define _eq (aux/fromrkt.binpred equal? #f))
(define _eq* (aux/fromrkt.binpred equal? #t))
;; _eq/1 :: {x:Number}[y:Number] -> [result:Boolean,y:Number]
(define (_eq/1 x)
  (λ (evaluator state)
    (let-values ([(localEnv stack) (toValues state)])
      (let ([evaluated (evaluator state (list x))])
        (MachineState localEnv (cons (= (car stack) (car (MachineState-stack evaluated))) stack))))))
(define _gt (aux/fromrkt.binpred > #f))
(define _gt* (aux/fromrkt.binpred > #t))
(define (_gt/1 x)
  (λ (evaluator state)
    (let-values ([(localEnv stack) (toValues state)])
      (let ([evaluated (evaluator state (list x))])
        (MachineState localEnv (cons (> (car stack) (car (MachineState-stack evaluated))) stack))))))

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
(define _notbool (aux/fromrkt (λ (x) (not x)) 1 0))
(define _andbool (aux/fromrkt (λ (x y) (and x y)) 2 0))
(define _orbool (aux/fromrkt (λ (x y) (or x y)) 2 0))


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

(define (aux/evalres evaluator state cmdlist)
  (car (MachineState-stack (evaluator state cmdlist))))

;; primitives for tables.
;; lists are tables with special keys (just like lua).
;; TODO: complete _getval & _setval
;; _setval :: {}[v:val,k:key,d:table] -> [updated:table]
(define-primitive _table
  (MachineState env (cons (make-immutable-hash) stack)))
(define _setval
  (λ (evaluator state)
    (let-values ([(localEnv stack) (toValues state)])
      (let-values ([(value key table) (values (car stack) (cadr stack) (caddr stack))])
        (MachineState localEnv (cons (hash-set table key value) (cdddr stack)))))))
;; _setval/1 :: {k:key}[v:val,d:table] -> [updated:table]
(define-primitive (_setval/1 key)
  (let-values ([(value key table)
                (values (car stack) (aux/evalres evaluator state (list key)) (cadr stack))])
    (MachineState env (cons (hash-set table key value) (cddr stack)))))
;; _setval/2 :: {k:key,v:val}[d:table] -> [updated:table]
(define-primitive (_setval/2 key value)
  (let-values ([(value key table)
                (values (aux/evalres evaluator state (list value))
                        (aux/evalres evaluator state (list key))
                        (car stack))])
    (MachineState env (cons (hash-set table key value) (cdr stack)))))

(define (_substr/2 start end)
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
(evaluator
 st
 `(,_table
   ,(_lit 3)
   ,(_lit 4)
   ,_setval
   ,(_lit "val2")
   ,(_setval/1 (_lit "key2"))
   ,(_setval/2 (_immediate (_lit 3) (_lit 9) _plus) (_lit "val3"))
   ))
