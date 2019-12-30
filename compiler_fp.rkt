#lang racket

; code by Shujun Liu
; function for each pass: 
; typecheck shrink uniquify reveal-functions convert-to-clos limit-functions remove-complex-opera* expose-allocation explicate-control select-instructions uncover-live allocate-registers patch-instructions print-x86 

; type checker

(define (flat-ty? ty)
  (match ty
    ('Integer #t)
    ('Boolean #t)
    ('Void #t)
    ('(Vectorof Any) #t)
    (`(Vector Any ...) #t)
    (`(Any ... -> Any) #t)
    (_ #f)))
  
(define (type-check-exp env)
  (lambda (e)
    (define recur (type-check-exp env))
    (define (err t) (error 'type-check-exp "~a : Expects ~a" e t))
    (match e
      (`(inject ,e ,ty)
       (unless (flat-ty? ty)
         (error 'typecheck "may only inject a value of flat type, not ~a" ty))
       (define-values (new-e e-ty) (recur e))
       (cond
         ((equal? e-ty ty)
          (values `(has-type (inject ,new-e ,ty) Any) 'Any))
         (else
          (match e-ty
            (`(Vector Any ...)
             (if (equal? ty '(Vectorof Any))
                 (values `(has-type (inject ,new-e ,ty) Any) 'Any)
                 (error 'typecheck "inject expected ~a to have type ~a" e ty)))
            (else (error 'typecheck "inject expected ~a to have type ~a" e ty))))))
      (`(project ,e ,ty)
       (unless (flat-ty? ty)
         (error 'typecheck "may only project to a flat type, not ~a" ty))
       (define-values (new-e e-ty) (recur e))
       (cond
         ((equal? e-ty 'Any)
          (values `(has-type (project ,new-e ,ty) ,ty) ty))
         (else
          (error 'typecheck "project expected ~a to have type Any" e))))
      (`(boolean? ,exp)
       (define-values (ee te) (recur exp))
       (if (eq? te 'Any)
           (values `(has-type (boolean? ,ee) Boolean) 'Boolean)
           (error 'typecheck "tagged value expected in ~a" e)))
      (`(integer? ,exp)
       (define-values (ee te) (recur exp))
       (if (eq? te 'Any)
           (values `(has-type (integer? ,ee) Boolean) 'Boolean)
           (error 'typecheck "tagged value expected in ~a" e)))
      (`(vector? ,exp)
       (define-values (ee te) (recur exp))
       (if (eq? te 'Any)
           (values `(has-type (vector? ,ee) Boolean) 'Boolean)
           (error 'typecheck "tagged value expected in ~a" e)))
      (`(procedure? ,exp)
       (define-values (ee te) (recur exp))
       (if (eq? te 'Any)
           (values `(has-type (procedure? ,ee) Boolean) 'Boolean)
           (error 'typecheck "tagged value expected in ~a" e)))
      (`(void? ,exp)
       (define-values (ee te) (recur exp))
       (if (eq? te 'Any)
           (values `(has-type (void? ,ee) Boolean) 'Boolean)
           (error 'typecheck "tagged value expected in ~a" e)))
      ('(void) (values `(has-type (void) Void) 'Void))
      [(? fixnum? n) (values `(has-type ,n Integer) 'Integer)]
      [(? boolean? b) (values `(has-type ,b Boolean) 'Boolean)]
      [(? flonum? n) (values `(has-type ,n Double) 'Double)]
      [(? symbol? x)
       (let ((t (dict-ref env x)))
         (values `(has-type ,x ,t) t))]
      [`(read) (values `(has-type (read) Integer) 'Integer)]
      (`(vector ,es ...)
       (define-values (e* t*) (for/lists (e* t*) ((e es)) (recur e)))
       (let ((t `(Vector ,@t*)))
         (values `(has-type (vector ,@e*) ,t) t)))
      (`(vector-ref ,v ,i)
       (define-values (ev tv) (recur v))
       (match tv
         (`(Vector ,ts ...)
          (unless (and (exact-nonnegative-integer? i) (< i (length ts)))
            (error 'type-check-exp "invalid index ~a" i))
          (let ((ti (list-ref ts i)))
            (values `(has-type (vector-ref ,ev (has-type ,i Integer)) ,ti) ti)))
         (`(Vectorof ,ty)
          (unless (exact-nonnegative-integer? i)
            (error 'type-check-exp "invalid index ~a" i))
          (values `(has-type (vector-ref ,ev (has-type ,i Integer)) ,ty) ty))
         (else (error "expected a vector in vector-ref, not" tv))))
      (`(vector-set! ,v ,i ,new)
       (define-values (ev tv) (recur v))
       (define-values (en tn) (recur new))
       (match tv
         (`(Vector ,ts ...)
          (unless (and (exact-nonnegative-integer? i) (< i (length ts)))
            (error 'type-check-exp "invalid index ~a" i))
          (let ((t (list-ref ts i)))
            (match* (t tn)
              ((`(Vector ,ts1 ...) `(Vector ,ts2 ...))
               (values `(has-type (vector-set! ,ev (has-type ,i Integer) ,en) Void) 'Void))
              ((_ _)
               (unless (equal? tn t)
                 (error 'type-check-exp "does not support changing type of a vector element:~a" e))
               (values `(has-type (vector-set! ,ev (has-type ,i Integer) ,en) Void) 'Void)))))
         (`(Vectorof ,ty)
          (unless (exact-nonnegative-integer? i)
            (error 'type-check-exp "invalid index ~a" i))
          (if (equal? tn ty)
              (values `(has-type (vector-set! ,ev (has-type ,i Integer) ,en) Void) 'Void)
              (error 'type-check-exp "does not support changing type of a vector element:~a" e)))
         (else (error "expected a vector in vector-set!, not" tv))))          
      (`(eq? ,arg1 ,arg2)
       (define-values (e1 t1) (recur arg1))
       (define-values (e2 t2) (recur arg2))
       (match* (t1 t2)
         ((`(Vector ,ts1 ...) `(Vector ,ts2 ...))
          (values `(has-type (eq? ,e1 ,e2) Boolean) 'Boolean))
         ((_ _)
          (if (eq? t1 t2)
              (values `(has-type (eq? ,e1 ,e2) Boolean) 'Boolean)
              (match `(,t1 ,t2)
                ((or '(Double Integer) '(Integer Double) '(Double Double))
                 (values `(has-type (feq? ,e1 ,e2) Boolean) 'Boolean))
                (_ (error "expected args in eq? to be of same type" e)))))))
      [`(let ([,x ,e]) ,body)
        (define-values (ee te) (recur e))
        (define new-env (cons (cons x te) env))        
        (define-values (eb tb) ((type-check-exp new-env) body))
        (values `(has-type (let ((,x ,ee)) ,eb) ,tb) tb)]
      [`(- ,e)
       (define-values (ee te) (recur e))
       (match te
         ('Integer
          (values `(has-type (- ,ee) ,te) te))
         ('Double
          (values `(has-type (-f ,ee) ,te) te)) 
         (else (err 'Integer\ or\ Double)))]
      [`(int ,e)
       (define-values (ee te) (recur e))
       (match te
         ('Integer
          (values `(has-type ,ee Integer) 'Integer))
         ('Double
          (values `(has-type (int ,ee) Integer) 'Integer))
         (_
          (err 'a\ Double)))]
      (`(+ ,e1 ,e2)
       (define-values (ee1 te1) (recur e1))
       (define-values (ee2 te2) (recur e2))
       (match `(,te1 ,te2)
         ('(Integer Integer)
          (values `(has-type (+ ,ee1 ,ee2) Integer) 'Integer))
         ((or '(Integer Double) '(Double Integer) '(Double Double))
          (values `(has-type (+f ,(if (equal? te1 'Integer) `(has-type (double ,ee1) Double) ee1) ,(if (equal? te2 'Integer) `(has-type (double ,ee2) Double) ee2)) Double) 'Double))
         (_
          (err 'two\ Integers\ or\ Doubles))))
      (`(- ,e1 ,e2)
       (define-values (ee1 te1) (recur e1))
       (define-values (ee2 te2) (recur e2))
       (match `(,te1 ,te2)
         ('(Integer Integer)
          (values `(has-type (- ,ee1 ,ee2) Integer) 'Integer))
         ((or '(Integer Double) '(Double Integer) '(Double Double))
          (values `(has-type (-f ,(if (equal? te1 'Integer) `(has-type (double ,ee1) Double) ee1) ,(if (equal? te2 'Integer) `(has-type (double ,ee2) Double) ee2)) Double) 'Double))
         (_
          (err 'two\ Integers\ or\ Doubles))))
      (`(and ,e1 ,e2)
       (define-values (ee1 te1) (recur e1))
       (define-values (ee2 te2) (recur e2))
       (match* (te1 te2)
         (('Boolean 'Boolean)
          (values `(has-type (and ,ee1 ,ee2) Boolean) 'Boolean))
         ((_ _)
          (err 'two\ Booleans))))
      (`(or ,e1 ,e2)
       (define-values (ee1 te1) (recur e1))
       (define-values (ee2 te2) (recur e2))
       (match* (te1 te2)
         (('Boolean 'Boolean)
          (values `(has-type (or ,ee1 ,ee2) Boolean) 'Boolean))
         ((_ _)
          (err 'two\ Booleans))))
      (`(< ,e1 ,e2)
       (define-values (ee1 te1) (recur e1))
       (define-values (ee2 te2) (recur e2))
       (match `(,te1 ,te2)
         ('(Integer Integer)
          (values `(has-type (< ,ee1 ,ee2) Boolean) 'Boolean))
         ((or '(Integer Double) '(Double Integer) '(Double Double))
          (values `(has-type (<f ,(if (equal? te1 'Integer) `(has-type (double ,ee1) Double) ee1) ,(if (equal? te2 'Integer) `(has-type (double ,ee2) Double) ee2)) Boolean) 'Boolean))
         (_
          (err 'two\ Integers\ or\ Doubles))))
      (`(> ,e1 ,e2)
       (define-values (ee1 te1) (recur e1))
       (define-values (ee2 te2) (recur e2))
       (match `(,te1 ,te2)
         ('(Integer Integer)
          (values `(has-type (> ,ee1 ,ee2) Boolean) 'Boolean))
         ((or '(Integer Double) '(Double Integer) '(Double Double))
          (values `(has-type (>f ,(if (equal? te1 'Integer) `(has-type (double ,ee1) Double) ee1) ,(if (equal? te2 'Integer) `(has-type (double ,ee2) Double) ee2)) Boolean) 'Boolean))
         (_
          (err 'two\ Integers\ or\ Doubles))))
      (`(<= ,e1 ,e2)
       (define-values (ee1 te1) (recur e1))
       (define-values (ee2 te2) (recur e2))
       (match `(,te1 ,te2)
         ('(Integer Integer)
          (values `(has-type (<= ,ee1 ,ee2) Boolean) 'Boolean))
         ((or '(Integer Double) '(Double Integer) '(Double Double))
          (values `(has-type (<=f ,(if (equal? te1 'Integer) `(has-type (double ,ee1) Double) ee1) ,(if (equal? te2 'Integer) `(has-type (double ,ee2) Double) ee2)) Boolean) 'Boolean))
         (_
          (err 'two\ Integers\ or\ Doubles))))
      (`(>= ,e1 ,e2)
       (define-values (ee1 te1) (recur e1))
       (define-values (ee2 te2) (recur e2))
       (match `(,te1 ,te2)
         ('(Integer Integer)
          (values `(has-type (>= ,ee1 ,ee2) Boolean) 'Boolean))
         ((or '(Integer Double) '(Double Integer) '(Double Double))
          (values `(has-type (>=f ,(if (equal? te1 'Integer) `(has-type (double ,ee1) Double) ee1) ,(if (equal? te2 'Integer) `(has-type (double ,ee2) Double) ee2)) Boolean) 'Boolean))
         (_
          (err 'two\ Integers\ or\ Doubles))))
      [`(if ,cnd ,thn ,els)
       (define-values (ec tc) (recur cnd))
       (if (eq? tc 'Boolean)
           (let-values (((e1 t1) (recur thn)) ((e2 t2) (recur els)))
             (if (equal? t1 t2)
                 (values `(has-type (if ,ec ,e1 ,e2) ,t1) t1)
                 (err 'type\ of\ two\ clauses\ to\ be\ the\ same)))
           (err 'Boolean))]
      [`(not ,e)
       (define-values (ee te) (recur e))
        (match te
          ['Boolean (values `(has-type (not ,ee) Boolean) 'Boolean)]
          [else (err 'Boolean)])]
      [`(lambda: ([,xs : ,Ts] ...) : ,rT ,body)
       (define new-env (append (map cons xs Ts) env))
       (define-values (eb Tb) ((type-check-exp new-env) body))
       (cond ((equal? rT Tb)
              (values `(has-type (lambda: ,(for/list ((a xs) (t Ts)) (cons a (list ': t))) : ,rT ,eb) (,@Ts -> ,rT)) `(,@Ts -> ,rT)))
             (else
              (error "mismatch in return type" Tb rT)))]
      [(or `(app ,op ,as ...) `(,op ,as ...))
       (define-values (eop top) (recur op))
       (match top
         (`(,td ... -> ,tr)
          (if (not (eq? (length td) (length as)))
              (error "wrong number of arguments in ~a" e)
              (for/list ((a as) (t td))
                (let-values (((ea ta) (recur a)))
                  (if (not (equal? ta t))
                      (error "Type mismatch in ~a" e)
                      (void)))))
          (define-values (eas tas) (for/lists (eas tas) ((a as)) (recur a)))
          (values `(has-type (app ,eop ,@eas) ,tr) tr)))])))

(define (init-env p)
  (define env '())
  (begin
    (match p
      (`(program ,info ,ds ... ,body)
       (for/list ((d ds))
         (match d
           (`(define (,f [,as : ,ts] ...) : ,rt ,body)
              (set! env (cons (cons f (append ts `(-> ,rt))) env)))))))
    env))

(define (typecheck-d d ienv)
  (match d
    (`(define (,f [,as : ,ts] ...) : ,rt ,body)
     (let ((env (append (for/list ((a as) (t ts)) (cons a t)) ienv)))
       (let-values (((eb tb) ((type-check-exp env) body)))
         (if (equal? tb rt)
             `(define (,f ,@(for/list ((a as) (t ts)) (cons a (list ': t)))) : ,rt ,eb)
             (error 'Type\ Checker "type mismatch\n expected: ~a \n given: ~a in: ~a" rt tb f)))))))

(define (typecheck p)
  (let ((ienv (init-env p)))
    (match p
      [`(program ,info ,ds ... ,body)
        (define-values (eb tb) ((type-check-exp ienv) body))
        `(program ,(cons (cons 'type tb) info) ,@(map (lambda (d) (typecheck-d d ienv)) ds) ,eb)])))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; HW Passes
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define keywords '(read - + -f +f let and or not >= <= > < >=f <=f >f <f eq? feq? double int if vector vector-ref vector-set! void lambda:))
(define caller-saved '((reg rcx) (reg rdx) (reg rsi) (reg rdi) (reg r8) (reg r9) (reg r10) (reg xmm2) (reg xmm3) (reg xmm4) (reg xmm5) (reg xmm6) (reg xmm7)))
(define regs '(rcx rdx rsi rdi r8 r9 r10 rbx r12 r13 r14))
(define xmms '(xmm2 xmm3 xmm4 xmm5 xmm6 xmm7))
(define ppregs '(rdi rsi rdx rcx r8 r9))
(define fppregs '(xmm2 xmm3 xmm4 xmm5 xmm6 xmm7))
(define sizeint 8)

(define (tag-for-ty ty)
  (match ty
    ('Integer 1)
    ('Boolean 4)
    ('Vector 2)
    (`(Vector ,a ...) 2)
    (`(Vectorof ,t) 2)
    ('Void 5)
    ('Procedure 3)
    ('Double 6)  ; actually not implemented
    (`(,ta ... -> ,rt) 3)))

;; shrink

(define fppool '((0.0 . fpconst0)))

(define (shrink-exp exp)
  (match exp
    ((? flonum? f)
     (set! fppool (cons (cons f (gensym 'fpconst)) fppool))
     f)
    (`(has-type ,e ,t)
     `(has-type ,(shrink-exp e) ,t))
    (`(project ,e ,ty)
     (define tmpid (gensym 'tmp))
     `(let ((,tmpid ,(shrink-exp e)))
        (has-type (if (has-type (eq? (has-type (tag-of-any (has-type ,tmpid Any)) Integer) (has-type ,(tag-for-ty ty) Integer)) Boolean)
            (value-of-any ,tmpid ,ty)
            (has-type (exit) Void)) ,ty)))
    (`(boolean? ,e)
     (define tmp (gensym 'tmp))
     `(let ((,tmp ,(shrink-exp e))) (eq? (tag-of-any ,tmp) ,(tag-for-ty 'Boolean))))
    (`(integer? ,e)
     (define tmp (gensym 'tmp))
     `(let ((,tmp ,(shrink-exp e))) (eq? (tag-of-any ,tmp) ,(tag-for-ty 'Integer))))
    (`(vector? ,e)
     (define tmp (gensym 'tmp))
     `(let ((,tmp ,(shrink-exp e))) (eq? (tag-of-any ,tmp) ,(tag-for-ty 'Vector))))
    (`(procedure? ,e)
     (define tmp (gensym 'tmp))
     `(let ((,tmp ,(shrink-exp e))) (eq? (tag-of-any ,tmp) ,(tag-for-ty 'Procedure))))
    (`(void? ,e)
     (define tmp (gensym 'tmp))
     `(let ((,tmp ,(shrink-exp e))) (eq? (tag-of-any ,tmp) ,(tag-for-ty 'Void))))        
    (`(- ,e1 ,e2)
     `(+ ,(shrink-exp e1) (has-type (- ,(shrink-exp e2)) Integer)))
    (`(-f ,e1 ,e2)
     `(+f ,(shrink-exp e1) (has-type (-f ,(shrink-exp e2)) Double)))
    (`(and ,e1 ,e2)
     `(if ,(shrink-exp e1) (has-type (if ,(shrink-exp e2) (has-type #t Boolean) (has-type #f Boolean)) Boolean) (has-type #f Boolean)))
    (`(or ,e1 ,e2)
     `(if ,(shrink-exp e1) (has-type #t Boolean) (has-type (if ,(shrink-exp e2) (has-type #t Boolean) (has-type #f Boolean)) Boolean) (has-type #f Boolean)))
    (`(<= ,e1 ,e2)
     `(not (has-type (< ,(shrink-exp e2) ,(shrink-exp e1)) Boolean)))
    (`(<=f ,e1 ,e2)
     `(not (has-type (<f ,(shrink-exp e2) ,(shrink-exp e1)) Boolean)))
    (`(> ,e1 ,e2)
     `(< ,(shrink-exp e2) ,(shrink-exp e1)))
    (`(>f ,e1 ,e2)
     `(<f ,(shrink-exp e2) ,(shrink-exp e1)))
    (`(>= ,e1 ,e2)
     `(not (has-type (< ,(shrink-exp e1) ,(shrink-exp e2)) Boolean)))
    (`(>=f ,e1 ,e2)
     `(not (has-type (<f ,(shrink-exp e1) ,(shrink-exp e2)) Boolean)))
    (`(if ,cnd ,thn ,els)
     `(if ,(shrink-exp cnd) ,(shrink-exp thn) ,(shrink-exp els)))
    (`(let ((,x ,e)) ,body)
     `(let ((,x ,(shrink-exp e))) ,(shrink-exp body)))
    (`(lambda: (,a ...) : ,rt ,body)
     `(lambda: (,@a) : ,rt ,(shrink-exp body)))
    (`(,op ,args ...)
     `(,(shrink-exp op) ,@(for/list ((a args)) (shrink-exp a))))
    (_ exp)))

(define (shrink p)
  (match p
    (`(program ,info ,ds ... ,exp)
     (define newds
       (for/list ((d ds))
           (match d
             (`(define (,f ,a ...) : ,rt ,body)
              `(define (,f ,@a) : ,rt () ,(shrink-exp body))))))
     (define newmain `(define (main) : Integer () ,(shrink-exp exp)))
     `(program
       ,(cons (cons 'fppool fppool) info)
       ,@newds
       ,newmain))))
             

;; uniquify : R -> R

(define (uniquify-exp alist)
  (lambda (e)
    (match e
      (`(has-type ,e ,t)
       `(has-type ,((uniquify-exp alist) e) ,t))
      ('(void) '(void))
      ((? symbol?)
       (if (dict-has-key? alist e)           
           (dict-ref alist e)
           e))
      ((? integer?) e)
      ((? boolean?) e)
      ((? flonum?) e)
      (`(let ([,x ,e]) ,body)
       (let ((sym (gensym)))
         `(let ([,sym ,((uniquify-exp alist) e)]) ,((uniquify-exp (cons (cons x sym) alist)) body))))
      (`(if ,cnd ,thn ,els)
       `(if ,((uniquify-exp alist) cnd) ,((uniquify-exp alist) thn) ,((uniquify-exp alist) els)))
      (`(lambda: ([,xs : ,ts] ...) : ,rt ,body)
       (let ((newlist (append (map (lambda (x) (cons x (gensym))) xs) alist)))
         `(lambda: (,@(for/list ((x xs) (t ts)) (cons (dict-ref newlist x) (list ': t)))) : ,rt ,((uniquify-exp newlist) body))))
      (`(,op ,es ...)
       `(,((uniquify-exp alist) op) ,@(for/list ([e^ es]) ((uniquify-exp alist) e^)))))))

(define (init-als p)
  (define als '())
  (begin
    (match p
      (`(program ,info ,ds ...)
       (for/list ((d ds))
         (match d
           (`(define (,f [,as : ,ts] ...) : ,rt () ,body)
              (set! als (cons (cons f (if (eq? f 'main) f (gensym f))) als)))))))
    als))

(define (uniquify p)
  (let ((ials (init-als p)))
    (match p
      [`(program ,info ,ds ...)
       `(program
         ,info
         ,@(for/list ((d ds))
         (match d
           (`(define (,f [,as : ,ts] ...) : ,rt () ,body)
            (let ((als (append (for/list ((a as)) (cons a (gensym a))) ials)))
              `(define (,(dict-ref ials f) ,@(for/list ((a as) (t ts)) (cons (dict-ref als a) (list ': t)))) : ,rt () ,((uniquify-exp als) body)))))))])))

;; reveal-functions : R -> R
(define (rf-exp e fls)
  (match e
    (`(has-type ,exp ,t)
     `(has-type ,(rf-exp exp fls) ,t))
    ('(void) '(void))
    ((? symbol?)
     (if (member e fls)
         `(fun-ref ,e)
         e))
    ((? integer?) e)
    ((? boolean?) e)
    ((? flonum?) e)
    (`(let ([,x ,e]) ,body)
     `(let ([,x ,(rf-exp e fls)]) ,(rf-exp body fls)))
    (`(if ,cnd ,thn ,els)
     `(if ,(rf-exp cnd fls) ,(rf-exp thn fls) ,(rf-exp els fls)))
    (`(lambda: (,a ...) : ,rt ,body)
     `(lambda: (,@a) : ,rt ,(rf-exp body fls)))
    (`(,op ,es ...)
     `(,(rf-exp op fls) ,@(for/list ((e^ es)) (rf-exp e^ fls))))))
     
(define (init-fls ds)
  (for/list ((d ds))
    (match d
      (`(define (,f [,as : ,ts] ...) : ,rt () ,body) f))))

(define (reveal-functions p)
    (match p
      [`(program ,info ,ds ...)
       (define fls (init-fls ds))
       `(program
         ,info
         ,@(for/list ((d ds))
             (match d
             (`(define (,f ,a ...) : ,rt () ,body)
              `(define (,f ,@a) : ,rt () ,(rf-exp body fls))))))]))

;; convert-to-clos : R -> R

(define newdefs '())

(define (free-vars e env)
  (match e
    (`(has-type ,exp ,t)
     (if (symbol? exp)
         (if (member exp env)
             (set)
             (set e))
         (free-vars exp env)))
    ('(void) (set))
    ((? integer?) (set))
    ((? boolean?) (set))
    ((? flonum?) (set))
    ((? symbol?) (set))
    (`(let ([,x ,exp]) ,body)
     (set-union (free-vars exp env) (free-vars body (cons x env))))
    (`(if ,cnd ,thn ,els)
     (set-union (free-vars cnd env) (set-union (free-vars thn env) (free-vars els env))))
    (`(lambda: ([,xs : ,ts] ...) : ,rt ,body)
     (free-vars body (append xs env)))
    (`(,op ,es ...)
     (set-union (free-vars op env) (foldr (lambda (elem res) (set-union (free-vars elem env) res)) (set) es)))))

(define (make-lets-convt vars tls body cid rt ind)
  (if (null? vars) `(has-type ,body ,rt)
  `(has-type (let ((,(car vars) (has-type (vector-ref ,cid ,ind) ,(car tls))))
     ,(make-lets-convt (cdr vars) (cdr tls) body cid rt (add1 ind))) ,rt)))

(define (convert-exp e)
  (match e
    (`(has-type (fun-ref ,f) ,t)
     `(has-type (vector (has-type (fun-ref ,f) ,t)) (Vector ,t)))
    (`(has-type ,exp ,t)
     `(has-type ,(convert-exp exp) ,t))
    (`(inject ,exp ,t)
     `(inject ,(convert-exp exp) ,t))
    (`(project ,exp ,t)
     `(project ,(convert-exp exp) ,t))
    ('(void) '(void))
    ((? symbol?) e)
    ((? integer?) e)
    ((? boolean?) e)
    ((? flonum?) e)
    (`(let ((,x ,exp)) ,body)
     `(let ((,x ,(convert-exp exp))) ,(convert-exp body)))
    (`(if ,cnd ,thn ,els)
     `(if ,(convert-exp cnd) ,(convert-exp thn) ,(convert-exp els)))
    (`(lambda: ([,xs : ,ts] ...) : ,rt ,body)
     (define fid (gensym 'lam))
     (define free (set->list (free-vars e keywords)))
     (define vls (for/list ((e free)) (match e (`(has-type ,v ,t) v))))
     (define tls (for/list ((e free)) (match e (`(has-type ,v ,t) t))))
     (define cid (gensym 'clos))
     (define newdef
       `(define (,fid (,cid : _) ,@(for/list ((a xs) (t ts)) (cons a (list ': t)))) : ,rt ()
          ,(make-lets-convt vls tls (convert-exp body) cid rt 1)))
     (set! newdefs (cons newdef newdefs))
     `(has-type (vector (has-type (fun-ref ,fid) (,@(cons '_ ts) -> ,rt)) ,@free) (Vector (,@(cons '_ ts) -> ,rt) ,@tls)))
    (`(app ,f ,args ...)
     (define id (gensym 'v))
     (define ftype (match f (`(has-type ,e ,t) t)))
     `(let ((,id ,(convert-exp f)))
        (app (has-type (vector-ref ,id 0) ,ftype) (has-type ,id ,ftype) ,@(for/list ((arg args)) (convert-exp arg)))))
    (`(,op ,es ...)
     `(,op ,@(for/list ((e es)) (convert-exp e))))))
     
(define (c2c-d d)
  (match d
    (`(define (,f [,as : ,ts] ...) : ,rt ,info ,body)
     `(define
        (,f
         ,@(if (eq? f 'main) '() (for/list ((a (cons (gensym 'clos) as)) (t (cons '_ ts))) (cons a (list ': t)))))
        : ,rt
        ,info
        ,(convert-exp body)))))

(define (convert-to-clos p)
  (match p
    (`(program ,info ,ds ...)
     (define new-ds (for/list ((d ds)) (c2c-d d)))
     (set! new-ds (append newdefs new-ds))
     `(program ,info ,@new-ds))))
                
;; limit-functions : R -> R

(define maxargs 6)

(define (lf-exp e table)
  (match e
    (`(has-type ,e ,t)
     `(has-type ,(lf-exp e table) ,t))
    ('(void) e)
    ((? symbol?) (if (dict-has-key? table e) (dict-ref table e) e))
    ((? integer?) e)
    ((? boolean?) e)
    ((? flonum?) e)
    (`(let ([,x ,e]) ,body)
     `(let ([,x ,(lf-exp e table)]) ,(lf-exp body table)))
    (`(if ,cnd ,thn ,els)
     `(if ,(lf-exp cnd table) ,(lf-exp thn table) ,(lf-exp els table)))
    (`(,op ,es ...)
     (if (member op keywords)
         `(,op ,@(for/list ((e^ es)) (lf-exp e^ table)))
         (if (> (length es) maxargs)
             (let-values (((a1 a2 a3 a4 a5)
                           (values
                            (car es)
                            (cadr es)
                            (caddr es)
                            (cadddr es)
                            (car (cddddr es)))))
               `(,(lf-exp op table)
                 ,@(for/list ((a (list a1 a2 a3 a4 a5))) (lf-exp a table))
                 (has-type ,(cons 'vector (cdr (cddddr es))) (Vector ,@(for/list ((e (cdr (cddddr es)))) (match e (`(has-type ,exp ,t) t)))))))
             `(,(lf-exp op table) ,@(for/list ((e^ es)) (lf-exp e^ table))))))))

(define (limit-t t)
  (match t
    (`(,at ... -> ,rt)
     (let ((at (map limit-t at)) (rt (limit-t rt)))
       (if (> (length at) 6)
           (let-values (((ea va) (split-at at (sub1 maxargs))))
             `(,@ea (Vector ,@va) -> ,rt))
           t)))
    (`(Vector ,ts ...)
     (`(Vector ,@(for/list ((t ts)) (limit-t t)))))
    (_ t)))

(define (limit-functions p)
  (match p
    [`(program ,info ,ds ...)
     `(program
       ,info
       ,@(for/list ((d ds))
           (match d
             (`(define (,f [,as : ,ts] ...) : ,rt () ,body)
              (let ((ts (map limit-t ts)) (rt (limit-t rt)))
                (if (> (length as) maxargs)
                    (let-values (((ea va) (split-at as (sub1 maxargs)))
                                 ((et vt) (split-at ts (sub1 maxargs))))
                      (let* ((vname (gensym 'argv))
                             (as^ `(,@ea ,vname))
                             (ts^ `(,@et ,(cons 'Vector vt)))
                             (table (let ((i -1)) (for/list ((a va)) (set! i (add1 i)) (cons a `(vector-ref ,vname ,i))))))
                        `(define (,f ,@(for/list ((a as^) (t ts^)) (cons a (list ': t)))) : ,rt () ,(lf-exp body table))))
                    `(define (,f ,@(for/list ((a as) (t ts)) (cons a (list ': t)))) : ,rt () ,(lf-exp body '()))))))))]))

;; remove-complex-opera* : R -> R

(define (is-complex-opera* e)
  (match e
    ('(Vectorof Any) #f)
    (`(Vector Any ...) #f)
    (`(Any ... -> Any) #f)
    (else (list? e))))

(define (extract-e htf)
  (match htf
    (`(has-type ,e ,t) e)
    (else htf)))

(define (gen-ls-and-body exp)
  (if (null? exp)
      (values '() '())
      (let-values (((ls body) (gen-ls-and-body (cdr exp))))
        (if (is-complex-opera* (extract-e (car exp)))
            (let ((sym (gensym)))
              (values
               (cons (cons sym (rco (car exp) #f)) ls)
               (match (car exp)
                 (`(has-type ,e ,t) (cons `(has-type ,sym ,t) body))
                 (else (cons sym body)))))
            (values ls (cons (car exp) body))))))

(define (my-make-lets ls body t)
  (match ls
    ('() (if t `(has-type ,body ,t) body))
    (`((,v . ,e) . ,rest) `(let ((,v ,e)) ,(my-make-lets rest body t)))))

(define (rco exp te)
  (match exp
    (`(has-type ,e ,t)
     `(has-type ,(rco e t) ,t))
    ('(void) '(void))
    ((? symbol?) exp)
    ((? integer?) exp)
    ((? boolean?) exp)
    ((? flonum?) exp)
    (`(let ([,x ,e]) ,body)
     `(let ([,x ,(rco e te)]) ,(rco body te)))
    (`(if ,cnd ,thn ,els)
     `(if ,(rco cnd te) ,(rco thn te) ,(rco els te)))
    (`(,op ...)
     (let-values (((ls body) (gen-ls-and-body exp)))
       (if (null? ls) (my-make-lets ls body #f) (my-make-lets ls body te))))))

(define (remove-complex-opera* p)
    (match p
      [`(program ,info ,ds ...)
       `(program
         ,info
         ,@(for/list ((d ds))
             (match d
             (`(define (,f ,a ...) : ,rt () ,body)
              `(define (,f ,@a) : ,rt () ,(rco body #f))))))]))


;; expose-allocation : R -> R

(define locals '())
(define (expose-allocation-exp exp)
  (define (make-init vname els n)
    (if (null? els)
        vname
        (let ((sym (string->symbol (symbol->string (gensym 'initret)))))
          (begin
            (set! locals (cons (cons sym 'Void) locals))
            `(let ((,sym (vector-set! ,vname ,n ,(expose-allocation-exp (car els))))) ,(make-init vname (cdr els) (add1 n)))))))
  (match exp
    (`(has-type (vector ,e0 ...) (Vector ,t0 ...))
     (let ((sym (string->symbol (symbol->string (gensym 'collectret))))
           (vname (string->symbol (symbol->string (gensym 'alloc))))
           (mem (string->symbol (symbol->string (gensym 'mem))))
           (len (length e0))
           (bytes (* 8 (+ (length e0) 1))))
       (begin
         (set! locals (cons (cons sym 'Void) locals))
         (set! locals (cons (cons vname (cons 'Vector t0)) locals))
         (set! locals (cons (cons mem 'Integer) locals))
         `(let ((,sym
                 (if
                  (let ((,mem (+ (global-value free_ptr) ,bytes)))
                    (< ,mem (global-value fromspace_end)))
                  (void)
                  (collect ,bytes))))
            (let ((,vname (allocate ,len ,(cons 'Vector t0))))
              ,(make-init vname e0 0))))))
    (`(let ((,x ,rhs)) ,body)
     (match rhs
       (`(has-type ,e ,t)
        (begin
          (set! locals (cons (cons x t) locals))
          `(let ((,x ,(expose-allocation-exp rhs))) ,(expose-allocation-exp body))))))
    (`(has-type ,e ,t)
     (expose-allocation-exp e))
    ('(void) '(void))
    ((? symbol?) exp)
    ((? integer?) exp)
    ((? boolean?) exp)
    ((? flonum?) exp)
    (`(if ,cnd ,thn ,els)
     `(if ,(expose-allocation-exp cnd) ,(expose-allocation-exp thn) ,(expose-allocation-exp els)))
    (`(,op ,es ...)
       `(,(expose-allocation-exp op) ,@(for/list ([e^ es]) (expose-allocation-exp e^))))))

(define (ea-init-env p)
  (define env '())
  (begin
    (match p
      (`(program ,info ,ds ...)
       (for/list ((d ds))
         (match d
           (`(define (,f [,as : ,ts] ...) : ,rt () ,body)
              (set! env (cons (cons f (append ts `(-> ,rt))) env)))))))
    env))

(define (expose-allocation p)
  (match p
    (`(program ,info ,ds ...)
     (define ienv (ea-init-env p))
     `(program
       ,info
       ,@(for/list ((d ds))
           (match d
             (`(define (,f [,as : ,ts] ...) : ,rt () ,body)
              (define env (append (for/list ((a as) (t ts)) (cons a t)) ienv))
              (set! locals '())
              (define res (expose-allocation-exp body))
               `(define
                  (,f ,@(for/list ((a as) (t ts)) (cons a (list ': t)))) : ,rt
                  ((locals . ,(append (for/list ((a as) (t ts)) (cons a t)) locals)))
                  ,res))))))))

;; explicate-control : R -> C
(define (ec-d d) 
  (define startlbl
    (match d
      (`(define (,f ,a ...) : ,rt ,info ,body)
       (string->symbol (format "~astart" (symbol->string f))))))
  (define conclbl
    (match d
      (`(define (,f ,a ...) : ,rt ,info ,body)
       (string->symbol (format "~aconclusion" (symbol->string f))))))
  (define (add-arrow! v1 v2 graph)
    (hash-update! graph v1 (lambda (s) (set-add s v2)) (set)))
  (define blks (make-hash `((,startlbl . ()))))
  (define cfg (make-hash `((,startlbl . ,(set)))))
  (define curblk startlbl)
  (define tbs (mutable-set))
  (define tmp '())

  (define (ectrl exp)
    (match exp
      (`(if ,cnd ,thn ,els)
       (let ((b1 (gensym 'block)))
         (let ((b2 (gensym 'block)))
           (begin
             (ectrl cnd)
             (for/set ((tb tbs))
               (match (mcar (hash-ref blks tb))
                 (`(return ,e)
                  (begin
                    (match e
                      ((or `(eq? ,a1 ,a2) `(< ,a1 ,a2) `(feq? ,a1 ,a2) `(<f ,a1 ,a2))
                       (set-mcar! (hash-ref blks tb) `(if ,e (goto ,b1) (goto ,b2))))
                      (`(not ,a)
                       (set-mcar! (hash-ref blks tb) `(if (eq? ,a #t) (goto ,b2) (goto ,b1))))
                      (_
                       (set-mcar! (hash-ref blks tb) `(if (eq? ,e #f) (goto ,b2) (goto ,b1)))))
                    (add-arrow! tb b1 cfg)
                    (add-arrow! tb b2 cfg)))
                 (`(tailcall ,f ,a ...)
                  (set-mcar! (hash-ref blks tb) `(if (eq? (call ,f ,@a) #f) (goto ,b2) (goto ,b1))))))
             (set! tbs (mutable-set))
             (set! curblk b1)
             (ectrl thn)
             (set! tmp (cons tbs tmp))
             (set! tbs (mutable-set))
             (set! curblk b2)
             (ectrl els)
             (set-union! tbs (car tmp))
             (set! tmp (cdr tmp))
             (values blks cfg)))))
      (`(let ((,x ,e)) ,body)
       (begin
         (ectrl e)
         (if (<= (set-count tbs) 1)
             (begin
               (match (mcar (hash-ref blks (set-first tbs)))
                 (`(return ,r)
                  (set-mcar! (hash-ref blks (set-first tbs)) `(assign ,x ,r)))
                 (`(tailcall ,f ,a ...)
                  (set-mcar! (hash-ref blks (set-first tbs)) `(assign ,x (call ,f ,@a)))))
               (set! tbs (mutable-set))
               (ectrl body))
             (let ((nb (gensym 'block)))
               (begin
                 (for/set ((tb tbs))
                   (match (mcar (hash-ref blks tb))
                     (`(return ,r)
                      (begin
                        (set-mcar! (hash-ref blks tb) `(assign ,x ,r))
                        (hash-update! blks tb (lambda (b) (mcons `(goto ,nb) b)) '())
                        (add-arrow! tb nb cfg)))
                     (`(tailcall ,f ,a ...)
                      (set-mcar! (hash-ref blks tb) `(assign ,x (call ,f ,@a)))
                      (hash-update! blks tb (lambda (b) (mcons `(goto ,nb) b)) '())
                      (add-arrow! tb nb cfg))))
                 (set! curblk nb)
                 (set! tbs (mutable-set))
                 (ectrl body))))
         (values blks cfg)))
      (`(app ,f ,a ...)
       (hash-update! blks curblk (lambda (b) (mcons `(tailcall ,f ,@a) b)) '())
       (set-add! tbs curblk)
       (values blks cfg))
      (_
       (hash-update! blks curblk (lambda (b) (mcons `(return ,exp) b)) '())
       (set-add! tbs curblk)
       (values blks cfg))))
  
  (define (patch blks cfg)
    (hash-for-each
     blks
     (lambda (b e)
       (begin
         (hash-set! blks b (car (formate (hash-ref blks b) '())))
         (if (not (hash-has-key? cfg b)) (hash-set! cfg b (set)) (void))))))


  (define (formate e acc)
    (if (null? e) acc
        (match (mcar e)
          ((or `(if ,r ...) `(return ,r ...) `(goto ,r ...) `(tailcall ,r ...))
           (formate (mcdr e) `(,(mcar e))))
          (`(assign ,v ...)
           (formate (mcdr e) `(,(cons 'seq (cons (mcar e) acc))))))))

  (match d
    (`(define (,f ,a ...) : ,rt ,info ,body)
     (begin
       (ectrl body)
       (patch blks cfg)
       `(define (,f ,@a) : ,rt ,(cons (cons 'conclbl conclbl) (cons (cons 'startlbl startlbl) (cons (cons 'cfg cfg) info))) ,(hash->list blks))))))

(define (explicate-control p)
  (match p
    (`(program ,info ,ds ...)
     `(program
       ,info
       ,@(for/list ((d ds)) (ec-d d))))))

;; uncover-locals : C0 -> C0
;; done in expose-allocation

(define (uncover-locals p) p)

;; select-instructions : C0 -> pseudo-x86

(define new-anys '())
(define flist '())

(define (gen-ptr-mask typels res shift)
  (if (null? typels) res
  (match (car typels)
    (`(Vector ,type ...)
     (gen-ptr-mask (cdr typels) (+ res (expt 2 shift)) (add1 shift)))
    (`(,td ... -> ,tr)
     (gen-ptr-mask (cdr typels) (+ res (expt 2 shift)) (add1 shift)))
    ('Any
     (gen-ptr-mask (cdr typels) (+ res (expt 2 shift)) (add1 shift)))
    (else
     (gen-ptr-mask (cdr typels) res (add1 shift))))))  

(define (process-arg a)
  (match a
    (#t `(int ,1))
    (#f `(int ,0))
    ((? integer? n) `(int ,n))
    ((? flonum? n) `(flo ,n))
    ((? symbol? n) `(var ,n))
    (`(global-value ,v) a)))

(define (process-assign var exp)
  (match exp
    ('(void) `((movq (int 0) (var ,var))))
    (`(global-value ,v)
     `((movq ,exp (var ,var))))
    (`(inject ,e ,T)
     (match T
       ((or 'Integer 'Boolean)
        `((movq ,(process-arg e) (var ,var))
          (salq (int 3) (var ,var))
          (orq (int ,(tag-for-ty T)) (var ,var))))
       (else
        `((movq ,(process-arg e) (var ,var))
          (orq (int ,(tag-for-ty T)) (var ,var))))))
    (`(tag-of-any ,e)
     `((movq ,(process-arg e) (var ,var))
       (andq (int 7) (var ,var))))
    (`(value-of-any ,e ,T)
     (match T
       ((or 'Integer 'Boolean)
        `((movq ,(process-arg e) (var ,var))
          (sarq (int 3) (var ,var))))
       (else
        `((movq (int 7) (var ,var))
          (notq (var ,var))
          (andq ,(process-arg e) (var ,var))))))
    ('(exit)
     `((callq exit)))
    (#t `((movq (int 1) (var ,var))))
    (#f `((movq (int 0) (var ,var))))
    (`(int ,arg)
     (match arg
       ((? flonum? f)
        (define lbl (dict-ref fppool f))
        `((cvtsd2si (global-value ,lbl) (reg rax))
          (movsd (reg rax) (var ,var))))
       ((? symbol?)
        `((cvtsd2si (var ,arg) (reg rax))
          (movsd (reg rax) (var ,var))))))
    (`(double ,arg)
     (match arg
       ((? fixnum? n)
        `((movq (int ,n) (reg rax))
          (cvtsi2sd (reg rax) (reg xmm0))
          (movsd (reg xmm0) (var ,var))))
       ((? symbol?)
        `((cvtsi2sd (var ,arg) (reg xmm0))
          (movsd (reg xmm0) (var ,var))))))
    ((? flonum? f)
     (define lbl (dict-ref fppool f)) 
     `((movsd (global-value ,lbl) (var ,var))))
    ((? integer? n)
     `((movq (int ,n) (var ,var))))
    ((? symbol?)
     (if (eq? exp var)
         '()
         `((movq (var ,exp) (var ,var)))))
    ('(read)
     `((callq read_int)
       (movq (reg rax) (var ,var))))
    (`(-f ,arg)
     (match arg
       ((? flonum? f)
        (define lbl (dict-ref fppool f))
        `((movsd (global-value fpconst0) (reg xmm0))
          (subsd (global-value ,lbl) (reg xmm0))
          (movsd (reg xmm0) (var ,var))))
       ((? symbol?)
        `((movsd (global-value fpconst0) (reg xmm0))
          (subsd (var ,arg) (reg xmm0))
          (movsd (reg xmm0) (var ,var)))))) 
    (`(- ,arg)
     (if (eq? arg var)
         `((negq (var ,var)))
         (match arg
           ((? integer?)
            `((movq (int ,(- arg)) (var ,var))))
           ((? symbol?)
            `((movq (var ,arg) (var ,var))
              (negq (var ,var)))))))
    (`(+ ,(? symbol? arg1) ,(? symbol? arg2))
     `((movq (var ,arg1) (var ,var))
       (addq (var ,arg2) (var ,var))))
    (`(+f ,(? symbol? arg1) ,(? symbol? arg2))
     `((movsd (var ,arg1) (var ,var))
       (addsd (var ,arg2) (var ,var))))
    (`(+ ,args ...)
     (match args
       ((list-no-order (? number? n) arg)
        (if (number? arg)
            `((movq (int ,(+ n arg)) (var ,var)))
            (if (eq? arg var)
                `((addq (int ,n) (var ,var)))
                `((movq ,(process-arg arg) (var ,var))
                  (addq (int ,n) (var ,var))))))
       ((list-no-order (? (lambda (x) (eq? x var)) arg1) arg2)
        (if (eq? arg2 var)
            `((addq (var ,arg1) (var ,arg2)))
            `((addq (var ,arg2) (var ,var)))))))
    (`(+f ,args ...)
     (match args
       ((list-no-order (? flonum? n) arg)
        (define lbl1 (dict-ref fppool n))
        (if (flonum? arg)
            (let ((lbl2 (dict-ref fppool arg)))
              `((movsd (global-value ,lbl2) (var ,var))
                (addsd (global-value ,lbl1) (var ,var))))
            `((movsd ,(process-arg arg) (var ,var))
              (addsd (global-value ,lbl1) (var ,var)))))))
    (`(not ,arg)
     (if (eq? var arg)
         `((xorq (int 1) (var ,var)))
         `((movq ,(process-arg arg) (var ,var))
           (xorq (int 1) (var ,var)))))
    (`(vector-ref ,vec ,n)
     `((movq (var ,vec) (reg r11))
       (movq (deref r11 ,(* 8 (add1 n))) (var ,var))))
    (`(vector-set! ,vec ,n ,arg)
     `((movq (var ,vec) (reg r11))
       (movq ,(process-arg arg) (deref r11 ,(* 8 (add1 n))))
       (movq (int 0) (var ,var))))
    (`(allocate ,len (Vector ,type ...))
     (let* (
           (ptrmask (gen-ptr-mask type 0 0))
           (veclen len)
           (fwding 1)
           (tag (+ (* ptrmask (expt 2 7)) (* veclen 2) fwding)))
     `((movq (global-value free_ptr) (var ,var))
       (addq (int ,(* 8 (add1 len))) (global-value free_ptr))
       (movq (var ,var) (reg r11))
       (movq (int ,tag) (deref r11 0)))))
    (`(collect ,bytes)
     `((movq (reg r15) (reg rdi))
       (movq (int ,bytes) (reg rsi))
       (callq collect)))
    (`(fun-ref ,f)
     `((leaq (fun-ref ,f) (var ,var))))
    (`(call ,f ,as ...)
     (define argtypes
       (if (assoc f flist)
           (car (dict-ref flist f))
           (match (dict-ref locals f)
             (`(,ta ... -> ,rt)
              (cons '_ ta)))))
     (define rtype
       (if (assoc f flist)
           (cdr (dict-ref flist f))
           (match (dict-ref locals f)
             (`(,ta ... -> ,rt)
              rt))))
     (define fpinds (indexes-where argtypes (lambda (t) (eq? t 'Double))))
     (define iinds (indexes-where argtypes (lambda (t) (not (eq? t 'Double)))))
     (define fpl (for/list ((i fpinds)) (list-ref as i)))
     (define il (for/list ((i iinds)) (list-ref as i)))
     `(,@(for/list ((a fpl) (r fppregs))
           (if (flonum? a)
               (let ((lbl (dict-ref fppool a)))
                 `(movsd (global-value ,lbl) (reg ,r)))
               `(movsd ,(process-arg a) (reg ,r))))            
       ,@(for/list ((a il) (r ppregs)) `(movq ,(process-arg a) (reg ,r)))
       (indirect-callq (var ,f))
       (movq ,(if (eq? rtype 'Double) '(reg xmm0) '(reg rax)) (var ,var))))
    (`(,cmp ,a1 ,a2)
     (if (or (eq? cmp 'eq?) (eq? cmp '<))
     `((cmpq ,(process-arg a2) ,(process-arg a1))
       (set ,(if (eq? cmp 'eq?) 'e 'l) (byte-reg al))
       (movzbq (byte-reg al) (reg rax))
       (movq (reg rax) (var ,var)))
     (cond
       ((and (symbol? a1) (symbol? a2))
        `((ucomisd (var ,a2) (var ,a1))
          (set ,(if (eq? cmp 'feq?) 'e 'g) (byte-reg al))
          (movzbq (byte-reg al) (reg rax))
          (movq (reg rax) (var ,var))))
       ((and (flonum? a1) (flonum? a2))
        (let ((lbl1 (dict-ref fppool a1)))
          (let ((lbl2 (dict-ref fppool a2)))
            `((movsd (global-value ,lbl1) (reg xmm0))
              (ucomisd (global-value ,lbl2) (reg xmm0))
              (set ,(if (eq? cmp 'feq?) 'e 'g) (byte-reg al))
              (movzbq (byte-reg al) (reg rax))
              (movq (reg rax) (var ,var))))))
       ((or (and (flonum? a1) (symbol? a2)) (and (symbol? a1) (flonum? a2)))
        (let ((lbl (dict-ref fppool (if (flonum? a1) a1 a2))))
          `((movsd (global-value ,lbl) (reg xmm0))
            (ucomisd (var ,(if (symbol? a2) a2 a1)) (reg xmm0))
            (set ,(if (eq? cmp 'feq?) 'e 'g) (byte-reg al))
            (movzbq (byte-reg al) (reg rax))
            (movq (reg rax) (var ,var))))))))))
              

(define (process-return exp)
  (match exp
    (#t `((movq (int 1) (reg rax))))
    (#f `((movq (int 0) (reg rax))))
    ((? integer? n)
     `((movq (int ,n) (reg rax))))
    ((? symbol?)
     `((movq (var ,exp) (reg rax))))
    (`(inject ,e ,T)
     (match T
       ((or 'Integer 'Boolean)
        `((movq ,(process-arg e) (reg rax))
          (salq (int 3) (reg rax))
          (orq (int ,(tag-for-ty T)) (reg rax))))
       (else
        `((movq ,(process-arg e) (reg rax))
          (orq (int ,(tag-for-ty T)) (reg rax))))))
    (`(tag-of-any ,e)
     `((movq ,(process-arg e) (reg rax))
       (andq (int 7) (reg rax))))
    (`(value-of-any ,e ,T)
     (match T
       ((or 'Integer 'Boolean)
        `((movq ,(process-arg e) (reg rax))
          (sarq (int 3) (reg rax))))
       (else
        `((movq (int 7) (reg rax))
          (notq (reg rax))
          (andq ,(process-arg e) (reg rax))))))
    ('(exit)
     `((callq exit)))
    ('(read)
     `((callq read_int)))
    (`(int ,arg)
     (match arg
       ((? flonum? f)
        (define lbl (dict-ref fppool f))
        `((cvtsd2si (global-value ,lbl) (reg rax))))
       ((? symbol?)
        `((cvtsd2si (var ,arg) (reg rax))))))
    (`(double ,arg)
     (match arg
       ((? fixnum? n)
        `((movq (int ,n) (reg rax))
          (cvtsi2sd (reg rax) (reg xmm0))))
       ((? symbol?)
        `((cvtsi2sd (var ,arg) (reg xmm0))))))
    ((? flonum? f)
     (define lbl (dict-ref fppool f)) 
     `((movsd (global-value ,lbl) (reg xmm0))))
    (`(- ,arg)
     (match arg
       ((? integer?)
        `((movq (int ,(- arg)) (reg rax))))
       ((? symbol?)
        `((movq (var ,arg) (reg rax))
          (negq (reg rax))))))
    (`(-f ,arg)
     (match arg
       ((? flonum? f)
        (define lbl (dict-ref fppool f))
        `((movsd (global-value fpconst0) (reg xmm0))
          (subsd (global-value ,lbl) (reg xmm0))))
       ((? symbol?)
        `((movsd (global-value fpconst0) (reg xmm0))
          (subsd (var ,arg) (reg xmm0))))))
    (`(+ ,(? symbol? arg1) ,(? symbol? arg2))
     `((movq (var ,arg1) (reg rax))
       (addq (var ,arg2) (reg rax))))
    (`(+f ,(? symbol? arg1) ,(? symbol? arg2))
     `((movsd (var ,arg1) (reg xmm0))
       (addsd (var ,arg2) (reg xmm0))))
    (`(+ ,args ...)
     (match args
       ((list-no-order (? number? n) arg)
        (if (number? arg)
            `((movq (int ,(+ n arg)) (reg rax)))
            `((movq (var ,arg) (reg rax))
              (addq (int ,n) (reg rax)))))))
    (`(+f ,args ...)
     (match args
       ((list-no-order (? flonum? n) arg)
        (define lbl1 (dict-ref fppool n))
        (if (flonum? arg)
            (let ((lbl2 (dict-ref fppool arg)))
              `((movsd (global-value ,lbl2) (reg xmm0))
                (addsd (global-value ,lbl1) (reg xmm0))))
            `((movsd ,(process-arg arg) (reg xmm0))
              (addsd (global-value ,lbl1) (reg xmm0)))))))
    (`(not ,arg)
     `((movq ,(process-arg arg) (reg rax))
       (xorq (int 1) (reg rax))))
    (`(vector-ref ,vec ,n)
     `((movq (var ,vec) (reg r11))
       (movq (deref r11 ,(* 8 (add1 n))) (reg rax))))
    (`(vector-set! ,vec ,n ,arg)
     `((movq (var ,vec) (reg r11))
       (movq ,(process-arg arg) (deref r11 ,(* 8 (add1 n))))
       (movq (int 0) (reg rax))))
    (`(allocate ,len (Vector ,type ...))
      (let*
	((ptrmask (gen-ptr-mask type 0 0))
	 (veclen len)
	 (fwding 1)
	 (tag (+ (* ptrmask (expt 2 7)) (* veclen 2) fwding)))
	`((movq (global-value free_ptr) (reg rax))
	 (addq (int ,(* 8 (add1 len))) (global-value free_ptr))
	 (movq (reg rax) (reg r11))
	 (movq (int ,tag) (deref r11 0)))))
    (`(,cmp ,a1 ,a2)
     (if (or (eq? cmp 'eq?) (eq? cmp '<))
     `((cmpq ,(process-arg a2) ,(process-arg a1))
       (set ,(if (eq? cmp 'eq?) 'e 'l) (byte-reg al))
       (movzbq (byte-reg al) (reg rax)))
     (cond
       ((and (symbol? a1) (symbol? a2))
        `((ucomisd (var ,a2) (var ,a1))
          (set ,(if (eq? cmp 'feq?) 'e 'g) (byte-reg al))
          (movzbq (byte-reg al) (reg rax))))
       ((and (flonum? a1) (flonum? a2))
        (let ((lbl1 (dict-ref fppool a1)))
          (let ((lbl2 (dict-ref fppool a2)))
            `((movsd (global-value ,lbl1) (reg xmm0))
              (ucomisd (global-value ,lbl2) (reg xmm0))
              (set ,(if (eq? cmp 'feq?) 'e 'g) (byte-reg al))
              (movzbq (byte-reg al) (reg rax))))))
       ((or (and (flonum? a1) (symbol? a2)) (and (symbol? a1) (flonum? a2)))
        (let ((lbl (dict-ref fppool (if (flonum? a1) a1 a2))))
          `((movsd (global-value ,lbl) (reg xmm0))
            (ucomisd (var ,(if (symbol? a2) a2 a1)) (reg xmm0))
            (set ,(if (eq? cmp 'feq?) 'e 'g) (byte-reg al))
            (movzbq (byte-reg al) (reg rax))))))))
    (`(fun-ref ,f)
     `((leaq (fun-ref ,f) (reg rax))))))

(define (gen-insts e conclbl)
  (match e
    (`(seq ,stmt ,tail)
     (match stmt
       (`(assign ,var ,exp)
        (let ((cur-inst-seq (process-assign var exp)))
          (append cur-inst-seq (gen-insts tail conclbl))))))
    (`(return ,exp)
     (append (process-return exp) `((jmp ,conclbl))))
    (`(goto ,label)
     `((jmp ,label)))
    (`(if (,cmp ,a1 ,a2) (goto ,l1) (goto ,l2))
     (define var1 (gensym))
     (define var2 (gensym))
     (if (or (flonum? a1) (eq? (if (assoc a1 locals) (cdr (assoc a1 locals)) #f) 'Double))
         (set! locals (cons (cons var1 'Double) locals))
         (void))
     (if (or (flonum? a2) (eq? (if (assoc a2 locals) (cdr (assoc a2 locals)) #f) 'Double))
         (set! locals (cons (cons var2 'Double) locals))
         (void))
     (define assign1 (process-assign var1 a1))
     (define assign2 (process-assign var2 a2))
     
     `(,@assign1
       ,@assign2
       ,@(if (or (flonum? a1) (flonum? a2) (eq? (if (assoc a1 locals) (cdr (assoc a1 locals)) #f) 'Double) (eq? (if (assoc a2 locals) (cdr (assoc a2 locals)) #f) 'Double))
             `((ucomisd (var ,var2) (var ,var1))
               (jmp-if ,(if (eq? cmp 'feq?) 'e 'g) ,l1)
               (jmp ,l2))
             `((cmpq (var ,var2) (var ,var1))
               (jmp-if ,(if (eq? cmp 'eq?) 'e 'l) ,l1)
               (jmp ,l2)))))
    (`(tailcall ,f ,as ...)
     (define argtypes
       (if (assoc f flist)
           (car (dict-ref flist f))
           (match (dict-ref locals f)
             (`(,ta ... -> ,rt)
              (cons '_ ta)))))
     (define rtype
       (if (assoc f flist)
           (cdr (dict-ref flist f))
           (match (dict-ref locals f)
             (`(,ta ... -> ,rt)
              rt))))
     (define fpinds (indexes-where argtypes (lambda (t) (eq? t 'Double))))
     (define iinds (indexes-where argtypes (lambda (t) (not (eq? t 'Double)))))
     (define fpl (for/list ((i fpinds)) (list-ref as i)))
     (define il (for/list ((i iinds)) (list-ref as i)))
     `(,@(for/list ((a fpl) (r fppregs))
           (if (flonum? a)
               (let ((lbl (dict-ref fppool a)))
                 `(movsd (global-value ,lbl) (reg ,r)))
               `(movsd ,(process-arg a) (reg ,r))))
       ,@(for/list ((a il) (r ppregs)) `(movq ,(process-arg a) (reg ,r)))
       (tail-jmp (var ,f))))))
     
(define (si-d d)
  (match d
    (`(define (,f ,a ...) : ,rt ,info ,blks)
     (define conclbl (dict-ref info 'conclbl))
     (define startlbl (dict-ref info 'startlbl))
     (set! new-anys '())
     (define argtypes
       (if (assoc f flist)
           (car (dict-ref flist f))
           (match (dict-ref locals f)
             (`(,ta ... -> ,rt)
              (cons '_ ta)))))
     (define rtype
       (if (assoc f flist)
           (cdr (dict-ref flist f))
           (match (dict-ref locals f)
             (`(,ta ... -> ,rt)
              rt))))
     (define fpinds (indexes-where argtypes (lambda (t) (eq? t 'Double))))
     (define iinds (indexes-where argtypes (lambda (t) (not (eq? t 'Double)))))
     (define fpl (for/list ((i fpinds)) (car (list-ref a i))))
     (define il (for/list ((i iinds)) (car (list-ref a i))))
     (let ((body
            (for/list ((blk blks))
               (match blk
                 (`(,label . ,tail)
                  (if (eq? label startlbl)
                      (let ((init
                             `(,@(for/list ((r fppregs) (fa fpl))
                                   `(movsd (reg ,r) (var ,fa)))
                               ,@(for/list ((r ppregs) (ia il))
                                   `(movq (reg ,r) (var ,ia))))))
                        `(,label . (block . (() . ,(append init (gen-insts tail conclbl))))))
                      `(,label . (block . (() . ,(gen-insts tail conclbl))))))))))
       `(define (,f ,@a) : ,rt ,(cons (cons 'newanys new-anys) info) ,body)))))

(define (select-instructions p)
  (match p
    (`(program ,info ,ds ...)
     (for/list ((d ds))
       (match d
         (`(define (,f [,as : ,ts] ...) : ,rt ,info ,body)
          (set! flist (cons (cons f (cons ts rt)) flist))
          (set! locals (append locals (cdr (assoc 'locals info)))))))     
     `(program
       ,info
       ,@(for/list ((d ds)) (si-d d))))))

;; uncover-live

(define (union-var set arg)
  (match arg
    ((or `(int ,a) `(reg ,a) `(byte-reg ,a) `(global-value ,a) `(fun-ref ,a))
     set)
    (`(deref ,r ,n)
     set)
    (`(var ,v)
     (set-add set v))))

(define (remove-var set arg)
  (match arg
    ((or `(int ,a) `(reg ,a) `(byte-reg ,a) `(global-value ,a) `(fun-ref ,a))
     set)
    (`(deref ,r ,n)
     set)
    (`(var ,v)
     (set-remove set v))))

(define (gen-sets insts-rev lafter)
  (if (null? insts-rev)
      (cons lafter '())
      (let ((lbefore
             (match (car insts-rev)
               ((or `(addq ,a1 ,a2) `(addsd ,a1 ,a2) `(subq ,a1 ,a2) `(subsd ,a1 ,a2) `(salq ,a1 ,a2) `(sarq ,a1 ,a2) `(cmpq ,a1 ,a2) `(xorq ,a1 ,a2) `(orq ,a1 ,a2) `(andq ,a1 ,a2) `(ucomisd ,a1 ,a2))
                (union-var (union-var lafter a1) a2))
               ((or `(movq (reg ,r) ,a2) `(movsd (reg ,r) ,a2) `(cvtsd2si (reg ,r) ,a2) `(cvtsi2sd (reg ,r) ,a2))
                (set-add (remove-var lafter a2) `(reg ,r)))
               ((or `(movq ,a1 ,a2) `(movzbq ,a1 ,a2) `(leaq ,a1 ,a2) `(movsd ,a1 ,a2) `(cvtsd2si ,a1 ,a2) `(cvtsi2sd ,a1 ,a2))
                (union-var (remove-var lafter a2) a1))
               ((or `(negq ,a) `(callq ,a) `(jmp ,a) `(notq ,a) `(jmp-if ,a ...) `(set ,a ...))
                lafter)
               (`(retq)
                lafter)
               (`(pushq ,a)
                (union-var lafter a))               
               ((or `(indirect-callq ,a) `(tail-jmp ,a))
                (union-var
                 (foldr
                  (lambda (elem res) (set-add res elem))
                  (set-remove (set-remove (set-remove (set-remove (set-remove lafter '(reg rax)) '(reg r10)) '(reg r11)) '(reg xmm0)) '(reg xmm1))
                  (map (lambda (r) `(reg ,r)) ppregs))
                 a))
               (`(popq ,a)
                (remove-var lafter a)))))
        (cons lafter (gen-sets (cdr insts-rev) lbefore)))))

(define (ul-d d)
  (define hlafter (make-hash))
  (define hlsets (make-hash))
  (define startlbl
    (match d
      (`(define (,f ,a ...) : ,rt ,info ,blks)
       (dict-ref info 'startlbl))))
  (define (all-gen-sets cfg blks)
    (for (((V Es) cfg) #:final (set-empty? Es))
      (if (set-empty? Es)
          (let ((lsets (reverse (gen-sets (reverse (cdddr (assoc V blks))) (hash-ref hlafter V)))))
            (begin
              (hash-set! hlsets V (cdr lsets))
              (if (not (eq? V startlbl))
                  (begin
                    (let ((lafter (car lsets)))
                      (hash-for-each cfg
                                     (lambda (V^ Es^)
                                       (let ((curedges (hash-ref cfg V^)))
                                         (if (set-member? curedges V)
                                             (begin
                                               (hash-set! cfg V^ (set-remove curedges V))
                                               (hash-set! hlafter V^ (set-union (hash-ref hlafter V^) lafter)))
                                             (void))))))
                    (hash-remove! cfg V)
                    (all-gen-sets cfg blks))
                  (void))))
            (void))))
  
  (match d
    (`(define (,f ,a ...) : ,rt ,info ,blks)
     (let ((cfg (cdr (assoc 'cfg info))))
       (begin
         (set! hlafter (make-hash (hash-map cfg (lambda (k v) (cons k (set))))))
         (set! hlsets (make-hash (hash-map cfg (lambda (k v) (cons k (set))))))
         (all-gen-sets cfg blks)
         `(define (,f ,@a) : ,rt ,(cons (cons 'hlsets hlsets) info) ,blks))))))   

(define (uncover-live p)
  (match p
    (`(program ,info ,ds ...)
     `(program
       ,info
       ,@(for/list ((d ds)) (ul-d d))))))

;; allocate registers (with move biasing)

(define (build-interference p) p) ;; just a placeholder; done in "analyze" below

(define (add-edge v1 v2 graph)
  (hash-update
   (hash-update graph v2 (lambda (s) (set-add s v1)) (set))
   v1
   (lambda (s) (set-add s v2))
   (set)))
(define spilledvecs (mutable-set))
(define (analyze insts lasets locals) ;; generates interference graph and move graph
  (if (null? insts) (values (hash) (hash) (hash))
      (let-values (((igraph mgraph freq) (analyze (cdr insts) (cdr lasets) locals))) ;; freq not used in allocation
        (match (car insts)
          ((or `(movq (var ,s) (var ,d)) `(movsd (var ,s) (var ,d)))
           (values
            (foldr (lambda (v g) (add-edge d v g)) igraph (set->list (set-remove (set-remove (car lasets) d) s)))
            (add-edge s d mgraph)
            (hash-update (hash-update freq d add1 0) s add1 0)))
          ((or `(movq (var ,s) (reg ,r)) `(movsd (var ,s) (reg ,r)) `(cvtsd2si (var ,s) (reg ,r)) `(cvtsi2sd (var ,s) (reg ,r)))
           (values
            (foldr (lambda (v g) (add-edge `(reg ,r) v g)) igraph (set->list (set-remove (set-remove (car lasets) `(reg ,r)) s)))
            mgraph
            (hash-update freq s add1 0)))
          ((or `(cmpq ,a1 (var ,d)) `(ucomisd ,a1 (var ,d)))
           (values
            igraph
            mgraph
            (hash-update (match a1 (`(var ,s) (hash-update freq s add1 0)) (_ freq)) d add1 0)))
          (`(,op ,a1 (var ,d))
           (values
            (foldr (lambda (v g) (add-edge d v g)) igraph (set->list (set-remove (car lasets) d)))
            mgraph
            (hash-update (match a1 (`(var ,s) (hash-update freq s add1 0)) (_ freq)) d add1 0)))
          (`(,op ,a1 ,a2)
           (values
            igraph
            mgraph
            (match a1 (`(var ,s) (hash-update freq s add1 0)) (_ freq))))
          ((or `(indirect-callq ,label) `(callq ,label))
           (for/set ((v (car lasets)))
             (unless (match v (`(reg ,r) #t) (else #f))
             (match (cdr (assoc v locals))
               (`(Vector ,type ...)
                (set-add! spilledvecs v))
               (`(,at ... -> ,rt)
                (set-add! spilledvecs v))
               ('Any
                (set-add! spilledvecs v))
               (else (void)))))
           (values
            (foldr
             (lambda (r g)
               (foldr (lambda (v g^) (add-edge r v g^)) g (set->list (car lasets))))
             igraph
             caller-saved)
            mgraph
            freq))
          ((or `(negq (var ,v) `(popq (var ,v)) `(notq (var ,v))))
           (values
            (foldr (lambda (v^ g) (add-edge v v^ g)) igraph (set->list (set-remove (car lasets) v)))
            mgraph
            (hash-update freq v add1 0)))
          (`(pushq (var ,v))
           (values
            igraph
            mgraph
            (hash-update freq v add1 0)))
          (_ (values igraph mgraph freq))))))

(define (patch-igraph igraph locals) ;; add 0-degree nodes
  (foldr (lambda (t g) (let ((v (car t))) (if (not (hash-has-key? g v)) (hash-set g v (set)) g))) igraph locals))

(define (color-graph igraph mgraph)
  (define (nextnum ls)
    (define (next sorted ans)
      (if (or (null? sorted) (< ans (car sorted)))
          ans
          (if (> ans (car sorted))
              (next (cdr sorted ans))
              (next (cdr sorted) (add1 ans)))))
    (next (sort ls <) 0))
  (define vecnum 10000000)
  (define colortable (make-hash))
  (define confltable (make-hash))
  (define remain '())
  (begin
    (hash-for-each igraph
                   (lambda (V Es)
                     (match V
                       (`(reg ,r)
                        (unless (or (eq? r 'rax) (eq? r 'r11) (eq? r 'r15) (eq? r 'xmm0) (eq? r 'xmm1))
                        (begin
                          (hash-set! colortable `(reg ,r) (index-of regs r))
                          (for/set ((adj (hash-ref igraph `(reg ,r))))
                            (hash-update! confltable adj (lambda (s) (set-add s (if (not (index-of regs r)) (index-of xmms r) (index-of regs r)))) (set))))))
                       (_ (set! remain (cons V remain))))))
    (for/list ((v remain)) (hash-update! confltable v (lambda (s) (if (set? s) s (error 'not-a-set))) (set)))
    (for ((i (range (length remain))))
      (let* ((cur_v (argmax (lambda (v) (set-count (hash-ref confltable v))) remain))
             (cur_num (nextnum (set->list (hash-ref confltable cur_v)))))
        (begin
          (if (hash-has-key? mgraph cur_v)
              (let ((mset (set-subtract (hash-ref mgraph cur_v) (hash-ref igraph cur_v))))
                (if (not (set-empty? mset))
                    (for/set ((adj mset))
                      (if (hash-has-key? colortable adj)
                          (if (not (set-member? (hash-ref confltable cur_v) (hash-ref colortable adj)))
                              (set! cur_num (hash-ref colortable adj))
                              (void))
                          (void)))
                    (void)))
              (void))
          (if (set-member? spilledvecs cur_v)
              (begin (set! cur_num vecnum) (set! vecnum (add1 vecnum)))
              (void))
          (hash-set! colortable cur_v cur_num)
          (for/set ((adj (hash-ref igraph cur_v)))
            (hash-update! confltable adj (lambda (s) (set-add s cur_num)) (set)))
          (set! remain (remove cur_v remain)))))
    colortable))

(define (assign-regs colortable locals2)
  (define offset 0)
  (define voffset 0)
  (begin
    (hash-for-each colortable
                   (lambda (v c)
                     (if (or (not (symbol? v)) (not (fixnum? c))) (void)
                     (if (eq? (if (assoc v locals2) (cdr (assoc v locals2)) (if (assoc v locals) (cdr (assoc v locals)) #f)) 'Double)
                         (if (< c (length xmms))
                             (hash-set! colortable v `(reg ,(list-ref xmms c)))
                             (begin
                               (hash-set! colortable v `(deref rbp ,(- (- offset sizeint) 40)))
                               (set! offset (- offset sizeint))))                         
                         (if (< c (length regs))
                             (hash-set! colortable v `(reg ,(list-ref regs c)))
                             (if (set-member? spilledvecs v)
                                 (begin
                                   (hash-set! colortable v `(deref r15 ,(- voffset sizeint)))
                                   (set! voffset (- voffset sizeint)))
                                 (begin
                                   (hash-set! colortable v `(deref rbp ,(- (- offset sizeint) 40)))
                                   (set! offset (- offset sizeint)))))))))
    (values colortable offset voffset)))

(define (update-insts instls regtable)
  (for/list ((inst instls))
    (for/list ((op* inst))
      (match op*
        (`(var ,v) (hash-ref regtable v))
        (_ op*)))))

(define (combine-blks blks hlsets)
  (if (null? blks) (values '() '())
      (let-values (((insts lasets) (combine-blks (cdr blks) hlsets)))
        (values (append (cdddr (car blks)) insts) (append (hash-ref hlsets (caar blks)) lasets)))))
(define locals2 locals)
(define (ar-d d)
  (match d
    (`(define (,f ,a ...) : ,rt ,info ,blks)
     (let-values (((insts lasets) (combine-blks blks (cdr (assoc 'hlsets info)))))
       (let ((locals (append (cdr (assoc 'newanys info)) (cdr (assoc 'locals info)))))
         (let-values (((igraph mgraph freq) (analyze insts lasets locals)))
           (let ((igraph (patch-igraph igraph locals)))
             (let ((colortable (color-graph igraph mgraph)))
               (let-values (((regtable offset voffset) (assign-regs colortable locals)))
                 `(define (,f ,@a) : ,rt
                    ,(cons (cons 'voffset voffset) (cons (cons 'offset offset) info))
                    ,(for/list ((b blks)) `(,(car b) . (block . (() . ,(update-insts (cdddr b) regtable)))))))))))))))

(define (allocate-registers p)
  (match p
    (`(program ,info ,ds ...)
     `(program
       ,info
       ,@(for/list ((d ds)) (ar-d d))))))

;; patch-instructions : psuedo-x86 -> x86

(define (patch instls offset voffset)
  (define (round-16 n)
    (if (= 0 (remainder n 16))
        n
        (round-16 (sub1 n))))
  (if (null? instls)
      '()
      (let ((inst (car instls)))
        (match inst
          (`(,op (deref ,r1 ,a1) (deref ,r2 ,a2))
           (match op
             ((or 'movsd 'addsd 'subsd 'ucomisd 'cvtsd2si 'cvtsi2sd)
              (cons `(movsd (deref ,r1 ,a1) (reg xmm0))
                    (cons `(,op (reg xmm0) (deref ,r2 ,a2))
                          (patch (cdr instls) offset voffset))))
             (else
              (cons `(movq (deref ,r1 ,a1) (reg rax))
                    (cons `(,op (reg rax) (deref ,r2 ,a2))
                          (patch (cdr instls) offset voffset))))))
          (`(,op (global-value ,gl) (deref ,r2 ,a2))
           (match op
             ((or 'movsd 'addsd 'subsd 'ucomisd 'cvtsd2si 'cvtsi2sd)
              (cons `(movsd (global-value ,gl) (reg xmm0))
                    (cons `(,op (reg xmm0) (deref ,r2 ,a2))
                          (patch (cdr instls) offset voffset))))
             (else
              (cons `(movq (global-value ,gl) (reg rax))
                    (cons `(,op (reg rax) (deref ,r2 ,a2))
                          (patch (cdr instls) offset voffset))))))
          (`(movq (reg ,r) (reg ,r))
           (patch (cdr instls) offset voffset))
          (`(movsd (reg ,r) (reg ,r))
           (patch (cdr instls) offset voffset))
          (`(leaq ,a1 (deref ,r2 ,a2))
           (cons `(leaq ,a1 (reg rax))
                 (cons `(movq (reg rax) (deref ,r2 ,a2))
                       (patch (cdr instls) offset voffset))))
          (`(cmpq (reg ,r) (int ,n))
           (cons `(movq (int ,n) (reg rax))
                 (cons `(cmpq (reg ,r) (reg rax))
                       (patch (cdr instls) offset voffset))))
          (`(cmpq (int ,n1) (int ,n2))
           (cons `(movq (int ,n2) (reg rax))
                 (cons `(cmpq (int ,n1) (reg rax))
                       (patch (cdr instls) offset voffset))))
          (`(tail-jmp ,arg)
           (append
            `((movq ,arg (reg rax))
              (subq (int ,(- voffset)) (reg r15))
              (addq (int ,(- (round-16 offset))) (reg rsp))
              (popq (reg r14))
              (popq (reg r13))
              (popq (reg r12))
              (popq (reg rbx))
              (popq (reg rbp))
              (tail-jmp (reg rax)))
            (patch (cdr instls) offset voffset)))
          (_ (cons inst (patch (cdr instls) offset voffset)))))))

(define (pi-d d)
  (match d
    (`(define (,f ,a ...) : ,rt ,info ,blks)
     `(define (,f ,@a) :  ,rt ,info ,(for/list ((b blks)) `(,(car b) . (block . (() . ,(patch (cdddr b) (dict-ref info 'offset) (dict-ref info 'voffset))))))))))

(define (patch-instructions p)
  (match p
    (`(program ,info ,ds ...)
     `(program
       ,info
       ,@(for/list ((d ds)) (pi-d d))))))

;; print-x86 : x86 -> string

(define (format-rand rand)
  (match rand
    (`(int ,n) (format "$~s" n))
    (`(reg ,r) (format "%~s" r))
    (`(deref ,r ,n) (format "~s(%~s)" n r))
    (`(byte-reg ,r) (format "%~s" r))
    (`(global-value ,gv) (format "~s(%rip)" gv))
    (`(fun-ref ,label) (format "~s(%rip)" label))))

(define (format-inst inst)
  (match inst
    (`(set ,cc ,arg)
      (format "set~a ~a" cc (format-rand arg)))
    (`(jmp-if e ,label)
     (format "je ~a" label))
    (`(jmp-if l ,label)
     (format "jl ~a" label))
    (`(jmp-if g ,label)
     (format "jg ~a" label))
    (`(,op ,arg1 ,arg2)
     (format "~a ~a, ~a" op (format-rand arg1) (format-rand arg2)))
    (`(,op ,arg)
     (match op
       ((or 'callq 'jmp) (format "~a ~a" op arg))
       ('indirect-callq (format "callq *~a" (format-rand arg)))
       ('tail-jmp (format "jmp *~a" (format-rand arg)))     
       (_ (format "~a ~a" op (format-rand arg)))))
    (`(,op)
     (format "~a" op))))

(define (format-label lbl)
  (match lbl
    (`(,label . ,block)
     (match block
       (`(block ,info ,inst ...)
        (format "~a:\n~a" label (string-join (map format-inst inst) "\n\t" #:before-first "\t")))))))


(define (round-16 n)
  (if (= 0 (remainder n 16))
      n
      (round-16 (sub1 n))))

(define (p86-d d)
  (define (init-rtstk n)
    (if (zero? n) '() (cons '(movq (int 0) (deref r15 0)) (cons '(addq (int 8) (reg r15)) (init-rtstk (sub1 n))))))
  (match d
    (`(define (,f ,a ...) : ,rt ,info ,lbls)
     (let ((offset (cdr (assoc 'offset info)))
           (voffset (cdr (assoc 'voffset info)))
           (startlbl (dict-ref info 'startlbl))
           (conclbl (dict-ref info 'conclbl)))
       (let ((func
              `(,f .
                     (block ()
                            (pushq (reg rbp))
                            (movq (reg rsp) (reg rbp))
                            (pushq (reg rbx))
                            (pushq (reg r12))
                            (pushq (reg r13))
                            (pushq (reg r14))
                            (subq (int ,(- (round-16 offset))) (reg rsp))
                            ,@(if (eq? f 'main)
                                  '((movq (int 16384) (reg rdi))
                                    (movq (int 16384) (reg rsi))
                                    (callq initialize)
                                    (movq (deref rip rootstack_begin) (reg r15)))
                                  '())
                            ,@(init-rtstk (/ (- voffset) 8))
                            (jmp ,startlbl))))
             (conclusion
              `(,conclbl .
                           (block ()
                                  (subq (int ,(- voffset)) (reg r15))
                                  (addq (int ,(- (round-16 offset))) (reg rsp))
                                  (popq (reg r14))
                                  (popq (reg r13))
                                  (popq (reg r12))
                                  (popq (reg rbx))
                                  (popq (reg rbp))
                                  (retq)))))
         (string-append
          "\n"
          (string-join (map format-label lbls) "\n")
          "\n\n"
          (format "\t.globl ~a\n" f)
          "\t.align 16\n"
          (format-label func)
          "\n"
          (format-label conclusion)
          "\n"))))))

(define (print-x86 p)
  (match p
    (`(program ,info ,ds ...)
     (foldr (lambda (elem res) (string-append elem res)) "" (cons (string-join (map (lambda (p) (format "~a: .double ~a" (cdr p) (car p))) fppool) "\n") (for/list ((d ds)) (p86-d d)))))))

