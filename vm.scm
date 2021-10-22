#!chezscheme
(define-syntax λ (identifier-syntax lambda))
(pretty-one-line-limit 40)

;; 16-bit word, load-store instruction set
;; common instruction format
;; iiii | mmmm | aaaa abbb
;; iiii : opcode
;; mmmm : optional mode
;; aaaa, bbbb : register arguments

;; registers
;; 0 zero
;; 1 ip
;; 2 const
;; 3 cond
;; 4 stack
;; 5 frame
;; 6 ret
;; 7 overflow
;; 8-15 v0-v7

;; 0 [const | i: 12-bit immediate] i -> const
;; 1 [mov | mode | a b] b -> a
;;    mode: y or cond
;; 2 [store | a r] r -> *(a)
;; 3 [load | r a] *(a) -> r

;; 4 [alu | op | a b] a op b -> a
;;    op: one of add, sub, neg, inc, xor, or, and, not
;;    sets overflow
;; 5 reserved for mul
;; 6

;; 7 [cmp | op | a b] a op b -> cond
;;    op: one of zero, eq, neq, less, less-or-eq
;; 8
;; 9

;; 10 [shift | direction | a b] 1-bit shift of b -> a
;;    might set overflow
;; 11 [flip | a b] swapped bytes of b -> a
;; 12

;; 13
;; 14
;; 15

;; pseudo instructions
;; [jump mode | a] mov mode ip a;
;; [nop] alu or zero zero
;; [push | a] store stack a; const -word; add stack const;

;; calling convention
;; *stack = end of the previous stack
;; *frame = end of arguments, and beginning of new frame
;;   frame size is static for each function
;;   after loading the arguments, *stack is moved to end of current frame
;; ret = return address at call time, later the return value
;; v0-v5 <- fast arguments
;; *(stack+1) ... (*frame) <- slow arguments at the top of the caller's stack

(define ram-size 256)

(define (register-name name)
  (case name
    [zero 0] [ip 1] [const 2]
    [cond 3] [overflow 4]
    [stack 5] [frame 6] [ret 7]
    [v0 8] [v1 9] [v2 10] [v3 11]
    [v4 12] [v5 13] [v6 14] [v7 15]
    [else (error "register-name" (format "no register ~s" name))]))

(define (print-registers registers)
  (for-each
   (λ (r)
     (let* ([addr (* 2 (register-name r))]
            [v (bytevector-u16-native-ref registers addr)]
            [s (bytevector-s16-native-ref registers addr)])
       (printf "~8:<~s~> ~5d ~5d\n" r v s)
       ))
   '(ip const cond overflow
        stack frame ret
        v0 v1 v2 v3 v4 v5 v6 v7)))

(define (print-memory memory)
  (let ([size (/ (bytevector-length memory) 2)]
        [stride 8])
    (printf "RAM ~s\n" size)
    (for-each (λ (row)
                (printf "~5s: " (* row stride 2))
                (for-each (λ (column)
                            (let* ([addr (* 2 (+ column (* row stride)))]
                                   [val (bytevector-s16-native-ref memory addr)])
                              (printf "~6d" val)))
                          (iota stride))
                (printf "\n"))
              (iota (fxdiv size stride)))))

(define (read-register registers r)
  (bytevector-u16-native-ref registers (* 2 (register-name r))))

(define (vm instructions data)
  (let* ([instructions (list->vector instructions)]
         [registers (make-bytevector 32 0)]
         [ram (make-bytevector (* ram-size 2) 0)]
         [cycles 0])
    (define (write-register r val)
      (when (not (eq? r 'zero))
        (bytevector-u16-native-set! registers (* 2 (register-name r)) val)))

    (for-each
     (λ (v n) (bytevector-u16-native-set! ram (* 2 n) v))
     data (enumerate data))

    (let exec ()
      (let* ([ip (read-register registers 'ip)]
             [inst (vector-ref instructions ip)])
        (set! cycles (+ 1 cycles))
        ;; (printf "~4s: ~s \n" ip inst)

        (record-case
         inst
         [const (n) (assert (>= 12 (fxlength n))) (write-register 'const n)]
         [mov (mode a b) (assert (member mode '(y cond)))
              (let* ([true (= 1 (fxand 1 (read-register registers 'cond)))]
                     [condition (or (eq? mode 'y) true)])
                (when condition (write-register a (read-register registers b))))]

         [store (a r)
                (let ([addr (read-register registers a)]
                      [val (read-register registers r)])
                  (assert (< addr ram-size))
                  (bytevector-u16-native-set! ram (* 2 addr) val))]

         [load (r a)
               (let ([addr (read-register registers a)])
                 (assert (< addr ram-size))
                 (let ([val (bytevector-u16-native-ref ram (* 2 addr))])
                   (write-register r val)))]

         [alu (op a b)
              (let* ([x (read-register registers a)]
                     [y (read-register registers b)]
                     [op
                      (case op
                        [add fx+]
                        [sub (λ (x y) (fx+ x (fx+ 1 (fxxor y #xffff))))]
                        [neg (λ (x y) (fx+ 1 (fxxor x #xffff)))]
                        [inc (λ (x _) (fx+ 1 x))]
                        [xor fxxor] [or fxor] [and fxand]
                        [not (λ (x _) (fxxor x #xffff))])]
                     [result (op x y)]
                     [overflow (if (< #xffff result) 1 0)])
                (write-register a (fxand #xffff result))
                (write-register 'overflow overflow))]

         [cmp (op a b)
              (let* ([op (case op
                           [zero (λ (a _) (fxzero? a))]
                           [eq fx=] [neq (λ (a b) (not (fx= a b)))]
                           [less fx<] [less-or-eq fx<=]
                           [else (error "cmp" (format "invalid cmp ~s" op))])]
                     [val (op (read-register registers a)
                              (read-register registers b))])
                (write-register 'cond (if val 1 0)))]

         [shift (direction a b)
                (assert (member direction '(l r)))
                (let* ([x (read-register registers b)]
                       [s (case direction
                            [l (fxsll x 1)]
                            [r (fxsrl x 1)])]
                       [overflow (if (< #xffff s) 1 0)])
                  (write-register a (fxand #xffff s))
                  (write-register 'overflow overflow))]

         [flip (a b)
               (let* ([x (read-register registers b)]
                      [val (fxor (fxsll (fxand #xffff x) 8)
                                 (fxsrl x 8))])
                 (write-register a (fxor high low)))]

         [print (v) (printf "~s: ~s\n" v (read-register registers v))]

         [else (error "vm" (format "unknown op ~s" (car inst)))]))
      (write-register 'ip (+ 1 (read-register registers 'ip)))
      (when (< (read-register registers 'ip) (vector-length instructions))
        (exec)))

    (values registers ram cycles)))


(define (assemble asm)
  (let* ([labels '()]
         [asm
          (let line ([asm asm] [addr 0])
            (if (null? asm) '()
                (let* ([inst (car asm)] [name (car inst)]
                       [label
                        (case name
                          [label (cons* (cadr inst) (- addr 1))]
                          [data (cons* (cadr inst) (caddr inst))]
                          [comment (set! addr (- addr 1)) #f]
                          [else #f])]
                       [next-addr (if label addr (+ 1 addr))])
                  (when label
                    (set! labels (cons label labels)))
                  (if (not label)
                      (cons inst (line (cdr asm) next-addr))
                      (line (cdr asm) next-addr)))))])
    (for-each (λ (name value)
                (set! asm (subst value name asm)))
              (map car labels) (map cdr labels))
    (filter (λ (inst) (not (eq? 'comment (car inst)))) asm)))

(define asm-1
  (assemble
   `((const 0) (mov y v1 const)  ;; from
     (const 20) (mov y v0 const)  ;; to
     (const 10) (mov y v3 const)  ;; size
     (label "loop")
     (load v2 v1)      ;; x = *v1
     (alu inc v1 zero) ;; v1++
     (store v0 v2)      ;; *v0 = x
     (alu inc v0 zero) ;; v2++
     (const 1)
     (alu sub v3 const) ;; n--
     (cmp zero v3 zero)
     (cmp zero cond zero)
     (const "loop")
     (mov cond ip const) ;; jump loop
     )))

(define asm-2
  (assemble
   `((data "xs" 0)
     (const "xs") (mov y v0 const)      ;; v0 from = 0
     (const 0) (mov y v1 const)         ;; v1 i = 0
     (const 10) (mov y v2 const)        ;; v2 count = 10
     (const 0) (mov y v3 const)         ;; v3 sum = 0
     (label "repeat")
     (load v4 v0)                       ;; v4 x = *from
     (alu inc v0 zero)                  ;; from++
     (alu add v3 v4)                    ;; sum += x
     (alu inc v1 zero)                  ;; i++
     (cmp eq v1 v2)                     ;; if v1 == v2
     (const "stop") (mov cond ip const) ;; jump stop
     (const "repeat") (mov y ip const)  ;; jump repeat
     (label "stop")
     (store v0 v3)
     )))

;; (for-each (λ (p) (printf "~s\n" p)) asm-2)
;; (vm asm-1
;;     `(1 2 3 4 5 6 7 8 9 ,(- 65535 45)))


(define symgen
  (let ([n 0])
    (λ (name)
      (let ([sym (string->symbol (format ":~o-~s" name n))])
        (set! n (+ 1 n)) sym))))

(define-record-type environment (fields parent symbols))
(define (new-environment parent)
  (make-environment parent (make-hashtable symbol-hash symbol=?)))

(define (get-symbol env name)
  (let ([lookup (symbol-hashtable-ref
                 (environment-symbols env)
                 name #f)])
    (or lookup
        (if (not (environment-parent env)) #f
            (get-symbol (environment-parent env) name)))))

(define (macro? name)
  (memq name '(:fn-addr)))

(define (builtin? name)
  (memq name '(def = load store
                   return
                   < > <= >= == !=
                   + - ++ -= +=
                   print)))

(define (function-label name)
  (format ".fn-~o" (symbol->string name)))

(define (analyze-symbols code)
  (define symbol-table (make-hashtable symbol-hash symbol=?))
  (define (descend env expr)
    (cond
     [(symbol? expr)
      (let ([resolve (get-symbol env expr)])
        (when (not resolve)
          (error "symbol analysis" (format "unknown name ~s" expr)))
        resolve)]
     [(number? expr) expr]

     [else
      (let ([form (car expr)])
        (cond
         [(eq? form '=)
          (let* ([lhs (cadr expr)]
                 [rhs (caddr expr)]
                 [rhs (descend env rhs)])
            (let ([var (get-symbol env lhs)])
              (if (not var)
                  (let ([name (symgen (symbol->string lhs))])
                    (symbol-hashtable-set!
                     (environment-symbols env) lhs name)
                    `(def ,name ,rhs))
                  `(= ,var ,rhs))))]

         [(memq form '(prog while))
          (let ([new-scope (new-environment env)]
                [result (list form)])
            (for-each
             (λ (statement)
               (set! result (cons (descend new-scope statement) result)))
             (cdr expr))
            (vector-for-each
             (λ (cell) (let ([k (car cell)] [v (cdr cell)])
                         (symbol-hashtable-set! symbol-table k v)))
             (hashtable-cells (environment-symbols new-scope)))
            (reverse result))]

         [(eq? form 'if)
          (cons 'if (map (λ (s) (descend env s)) (cdr expr)))]

         [(macro? form) expr]

         [(builtin? form)
          (let ([result (list form)])
            (for-each (λ (expr) (append! result (list (descend env expr))))
                      (cdr expr))
            result)]

         [(or (not (symbol? form))
              (get-symbol env form)) ;; function address call
          (let ([name (descend env form)]
                [args (map (λ (arg) (descend env arg)) (cdr expr))])
            (append `(addr-call #f ,name) args))]

         [else ;; direct call
          (let ([name form]
                [args (map (λ (arg) (descend env arg)) (cdr expr))])
            (append `(call #f ,name) args))])
        )]))

  (define (parse-top-level block)
    (let* ([signature (cadr block)]
           [name (car signature)]
           [arguments (cdr signature)]
           [body (cddr block)]
           [fn-env (new-environment #f)])
      `(fn ,name
           ,(map (λ (arg)
                   (let ([name (symgen (symbol->string arg))])
                     (symbol-hashtable-set!
                      (environment-symbols fn-env) arg name)
                     name))
                 arguments)
           ,(descend fn-env `(return (prog . ,body))))))

  (let ([ast (cons 'program (map parse-top-level code))])
    (values ast symbol-table)))



(define (annotate-tail-calls ast)
  (define (descend expr)
    (if (not (pair? expr)) expr
        (let ([form (car expr)])
          ;; (printf "~s\n" form)
          (cond
           [(eq? form 'program)
            (cons form (map descend (cdr expr)))]
           [(eq? form 'fn)
            (let ([name (cadr expr)]
                  [args (caddr expr)]
                  [body (cadddr expr)])
              `(fn ,name ,args ,(descend body)))]
           [(eq? form 'return)
            `(return ,(descend (cadr expr)))]
           [(eq? form 'prog)
            (let ([tail (last-pair expr)])
              (append (list-head expr (- (length expr) 1))
                      (list (descend (car tail)))))]
           [(eq? form 'if)
            (let ([condition (cadr expr)]
                  [true (descend (caddr expr))]
                  [false (cdddr expr)])
              (if (null? false)
                  `(if ,condition ,true)
                  `(if ,condition ,true
                       ,(descend (car false)))))]
           [(eq? form 'addr-call)
            (set-car! (cdr expr) 'tail-call)
            expr]
           [(eq? form 'call)
            (set-car! (cdr expr) 'tail-call)
            expr]
           [(memq form '(= while)) expr]
           [(macro? form) expr]
           [(builtin? form) expr]
           [else (error "tco" (format "a: ~s" form))])
          )))

  (descend ast))



(define (generate-ir symbols ast)
  (define (builtin-ir env ir fn args)
    (case fn
      [=
       (let* ([lhs (car args)] [rhs (cadr args)]
              [ir (cons `(set ,lhs ,rhs) ir)])
         (values ir lhs))]
      [def
       (let* ([name (car args)] [value (cadr args)]
              [ir (cons `(def ,name) ir)])
         (builtin-ir env ir '= (list name value)))]
      [+
       (let* ([var (symgen "add")]
              [a (car args)] [b (cadr args)]
              [code `((value ,var (+ ,a ,b)))])
         (values (append (reverse code) ir) var))]
      [-
       (let* ([var (symgen "sub")]
              [a (car args)] [b (cadr args)]
              [code `((value ,var (- ,a ,b)))])
         (values (append (reverse code) ir) var))]
      [+=
       (let*-values ([(ir add) (builtin-ir env ir '+ args)])
         (builtin-ir env ir '= (list (car args) add)))]
      [-=
       (let*-values ([(ir add) (builtin-ir env ir '- args)])
         (builtin-ir env ir '= (list (car args) add)))]
      [++
       (let-values ([(ir one) (descend env ir 1)])
         (builtin-ir env ir '+= (list (car args) one)))]
      [(< > <= >= == !=)
       (let* ([a (car args)] [b (cadr args)]
              [result (symgen "cmp")]
              [code `((value ,result (cmp ,fn ,a ,b)))])
         (values (append (reverse code) ir) result))]
      [load
       (let* ([var (symgen "mem")] [a (car args)]
              [code `((value ,var (load ,a)))])
         (values (append code ir) var))]
      [store
       (let* ([a (car args)] [b (cadr args)]
              [code `((store ,a ,b))])
         (values (append code ir) a))]
      [return
       (let* ([x (car args)]
              [code `((return ,x))])
         (values (append code ir) x))]
      [print
       (let* ([x (car args)] [code `((print ,x))])
         (values (append code ir) x))]
      [else (error "builtin-ir" (format "unknown builtin ~s" fn))]))

  (define (macro-ir env ir name args)
    (case name
      [:fn-addr
       (let* ([fn (car args)] [addr (function-label fn)]
              [val (symgen (format "f-~s" fn))])
         (values (append `((value ,val (fn-addr ,addr))) ir)
                 val))]
      [else (error "macro-ir" (format "unknown macro ~s" name))]))

  (define (descend env ir expr)
    (cond
     [(symbol? expr)
      (let ([resolve (symbol-hashtable-ref env expr #f)])
        (if resolve (values ir resolve)
            (let* ([name (symbol->string expr)]
                   [name (substring name 1 (string-length name))]
                   [var (symgen (format "var-~o" name))])
              (symbol-hashtable-set! env expr var)
              (values ir var))))]

     [(number? expr)
      (let* ([var (symgen (format "const<~s>" expr))]
             [code `((value ,var (const ,expr)))])
        (symbol-hashtable-set! env var expr)
        (values (append code ir) var))]

     [else
      (let ([form (car expr)])
        (cond
         [(eq? form 'program)
          (values
           (map (λ (fn)
                  (let-values ([(ir _) (descend env ir fn)])
                    (reverse ir)))
                (cdr expr))
           (void))]

         [(eq? form 'fn)
          (let* ([name (cadr expr)]
                 [args (caddr expr)]
                 [args
                  (map
                   (λ (arg position)
                     (let* ([name (symbol->string arg)]
                            [name (substring name 1 (string-length name))]
                            [var (symgen (format "arg-~o" name))])
                       (symbol-hashtable-set! env arg var)
                       `(fn-arg ,var ,position)))
                   args (enumerate args))]
                 [body (cadddr expr)]
                 [ir (cons `(function ,name ,(length args)) ir)]
                 [ir (append (reverse args) ir)]
                 [ir (cons `(function-start) ir)])
            (descend env ir body))]

         [(eq? form 'prog)
          (let prog ([statements (cdr expr)]
                     [ir ir] [ret (void)])
            (if (null? statements) (values ir ret)
                (let-values ([(ir ret) (descend env ir (car statements))])
                  (prog (cdr statements) ir ret))))]

         [(eq? form 'while)
          (let* ([condition (cadr expr)]
                 [body (cddr expr)]
                 [repeat (symgen "repeat")]
                 [loop-body (symgen "loop")]
                 [end (symgen "end")])
            (let*-values
                ([(ir) (cons `(label ,repeat) ir)]
                 [(ir test) (descend env ir condition)]
                 [(ir) (cons `(branch ,test ,loop-body) ir)]
                 [(ir) (cons `(jump ,end) ir)]
                 [(ir) (cons `(label ,loop-body) ir)]
                 [(ir ret) (descend env ir (cons 'prog body))]
                 [(ir) (cons `(jump ,repeat) ir)]
                 [(ir) (cons `(label ,end) ir)])
              (values ir ret)))]

         [(eq? form 'if)
          (let* ([condition (cadr expr)]
                 [true-expr (caddr expr)] [if-true (symgen "if-true")]
                 [false-expr (cdddr expr)] [if-false (symgen "if-false")]
                 [if-end (symgen "if-end")]
                 [if-val (symgen "if-val")])
            (if (not (null? false-expr))
                (let*-values ([[false-expr] (car false-expr)]
                              [(ir) (cons `(def ,if-val) ir)]
                              [(ir test) (descend env ir condition)]
                              [(ir) (cons `(branch ,test ,if-true) ir)]
                              [(ir) (cons `(jump ,if-false) ir)]
                              [(ir) (cons `(label ,if-true) ir)]
                              [(ir true-ret) (descend env ir true-expr)]
                              [(ir _) (builtin-ir env ir '= (list if-val true-ret))]
                              [(ir) (cons `(jump ,if-end) ir)]
                              [(ir) (cons `(label ,if-false) ir)]
                              [(ir false-ret) (descend env ir false-expr)]
                              [(ir _) (builtin-ir env ir '= (list if-val false-ret))]
                              [(ir) (cons `(label ,if-end) ir)])
                  (values ir if-val))))]

         [(memq form '(call addr-call))
          (let ([function (caddr expr)]
                [args (cdddr expr)]
                [tail? (cadr expr)])
            (let eval-args ([args args] [arg-values '()] [arg-ir '()])
              (if (not (null? args))
                  (let-values ([(arg-ir val) (descend env arg-ir (car args))])
                    (eval-args (cdr args) (cons val arg-values) arg-ir))
                  (let-values ([(fn-ir fn)
                                (case form
                                  [call (values '() function)]
                                  [addr-call (descend env '() function)])])
                    (let* ([ir (append fn-ir arg-ir ir)]
                           [args (reverse arg-values)]
                           [call (append (list form tail? fn) args)]
                           [result (symgen (format "val-~s" fn))]
                           [code `((value ,result ,call))])
                      (values (append code ir) result))))))]

         [(builtin? form)
          (let eval-args ([args (cdr expr)] [arg-values '()] [arg-ir '()])
            (if (not (null? args))
                (let-values ([(arg-ir val) (descend env arg-ir (car args))])
                  (eval-args (cdr args) (cons val arg-values) arg-ir))
                (let ([ir (append arg-ir ir)])
                  (builtin-ir env ir form (reverse arg-values)))))]

         [(macro? form) (macro-ir env ir form (cdr expr))]

         [else (error "ir generation" (format "unrecognized form\n    ~s" expr))])
        )]))

  (let*-values ([(value-table) (make-hashtable symbol-hash symbol=?)]
                [(ir _) (descend value-table '() ast)])
    (values (reverse ir) value-table)))


(define (lifetime-analysis ir)
  (define (extract-uses instr)
    (record-case
     instr
     [load (a) (list a)]
     [cmp (_ a b) (list a b)]
     [(+ -) (a b) (list a b)]
     [(const fn-addr) _ '()]
     [call (_ _ . args) args]
     [addr-call (_ f . args) (cons f args)]
     [else (error "lifetime"
                  (format "unknown builtin:\n   ~s" instr))]))

  (define lifetimes (make-eqv-hashtable))
  (define labels (make-hashtable symbol-hash symbol=?))
  (define jumps (make-eqv-hashtable))
  (define reverse-jumps (make-eqv-hashtable))

  (for-each
   (λ (instr line) (when (eq? (car instr) 'label)
                     (symbol-hashtable-set! labels (cadr instr) line)))
   ir (enumerate ir))

  (for-each
   (λ (instr line)
     (let ([id (case (car instr)
                 [jump (cadr instr)]
                 [branch (caddr instr)]
                 [else #f])])
       (when id
         (hashtable-set! jumps line id)
         (hashtable-update!
          reverse-jumps
          (symbol-hashtable-ref labels id 'ERR)
          (λ (sources) (cons line sources))
          '()))))
   ir (enumerate ir))

  (let backwards-scan ([line (- (length ir) 1)])
    (let ([instr (list-ref ir line)])
      (define (use var)
        (hashtable-update!
         lifetimes line
         (λ (live-vars)
           (if (member var live-vars) live-vars
               (cons var live-vars))) '()))
      (define (definition var)
        (hashtable-update!
         lifetimes line (λ (live-vars) (remove var live-vars)) '()))

      (record-case
       instr
       [set (a b) (use b)]
       [def (x) (definition x)]
       [value (var f) (definition var)
              (map use (extract-uses f))]
       [store (var val) (use var) (use val)]
       [function (name) (void)]
       [function-start () (void)]
       [fn-arg (arg _) (definition arg)]
       [return (var) (use var)]
       [(label jump) (id) (void)]
       [(branch) (cmp _) (use cmp)]
       [print (x) (use x)]
       [else (error "lifetimes"
                    (format "unknown ir form:\n    ~s" instr))])

      (let* ([predecessors (hashtable-ref reverse-jumps line '())]
             [predecessors (if (zero? line) predecessors
                               (cons (- line 1) predecessors))]
             [local-lifetimes (hashtable-ref lifetimes line '())])
        (define (set-union u v)
          (fold-left (λ (union x) (if (memq x union) union
                                      (cons x union))) u v))
        (for-each
         (λ (source)
           (let* ([preceding-lifetimes
                   (hashtable-ref lifetimes source '())]
                  [lifetime-union
                   (set-union local-lifetimes preceding-lifetimes)]
                  [changed? (< (length preceding-lifetimes)
                               (length lifetime-union))])
             (when (or changed? (= source (- line 1)))
               (hashtable-set! lifetimes source lifetime-union)
               (backwards-scan source))))
         predecessors))))

  lifetimes)


(define (function-asm ir lifetimes)
  (define asm '())
  (define (emit! code)
    (set! asm (append (reverse code) asm)))

  (define registers (make-eqv-hashtable))
  (define variables (make-hashtable symbol-hash symbol=?))
  (define next-register
    (let ([id 0])
      (λ () (set! id (+ 1 id)) id)))
  (define (first-free-register live-vars)
    (let scan ([r 0])
      (let ([stored-var (hashtable-ref registers r 'nil)])
        (if (memq stored-var live-vars)
            (scan (+ r 1))
            (begin (symbol-hashtable-delete! variables stored-var)
                   r)))))

  (define (reference! ir-line var)
    (or (let ([store
               (symbol-hashtable-ref variables var #f)])
          (and store `(ref ,store)))
        (let* ([register
                (if lifetimes
                    (first-free-register
                     (hashtable-ref lifetimes ir-line '()))
                    (next-register))])
          (hashtable-set! registers register var)
          (symbol-hashtable-set! variables var register)
          `(ref ,register))))

  (define (definition! ir-line var)
    (let ([ref (reference! ir-line var)])
      `(def ,(cadr ref))))

  (define (builtin instr line out-var)
    (record-case
     instr
     [cmp (op a b)
          (let* ([op (case op [== 'eq] [!= 'neq]
                           [< 'less] [<= 'less-or-eq]
                           [(> >= zero) (void)])]
                 [a (reference! line a)] [b (reference! line b)]
                 [out (reference! line out-var)])
            (emit! `((cmp ,op ,a ,b)
                     (mov y ,out cond))))]
     [load (addr) (let* ([addr (reference! line addr)]
                         [out (reference! line out-var)])
                    (emit! `((load ,out ,addr))))]

     [fn-addr (fn)
              (emit! `((const ,fn)
                       (mov y ,(reference! line out-var) const)))]

     [(call addr-call)
      (tail-call fn . args)
      (define fn-addr (case (car instr)
                        [call `(const-ref ,(function-label fn))]
                        [addr-call (reference! line fn)]))
      (define ret-addr (symbol->string (symgen "ret")))
      (define live-variables
        (filter
         (λ (exists) exists)
         (map (λ (var) (symbol-hashtable-ref variables var #f))
              (hashtable-ref lifetimes (+ 1 line) '()))))

      (cond
       [tail-call
        ;; stack only args
        (emit! `((const 1)))
        (for-each
         (λ (arg) (let ([var (reference! line arg)])
                    (emit! `((alu sub stack const) (store stack ,var)))))
         args)
        (emit! `((mov y v6 ,fn-addr)
                 (const ,argument-frame-size)
                 (alu add frame const)
                 (const ,(length args))
                 (alu add stack const)
                 (const 1)))
        (for-each
         (λ (_) (emit!
                 `((alu sub stack const) (alu sub frame const)
                   (load v7 stack) (store frame v7))))
         (enumerate args))
        ;; restore caller's stack
        (emit! `((mov y stack frame)
                 (const ,(length args))
                 (alu add stack const)
                 (mov y ip v6)))]

       [else
        ;; save ret, frame
        (emit! `((const 1)
                 (alu sub stack const)
                 (store stack ret)
                 (alu sub stack const)
                 (store stack frame)
                 ;; save registers v0-v7
                 (call-save-registers ,live-variables)))

        ;; save this stack position for reading off the arguments later

        (emit! `((mov y ret stack)))

        ;; arrange the arguments
        (for-each
         (λ (arg position)
           (let ([var (reference! line arg)])
             (if #f ;; (< position 5)
                 ;; register
                 (begin (void))
                 ;; stack
                 (begin
                   (emit! `((alu sub stack const) (store stack ,var)))))))
         args (enumerate args))

        ;; set the new frame address
        ;; stack <- argument section
        ;; ret <- here (ip)
        (emit! `((mov y frame stack)
                 (mov y stack ret)
                 (const ,ret-addr) (mov y ret const)))

        ;; load fn address, jump
        (emit! `((mov y ip ,fn-addr)
                 ;; return point
                 (label ,ret-addr)
                 ;; restore registers v0-v7
                 (call-restore-registers ,live-variables)))

        ;; restore frame
        (emit! `((load frame stack) (alu inc stack zero)))

        (let ([out (reference! line out-var)])
          (emit! `(;; out <- return value
                   (mov y ,out ret)
                   ;; restore ret
                   (const 1)
                   (load ret stack) (alu inc stack zero))))])]

     [const (value) (let* ([out (reference! line out-var)])
                      (emit! `((mov y ,out (const-ref ,value)))))]
     [+ (a b) (let* ([a (reference! line a)]
                     [b (reference! line b)]
                     [out (reference! line out-var)])
                (emit! `((mov y ,out ,a)
                         (write ,out)
                         (alu add ,out ,b))))]
     [- (a b) (let* ([a (reference! line a)]
                     [b (reference! line b)]
                     [out (reference! line out-var)])
                (emit! `((mov y ,out ,a)
                         (write ,out)
                         (alu sub ,out ,b))))]

     [else (error "asm" (format "unknown builtin ~s" instr))]))

  (define (next ir line)
    (when (not (null? ir))
      (let ([instr (car ir)])
        (emit! `((comment ,instr)))
        (when (not (null? (hashtable-ref lifetimes line '())))
          (emit! `((comment ,(format "~~~s" (hashtable-ref
                                             lifetimes line '()))))))

        (record-case
         instr
         [set (var val) (let* ([val (reference! line val)]
                               [var (definition! line var)])
                          ;; dont load spilled target for set
                          (emit! `((mov y ,var ,val)
                                   (write ,var))))]
         [def () (void)]

         [value (var instr) (builtin instr line var)
                (emit! `((write ,(reference! line var))))]

         [store (addr val) (let* ([val (reference! line val)]
                                  [addr (reference! line addr)])
                             (emit! `((store ,addr ,val))))]

         [branch (condition jump)
                 (let ([test (reference! line condition)])
                   (emit! `((mov y cond ,test)
                            (const ,(symbol->string jump))
                            (mov cond ip const))))]

         [jump (jump) (emit! `((const ,(symbol->string jump))
                               (mov y ip const)))]

         [label (id) (emit! `((label ,(symbol->string id))))]

         [function
          (name arg-count)
          (set! argument-frame-size arg-count)
          (emit! `((label ,(function-label name))))]

         [fn-arg (var position)
                 (let ([var (reference! line var)])
                   (emit! `((const 1)
                            (alu sub stack const)
                            (load ,var stack)
                            (write ,var))))]

         [function-start
          () (emit! '((alu sub stack (const-ref :frame-size))))]

         [return (val) (let* ([val (reference! line val)])
                         (emit! `(;; restore caller's stack
                                  (mov y stack frame)
                                  ;; pop the stack arguments
                                  (const ,argument-frame-size)
                                  (alu add stack const)
                                  (mov y const ret)
                                  (mov y ret ,val)
                                  (mov y ip const))))]

         [print (x) (emit! `((print ,(reference! line x))))]

         [else (error "asm" (format "unknown ir form ~s" instr))]))

      (next (cdr ir) (+ line 1))))

  (define (register-assignment asm)
    (define spill-slots '((v6 . #f) (v7 . #f)))
    (define (evict-spills!)
      (set! spill-slots (map (λ (slot) (cons* (car slot) #f))
                             spill-slots)))
    (define (spill-reuse! var)
      (let ([recent-use
             (find (λ (slot) (eqv? var (cdr slot))) spill-slots)])
        (if (not recent-use) #f
            (begin (set! spill-slots (cons recent-use
                                           (remq recent-use spill-slots)))
                   (car recent-use)))))
    (define (spill-restore! var)
      (or (spill-reuse! var)
          (let* ([cutoff (- (length spill-slots) 1)]
                 [evicted (list-ref spill-slots cutoff)])
            (set! spill-slots (cons (cons* (car evicted) var)
                                    (list-head spill-slots cutoff)))
            (car evicted))))

    (define highest-frame-offset 0)

    (define max-direct-register (- 7 (length spill-slots)))
    (define (spill-frame-offset r)
      (let ([position (- r max-direct-register)])
        (set! highest-frame-offset (max position highest-frame-offset))
        position))
    (define (direct-register var)
      (if (< max-direct-register var) #f
          (string->symbol (format "v~s" var))))

    (define (scan asm)
      (cond
       [(null? asm)
        '()]
       [(eq? (caar asm) 'comment)
        (cons (car asm) (scan (cdr asm)))]
       [(eq? (caar asm) 'label)
        ;; might jump here, evict all temporaries
        (evict-spills!)
        (cons (car asm) (scan (cdr asm)))]

       [(eq? (caar asm) 'write)
        (let ([var (cadar (cdar asm))])
          (if (direct-register var)
              (scan (cdr asm))
              (let* ([addr (spill-frame-offset var)]
                     [register (spill-restore! var)])
                (append `((const ,addr)
                          (alu neg const zero)
                          (alu add const frame)
                          (store const ,register))
                        (scan (cdr asm))))))]

       [(eq? (caar asm) 'call-save-registers)
        (let ([live (cadr (car asm))])
          (append
           (fold-left
            append '()
            (map (λ (r) (let ([vx (string->symbol (format "v~s" r))])
                          `((alu sub stack const) (store stack ,vx))))
                 live))
           (scan (cdr asm))))]

       [(eq? (caar asm) 'call-restore-registers)
        (let ([live (cadr (car asm))])
          (append
           (fold-left
            append '()
            (map (λ (r) (let ([vx (string->symbol (format "v~s" r))])
                          `((load ,vx stack) (alu inc stack zero))))
                 (reverse live)))
           (scan (cdr asm))))]

       [else
        (let* ([instruction (car asm)]
               [references
                (filter (λ (x) (and (pair? x) (eq? 'ref (car x))))
                        instruction)]
               [references (map cadr references)]
               [loads
                (map
                 (λ (var)
                   (if (or (direct-register var) (spill-reuse! var)) '()
                       (let* ([addr (spill-frame-offset var)]
                              [register (spill-restore! var)])
                         `((const ,addr)
                           (alu neg const zero)
                           (alu add const frame)
                           (load ,register const)))))
                 references)]
               [loads (apply append loads)]
               [instruction
                (map
                 (λ (x)
                   (if (not (pair? x)) x
                       (let ([access (car x)] [var (cadr x)])
                         (cond
                          [(and (memq access '(ref def))
                                (direct-register var))
                           (direct-register var)]
                          [(eq? access 'ref) (spill-reuse! var)]
                          [(eq? access 'def) (spill-restore! var)]
                          [else x]))))
                 instruction)])
          (append loads (cons instruction
                              (scan (cdr asm)))))]))

    (let ([asm (scan asm)])
      (subst highest-frame-offset ':frame-size asm)))

  (define (load-consts asm)
    (if (null? asm) '()
        (let* ([instruction (car asm)]
               [const-ref
                (find
                 (λ (x) (and (pair? x) (eq? 'const-ref (car x))))
                 instruction)])
          (append
           (if (not const-ref) (list instruction)
               (let ([val (cadr const-ref)])
                 (if (eq? 0 val)
                     (list (subst 'zero const-ref instruction))
                     (list `(const ,(cadr const-ref))
                           (subst 'const const-ref instruction)))))
           (load-consts (cdr asm))))))

  (next ir 0)
  (load-consts
   (register-assignment (reverse asm))))

(define (generate-asm ir)
  (let* ([lifetimes (map lifetime-analysis ir)]
         [asm-fns (map (λ (fn lifetimes) (function-asm fn lifetimes))
                       ir lifetimes)]
         [asm (fold-left append '() asm-fns)])
    (append `((comment 'init)
              (const ".halt")
              (mov y ret const)
              (const ,ram-size)
              (mov y frame const)
              (mov y stack const)
              (const ,(function-label 'main))
              (alu add zero zero)
              (mov y ip const))
            asm
            '((label ".halt")))))


(define (compile code)
  (let*-values ([(ast symbols) (analyze-symbols code)]
                [(ast) (annotate-tail-calls ast)]
                ;; [_ (pretty-print ast)]
                [(ir value-table) (generate-ir symbols ast)]
                ;; [_ (pretty-print ir)]
                [(asm) (generate-asm ir)])
    asm))

(define (print-asm asm)
  (pretty-initial-indent 5)
  (let next-line ([asm asm] [line 0])
    (cond [(null? asm) (void)]
          [(eq? (caar asm) 'comment)
           (printf ";; ~o\n" (cadr (car asm)))
           (next-line (cdr asm) line)]
          [(eq? (caar asm) 'label)
           (printf " ~o:\n" (cadr (car asm)))
           (next-line (cdr asm) line)]
          [else
           (printf "~5s" line) (pretty-print (car asm))
           (next-line (cdr asm) (+ line 1))]))
  (pretty-initial-indent 0)
  (printf "\n"))

;; low level lisp-like language
(printf "program          size    cycles    memory  check\n")
(define (run-l5 name code data checks)
  (let* ([asm (compile code)]
         [bin (assemble asm)]
         [result (format "~16a ~8s" name (length bin))])
    (let-values ([(registers ram cycles) (vm bin data)])
      (set! result
            (string-append
             result
             (format "~8s" cycles)
             (format "~8o  " (format "~3,1f%" (* 100. (- 1 (memory-usage ram)))))))
      (if (checks asm registers ram)
          (set! result (string-append result "ok"))
          (begin
            (set! result (string-append result "failed"))
            (print-asm asm)
            (print-registers registers)
            (print-memory ram)))
      (printf "~o\n" result))))

(define (memory-usage ram)
  (let ([longest-run 0]
        [size (bytevector-length ram)])
    (let scan ([n 0] [run 0])
      (set! longest-run (max run longest-run))
      (when (< n size)
        (scan (+ 1 n) (if (= 0 (bytevector-u8-ref ram n))
                          (+ 1 run) 0))))
    (/ longest-run size)))

(run-l5 "expr"
        '((fn (main)
              (= a 13)
              (= b 5)
              (= c 12)
              (- (+ (+ a c) (- b b)) b)))
        '()
        (λ (asm registers ram)
          (= 20 (read-register registers 'ret))))

(run-l5 "reuse"
        '((fn (main)
              (= a 9)
              (+ a (+ 9 9))))
        '()
        (λ (asm registers ram)
          (= 27 (read-register registers 'ret))))

(run-l5 "spill"
        '((fn (main)
              (+ 1 (+ 2 (+ 3 (+ 4 (+ 5 (+ 6 (+ 7 (+ 8 9))))))))))
        '()
        (λ (asm registers ram)
          (= 45 (read-register registers 'ret))))

(run-l5 "control"
        '((fn (main) (if (== 0 1) (prog 1 2)
                         (prog (if (!= 0 1) 4 3)))))
        '()
        (λ (asm registers ram)
          (= 4 (read-register registers 'ret))))

(run-l5 "fncall"
        '((fn (main) (foo 2 3))
          (fn (foo a b) (bar a b 7 11))
          (fn (bar q w e r) (+ q (+ w (+ e (- r 10))))))
        '()
        (λ (asm registers ram)
          (= 13 (read-register registers 'ret))))

(run-l5 "tail-call"
        '((fn (main) (spin 4095))
          (fn (spin n x) (if (< n x) (spin (+ n x) x) n)))
        '() (λ (asm registers ram) (> 1. (memory-usage ram))))

(run-l5 "fib"
        '((fn (main) (fib 21))
          (fn (fib x)
              (= a 1) (= b 1)
              (while (< 0 x)
                     (= c a) (= a b)
                     (+= b c)
                     (-= x 1))
              b))
        '()
        (λ (asm registers ram)
          (= 28657 (read-register registers 'ret))))

(run-l5 "recursion"
        '((fn (main) (fib (load 0)))
          (fn (fib n)
              (if (< n 2) 1
                  (+ (fib (- n 1))
                     (fib (- n 2))))))
        '(20)
        (λ (asm registers ram)
          (= 10946 (read-register registers 'ret))))

(run-l5 "partial-sums"
        '((fn (main)
              (= to 16)
              (= from 0)
              (= sum 0)
              (= n 0)
              (= count 10)
              (while (!= n count)
                     (+= sum (load from))
                     (store to sum)
                     (++ to)
                     (++ from)
                     (++ n))
              sum))
        '(1 2 3 4 5 6 7 8 9 65490)
        (λ (asm registers ram)
          (= 65535 (read-register registers 'ret))))


(run-l5 "array"
        '((fn (init) (store 0 1))
          (fn (iota out n)
              (= i 0)
              (while (< i n)
                     (store (+ i out) i)
                     (++ i)))
          (fn (range-sum a b)
              (= sum 0)
              (while (< a b)
                     (+= sum (load a))
                     (++ a))
              sum)
          (fn (main)
              (init)
              (= size 10)
              (= arr 16)
              (iota arr (+ arr size))
              (range-sum arr (+ arr size))))
        '()
        (λ (asm registers ram)
          (= 45 (read-register registers 'ret))))

(run-l5 "fn-addr"
        '((fn (x f a b c) (f a b c))
          (fn (y f a b) (f a b))
          (fn (z f a) (f a))
          (fn (w a) a)
          (fn (main)
              ((:fn-addr x)
               (:fn-addr y)
               (:fn-addr z)
               (:fn-addr w) 7)))
        '()
        (λ (asm registers ram)
          (= 7 (read-register registers 'ret))))

(run-l5
 "cmp"
 '((fn (zero? p) (== p 0))
   (fn (main) (zero? 0)))
 '()
 (λ (asm registers ram) (= 1 (read-register registers 'ret))))

(run-l5
 "lib"
 '((fn (nil? p) (== 0 p))

   (fn (malloc-init) (store 0 0))
   (fn (mmb-size p) (load (+ p 1)))
   (fn (mmb-next p) (load p))
   (fn (mmb-next-set! p addr) (store p addr))
   (fn (mmb-past p) (+ p (+ 2 (mmb-size p))))
   (fn (mmb-create! addr size)
       (store addr 0) (store (+ addr 1) size))
   (fn (mmb-last p) (if (nil? (mmb-next p))
                        p (mmb-last (mmb-next p))))
   (fn (mmb-find-parent from to)
       (if (== to (mmb-next from))
           from
           (prog
            (= next (mmb-next from))
            (if (nil? next) 0
                (mmb-find-parent next to)))))

   (fn (malloc-find-space p size)
       (= next (mmb-next p))
       (if (nil? next) p
           (prog (= gap (- next (mmb-past p)))
                 (if (<= (+ 2 size) gap) p
                     (malloc-find-space next size)))))

   (fn (malloc size)
       (= at (malloc-find-space 0 size))
       (= new (mmb-past at))
       (mmb-create! new size)
       (mmb-next-set! new (mmb-next at))
       (mmb-next-set! at new)
       (+ 2 new))

   (fn (free p)
       (= p (- p 2))
       (if (nil? p) (return 0) (prog 0))
       (= prev (mmb-find-parent 0 p))
       (mmb-next-set! prev (mmb-next p))
       1)

   (fn (nil) 0)
   (fn (cons x l)
       (= cell (malloc 2))
       (store cell x)
       (store (+ 1 cell) l)
       cell)
   (fn (car l) (load l))
   (fn (cdr l) (load (+ 1 l)))
   (fn (null? l) (nil? l))

   (fn (map f l)
       (if (null? l) (nil)
           (cons (f (car l))
                 (map f (cdr l)))))
   (fn (filter f l)
       (if (null? l) (nil)
           (if (f (car l))
               (cons (car l) (filter f (cdr l)))
               (filter f (cdr l)))))

   (fn (iota-recur i n)
       (if (<= n i) (nil)
           (cons i (iota-recur (+ 1 i) n))))
   (fn (iota n) (iota-recur 0 n))

   (fn (sum l)
       (if (null? l) 0
           (+ (car l) (sum (cdr l)))))

   (fn (double x) (+ x x))
   (fn (display x) (print x))

   (fn (mul a b) (= s 0)
       (while (< 0 a) (-= a 1) (+= s b)))
   (fn (div a b) (= s 0)
       (while (<= b a) (-= a b) (+= s 1)))
   (fn (mod a b) (- a (mul b (div a b))))

   (fn (even? x) (== 0 (mod x 2)))

   (fn (main) (malloc-init)
       (sum (map (:fn-addr double)
                 (filter (:fn-addr even?)
                         (iota 10))))))
 '()
 (λ (asm registers ram)
   (= 40 (read-register registers 'ret))))
