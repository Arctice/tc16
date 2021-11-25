#!chezscheme
(define-syntax λ (identifier-syntax lambda))
(pretty-one-line-limit 40)

(define enable-tail-calls (make-parameter #t))
(define enable-inlining (make-parameter #t))
(define enable-optimizations (make-parameter #t))
(define enable-fuse-lifetimes (make-parameter #t))
(define ram-size (make-parameter 1024))

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
;;    op: one of add, sub, neg, inc, dec, xor, or, and, not
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
;; 15 [nconst | i: 12-bit immediate] (- i) -> const

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

(define (register-name name)
  (case name
    [zero 0] [ip 1] [const 2] [cond 3]
    [stack 4] [frame 5] [ret 6] [overflow 7]
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
    (printf "RAM 16-bit x~s\n" size)
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
         [ram (make-bytevector (* (ram-size) 2) 0)]
         [cycles 0])
    (define (write-register r val)
      (when (not (eq? r 'zero))
        (bytevector-u16-native-set! registers (* 2 (register-name r)) val)))

    (for-each
     (λ (v n) (bytevector-u16-native-set! ram (* 2 n) v))
     data (enumerate data))

    (let exec ()
      (let* ([ip (read-register registers 'ip)]
             [instr (vector-ref instructions ip)])
        (set! cycles (+ 1 cycles))
        ;; (printf "~4s: ~s \n" ip instr)

        (record-case
         instr
         [const (n) (assert (>= 12 (fxlength n)))
                (write-register 'const n)]
         [nconst (n) (assert (>= 12 (fxlength n)))
                 (write-register 'const
                                 (fxand #xffff (fx+ 1 (fxxor n #xffff))))]
         [mov (mode a b) (assert (member mode '(y cond)))
              (let* ([true (= 1 (fxand 1 (read-register registers 'cond)))]
                     [condition (or (eq? mode 'y) true)])
                (when condition (write-register a (read-register registers b))))]

         [store (a r)
                (let ([addr (read-register registers a)]
                      [val (read-register registers r)])
                  (assert (< addr (ram-size)))
                  (bytevector-u16-native-set! ram (* 2 addr) val))]

         [load (r a)
               (let ([addr (read-register registers a)])
                 (assert (< addr (ram-size)))
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
                        [dec (λ (x _) (fx- x 1))]
                        [xor fxxor] [or fxior] [and fxand]
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

         [assert-equal
          (a b) (when (not (equal? (read-register registers a)
                                   (read-register registers b)))
                  (print-registers registers)
                  (print-memory ram)
                  (error "assert-equal" "vm assertion failure"))]

         [else (error "vm" (format "unknown op ~s" (car instr)))]))
      (write-register 'ip (+ 1 (read-register registers 'ip)))
      (when (< (read-register registers 'ip) (vector-length instructions))
        (exec)))

    (values registers ram cycles)))



(define (binary instructions)
  (define (reg-args a b)
    (fxior (fxsll (register-name a) 4)
           (register-name b)))
  (map
   (λ (instr)
     (record-case
      instr
      [const (n) (assert (>= 12 (fxlength n))) n]
      [nconst (n) (assert (>= 12 (fxlength n)))
              (fxior (fxsll #b1111 12)
                     (fxand #b0000111111111111
                            (fx+ 1 (fxxor n #xffff))))]
      [mov (mode a b) (assert (member mode '(y cond)))
           (fxior (fxsll #b0001 12)
                  (fxsll (case mode [y 1] [cond 0]) 8)
                  (reg-args a b))]
      [store (a r) (fxior (fxsll #b0010 12)
                          (reg-args a r))]

      [load (r a) (fxior (fxsll #b0011 12)
                         (reg-args r a))]

      [alu (op a b)
           (fxior (fxsll #b0100 12)
                  (fxsll (case op
                           [add 0] [sub 1] [inc 2] [dec 3] [neg 4]
                           [xor 5] [or 6] [and 7] [not 8])
                         8)
                  (reg-args a b))]

      [cmp (op a b)
           (fxior (fxsll #b0111 12)
                  (fxsll (case op
                           [zero 0] [eq 1] [neq 2]
                           [less 3] [less-or-eq 4])
                         8)
                  (reg-args a b))]

      [shift (direction a b)
             (assert (member direction '(l r)))
             (fxior (fxsll #b1010 12)
                    (fxsll (case direction [l 0] [r 1]) 8)
                    (reg-args a b))]

      [flip (a b) (fxior (fxsll #b1011 12)
                         (reg-args a b))]

      [else (error "bin" (format "unknown op ~s" (car instr)))]))

   instructions))


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
             (λ (k v) (symbol-hashtable-set! symbol-table k v))
             (hashtable-keys (environment-symbols new-scope))
             (hashtable-values (environment-symbols new-scope)))
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
       (let*-values ([(ir add) (builtin-ir env ir '+ (reverse args))])
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
       (let-values ([(ir a) (reify-consts ir (car args))])
         (let* ([b (cadr args)]
                [code `((store ,a ,b))])
           (values (append code ir) a)))]
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
       (let* ([fn (car args)]
              [val (symgen (format "f-~s" fn))])
         (values (append `((value ,val (fn-addr ,fn))) ir)
                 val))]
      [else (error "macro-ir" (format "unknown macro ~s" name))]))

  (define (reify-consts ir val)
    (if (and (pair? val) (eq? 'const-ref (car val)))
        (let* ([val (cadr val)]
               [var (symgen (format "const<~s>" val))]
               [code `((value ,var (const ,val)))])
          (values (append code ir) var))
        (values ir val)))

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

     [(number? expr) (values ir `(const-ref ,expr))]

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
                 [arg-names (caddr expr)]
                 [args
                  (map
                   (λ (arg position)
                     (let* ([name (symbol->string arg)]
                            [name (substring name 1 (string-length name))]
                            [var (symgen (format "arg-~o" name))])
                       (symbol-hashtable-set! env arg var)
                       `(fn-arg ,var ,position)))
                   arg-names (enumerate arg-names))]
                 [arg-values (map cadr args)]
                 [body (cadddr expr)]
                 [ir (cons `(function ,name ,arg-values) ir)]
                 [ir (append (reverse args) ir)]
                 [ir (cons `(function-body ,arg-values) ir)])
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
                (let*-values
                    ([[false-expr] (car false-expr)]
                     [(ir) (cons `(def ,if-val) ir)]
                     [(ir test) (descend env ir condition)]
                     [(ir) (cons `(branch ,test ,if-true) ir)]
                     [(ir false-ret) (descend env ir false-expr)]
                     [(ir _) (builtin-ir env ir '= (list if-val false-ret))]
                     [(ir) (cons `(jump ,if-end) ir)]
                     [(ir) (cons `(label ,if-true) ir)]
                     [(ir true-ret) (descend env ir true-expr)]
                     [(ir _) (builtin-ir env ir '= (list if-val true-ret))]
                     [(ir) (cons `(label ,if-end) ir)])
                  (values ir if-val))))]

         [(memq form '(call addr-call))
          (let ([function (caddr expr)]
                [args (cdddr expr)]
                [tail? (cadr expr)])
            (let eval-args ([args args] [arg-values '()] [arg-ir '()])
              (if (not (null? args))
                  (let*-values ([(arg-ir val) (descend env arg-ir (car args))]
                                [(arg-ir val) (reify-consts arg-ir val)])
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

  (for-each (λ (instr line)
              (when (eq? (car instr) 'label)
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
        (when (not (and (pair? var) (eq? 'const-ref (car var))))
          (hashtable-update!
           lifetimes line
           (λ (live-vars)
             (if (member var live-vars) live-vars
                 (cons var live-vars))) '())))
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
       [function (name args) (map definition args)]
       [function-body (args) (map use args)]
       [fn-arg (arg _) (use arg)]
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

(define (asm-register-allocation lifetimes asm)
  (define registers (make-eqv-hashtable))
  (define variables (make-hashtable symbol-hash symbol=?))

  (define local-vars-referenced (make-hashtable symbol-hash symbol=?))
  (define inline-stack '())

  (define (cleanup-inline-locals f)
    (let ([a '()])
      (for-each
       (λ (var)
         (let ([stored (symbol-hashtable-ref variables var #f)])
           (when stored
             (symbol-hashtable-delete! variables var)
             (when (eq? var (hashtable-ref registers stored 'nil))
               (hashtable-delete! registers stored)))))
       (symbol-hashtable-ref local-vars-referenced f '()))
      a))
  (define (enter-inline! fn ir-line)
    (let ([live-vars
           (hashtable-ref
            (symbol-hashtable-ref lifetimes fn (void))
            ir-line '())])
      (set! inline-stack (cons (cons* fn ir-line) inline-stack))
      '()
      ))
  (define (leave-inline! fn inlined-function)
    (set! inline-stack (cdr inline-stack))
    (cleanup-inline-locals inlined-function))


  (define (live fn line)
    (append
     (fold-left append '()
                (map (λ (inline-context)
                       (hashtable-ref
                        (symbol-hashtable-ref
                         lifetimes (car inline-context) (void))
                        (cdr inline-context) '()))
                     inline-stack))
     (hashtable-ref (symbol-hashtable-ref lifetimes fn (void))
                    line '())))

  (define (evictable fn line)
    (append
     (fold-left append '()
                (map (λ (inline-context)
                       (hashtable-ref
                        (symbol-hashtable-ref
                         lifetimes (car inline-context) (void))
                        (+ 1 (cdr inline-context)) '()))
                     inline-stack))
     (hashtable-ref (symbol-hashtable-ref lifetimes fn (void))
                    (+ 1 line) '())))


  (define next-free-register
    (if lifetimes
        (λ (fn ir-line)
          (let ([live-variables (live fn ir-line)])
            (let scan ([r 0])
              (let ([stored-var (hashtable-ref registers r 'nil)])
                (if (memq stored-var live-variables)
                    (scan (+ r 1)) r)))))
        (let ([id 0])
          (λ _ (set! id (+ 1 id)) id))))

  (define (reference! fn ir-line var)
    (cond
     [(and (pair? var) (eq? (car var) 'const-ref)) var]
     [else
      (symbol-hashtable-update! local-vars-referenced fn
                                (λ (vars) (cons var vars)) '())
      (let ([stored (symbol-hashtable-ref variables var #f)])
        (if stored `(ref ,stored)
            (let ([register (next-free-register fn ir-line)])
              (symbol-hashtable-delete!
               variables (hashtable-ref registers register 'nil))
              (hashtable-set! registers register var)
              (symbol-hashtable-set! variables var register)
              `(ref ,register))))]))

  (define (fuse-lifetimes line)
    (if (or (not (enable-fuse-lifetimes))
            (not (and (eq? 'mov (car line)) (eq? 'y (cadr line))))) #f
            (let* ([refs (cddr line)]
                   [a (car refs)] [b (cadr refs)]
                   [is-def (and (pair? a) (eq? 'def (car a)))]
                   [from-var (and (pair? b) (eq? 'ref (car b))
                                  (not (pair? (cadr b))))])
              (if (not (and is-def from-var)) #f
                  (let* ([fn-a (list-ref a 2)]
                         [fn-b (list-ref b 2)]
                         [ir-line-a (list-ref a 3)]
                         [ir-line-b (list-ref b 3)]
                         [val-dies
                          (not (memq (cadr b) (evictable fn-b ir-line-b)))]
                         [new-def
                          (not (memq (cadr a) (live fn-a (- ir-line-a 1))))])
                    (if (not (and new-def val-dies)) #f
                        (let* ([var (cadr a)]
                               [ref (reference! fn-b ir-line-b (cadr b))]
                               [is-inline (not (eq? fn-a fn-b))])
                          (hashtable-set! registers (cadr ref) var)
                          (symbol-hashtable-set! variables var (cadr ref))
                          (list `(mov y ,ref ,ref)))))))))

  (define (allocate-refs line)
    (let* ([ref-indices
            (filter (λ (index)
                      (let ([word (list-ref line index)])
                        (and (pair? word)
                             (memq (car word) '(def ref)))))
                    (enumerate line))]
           [refs (map (λ (index) (list-ref line index)) ref-indices)]
           [refs
            (map (λ (ref) ;; resolve refs
                   (if (eq? 'def (car ref)) ref
                       (let* ([var (cadr ref)]
                              [location (cddr ref)]
                              [fn (car location)]
                              [line (cadr location)])
                         (reference! fn line var))))
                 refs)]
           [refs
            (map (λ (ref) ;; resolve defs
                   (if (not (eq? 'def (car ref))) ref
                       (let* ([var (cadr ref)]
                              [location (cddr ref)]
                              [fn (car location)]
                              [line (cadr location)])
                         `(def ,(cadr (reference! fn line var))))))
                 refs)]
           [line
            (let merge-refs ([line line] [index 0]
                             [refs refs] [ref-indices ref-indices])
              (cond [(null? refs) line]
                    [(null? line) line]
                    [(= index (car ref-indices))
                     (cons (car refs)
                           (merge-refs (cdr line) (+ 1 index)
                                       (cdr refs) (cdr ref-indices)))]
                    [else
                     (cons (car line)
                           (merge-refs (cdr line) (+ 1 index)
                                       refs ref-indices))]))])
      (append (list line))))

  (define (live-registers fn line)
    (map (λ (var) (symbol-hashtable-ref variables var (void)))
         (filter (λ (var) (symbol-hashtable-contains? variables var))
                 (live fn line))))

  (define call-saved '())

  (let scan ([asm asm])
    (if (null? asm) '()
        (let* ([line (car asm)])
          (case (car line)
            [inline
             (enter-inline! (cadr line) (caddr line))
             (scan (cdr asm))]
            [inline-end
             (let ([x (leave-inline! (cadr line) (caddr line))])
               (append x (scan (cdr asm))))]
            [register-argument
             (let* ([register (cadr line)]
                    [var (caddr line)])
               (hashtable-set! registers register var)
               (symbol-hashtable-set! variables var register)
               (scan (cdr asm)))]
            [call-save-registers
             (let* ([fn (cadr line)] [ir-line (caddr line)]
                    [live-variables (live-registers fn ir-line)]
                    [save
                     `((comment ,(format
                                  "call-save ~s ~s"
                                  live-variables
                                  (map (λ (r) (hashtable-ref registers r #f))
                                       live-variables)))
                       (call-save-registers . ,live-variables))])
               (set! call-saved live-variables)
               (append save (scan (cdr asm))))]
            [call-restore-registers
             (cons `(call-restore-registers . ,call-saved)
                   (scan (cdr asm)))]
            [else
             (let ([line
                    (or (fuse-lifetimes line)
                        (allocate-refs line))])
               (append line (scan (cdr asm))))])))))

(define (asm-register-assignment asm)
  (define registers-only #f)
  (define spill-retry #f)
  (define spill-slots '((v6 . #f) (v7 . #f)))
  (define (evict-spills!)
    (set! spill-slots (map (λ (slot) (cons* (car slot) #f))
                           spill-slots)))
  (define (spill-reuse! var)
    (when registers-only (spill-retry))
    (let ([recent-use
           (find (λ (slot) (eqv? var (cdr slot))) spill-slots)])
      (if (not recent-use) #f
          (begin (set! spill-slots (cons recent-use
                                         (remq recent-use spill-slots)))
                 (car recent-use)))))
  (define (spill-restore! var)
    (when registers-only (spill-retry))
    (or (spill-reuse! var)
        (let* ([cutoff (- (length spill-slots) 1)]
               [evicted (list-ref spill-slots cutoff)])
          (set! spill-slots (cons (cons* (car evicted) var)
                                  (list-head spill-slots cutoff)))
          (car evicted))))

  (define highest-frame-offset 0)

  (define max-direct-registers (- 7 (length spill-slots)))
  (define (spill-frame-offset r)
    (when registers-only (spill-retry))
    (let ([position (- r max-direct-registers)])
      (set! highest-frame-offset (max position highest-frame-offset))
      position))
  (define (direct-register var)
    (if (< max-direct-registers var) #f
        (string->symbol (format "v~s" var))))

  (define (scan asm)
    (cond
     [(null? asm)
      '()]
     [(eq? (caar asm) 'comment)
      (cons (car asm) (scan (cdr asm)))]
     [(eq? (caar asm) 'label)
      ;; might jump here, evict volatile registers
      (evict-spills!)
      (cons (car asm) (scan (cdr asm)))]

     [(eq? (caar asm) 'write)
      (let ([var (cadar (cdar asm))])
        (if (direct-register var)
            (scan (cdr asm))
            (let* ([addr (spill-frame-offset var)]
                   [register (spill-reuse! var)])
              (if (not register)
                  (scan (cdr asm))
                  (append `((nconst ,addr)
                            (alu add const frame)
                            (store const ,register))
                          (scan (cdr asm)))))))]

     [(eq? (caar asm) 'call-save-registers)
      (let ([live (cdr (car asm))])
        (append
         (fold-left
          append '()
          (map (λ (r)
                 (let ([vx (direct-register r)])
                   (if (not vx) '()
                       `((alu dec stack zero) (store stack ,vx)))))
               live))
         (scan (cdr asm))))]

     [(eq? (caar asm) 'call-restore-registers)
      (let ([live (cdr (car asm))])
        (append
         (fold-left
          append '()
          (map (λ (r)
                 (let ([vx (direct-register r)])
                   (if (not vx) '()
                       `((load ,vx stack) (alu inc stack zero)))))
               (reverse live)))
         (scan (cdr asm))))]

     [(eq? (caar asm) 'call-register-arguments)
      (let* ([args (cdr (car asm))]
             [args (map cadr args)]
             [moved (make-vector 1024 #f)]
             [stored (make-vector 1024 #f)])
        (for-each (λ (r) (vector-set! stored r r)) args)
        (append
         (fold-left
          (λ (asm current expected)
            (append
             asm
             (if (= current expected) '()
                 (let* ([A (or (vector-ref moved current) current)]
                        [A-direct (direct-register A)]
                        [B (vector-ref stored expected)]
                        [A-available
                         (or A-direct (spill-reuse! A))]
                        [A-load
                         (if A-available '()
                             (let* ([addr (spill-frame-offset A)]
                                    [register (spill-restore! A)])
                               `((nconst ,addr)
                                 (alu add const frame)
                                 (load ,register const))))]
                        [A-pos (or A-direct (spill-reuse! A))])
                   (cond
                    [(not B)
                     (vector-set! stored A #f)
                     (append
                      A-load
                      `((mov y ,(direct-register expected) ,A-pos)))]
                    [B
                     (vector-set! moved B A)
                     (vector-set! stored A B)
                     (append
                      A-load
                      ;; swap registers, use a spill register as a tmp
                      (let ([tmp-register (spill-restore! -1)])
                        `((mov y ,tmp-register ,(direct-register expected))
                          (mov y ,(direct-register expected) ,A-pos)
                          (mov y ,A-pos ,tmp-register)))
                      ;; if A didn't need a load, emit the address
                      (if A-available '()
                          (let* ([addr (spill-frame-offset A)]
                                 [register (spill-reuse! A)])
                            `((nconst ,addr)
                              (alu add const frame))))
                      ;; write B back to A's former spill memory
                      (if A-direct '() `((store const A-pos))))])
                   ))))
          '() args (enumerate args))

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
                       `((nconst ,addr)
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

  (let* ([try-direct-only (call/cc (λ (cc) (λ () (cc #f))))]
         [asm
          (if try-direct-only
              (fluid-let ([max-direct-registers 7]
                          [registers-only #t]
                          [spill-retry try-direct-only])
                (scan asm))
              (scan asm))])
    (subst highest-frame-offset ':frame-size asm)))


(define (asm-load-consts asm)
  (if (null? asm) '()
      (let* ([instruction (car asm)]
             [const-ref
              (find
               (λ (x) (and (pair? x) (eq? 'const-ref (car x))))
               instruction)])
        (append
         (if (not const-ref) (list instruction)
             (let ([val (cadr const-ref)])
               (cond
                [(eq? 0 val)
                 (list (subst 'zero const-ref instruction))]
                [(and (number? val) (> 0 val))
                 (list `(nconst ,(abs (cadr const-ref)))
                       (subst 'const const-ref instruction))]
                [else
                 (list `(const ,(cadr const-ref))
                       (subst 'const const-ref instruction))])))
         (asm-load-consts (cdr asm))))))

(define (asm-remove-unused-labels asm)
  (let* ([labels '()]
         [uses (make-hashtable string-hash string=?)])
    (for-each
     (λ (instr)
       (case (car instr)
         [label (set! labels (cons (cadr instr) labels))]
         [const (when (string? (cadr instr))
                  (hashtable-set!
                   uses (cadr instr) #t))]))
     asm)
    (let scan ([asm asm])
      (cond [(null? asm) '()]
            [(eq? 'label (caar asm))
             (if (hashtable-ref uses (cadr (car asm)) #f)
                 (cons (car asm) (scan (cdr asm)))
                 (scan (cdr asm)))]
            [else (cons (car asm) (scan (cdr asm)))]))))

(define (asm-remove-unreachable-code asm)
  (let scan ([asm asm] [alive #t])
    (cond [(null? asm) '()]
          [(eq? 'label (caar asm))
           (cons (car asm) (scan (cdr asm) #t))]
          [(not alive) (scan (cdr asm) alive)]
          [(and (eq? 'mov (caar asm))
                (equal? (list-head (car asm) 3)
                        '(mov y ip)))
           (cons (car asm) (scan (cdr asm) #f))]
          [else (cons (car asm) (scan (cdr asm) alive))])))


(define (asm-pattern-optimizations asm)
  (define patterns
    '(

      (((alu sub "_" zero)) . ())
      (((alu add "_" zero)) . ())

      (((mov y "a" "a")) . ())
      (((mov y "a" "b") (mov y "a" "b")) . ((mov y "a" "b")))
      (((mov y "a" "b") (mov y "b" "a")) . ((mov y "a" "b")))

      (((mov y "b" "a") (const "x") (alu add "b" const) (load "b" "b"))
       . ((const "x") (alu add const "a") (load "b" const)))

      (((mov y "b" "a") (load "b" "b")) . ((load "b" "a")))

      (((const "a") (mov y ip const) (label "a")) . ((label "a")))

      (((const "t") (mov cond ip const)
        (const "f") (mov y ip const) (label "t"))
       . ((cmp eq zero cond) (const "f")
          (mov cond ip const) (label "t")))

      (((const 1) (alu sub "a" const)) . ((alu dec "a" zero)))
      (((const 1) (alu add "a" const)) . ((alu inc "a" zero)))

      (((mov y "b" "a") (alu add "b" "c") (mov y "a" "b"))
       . ((alu add "a" "c") (mov y "b" "a")))

      (((mov y "b" "a") (alu sub "b" "c") (mov y "a" "b"))
       . ((alu sub "a" "c") (mov y "b" "a")))

      (((mov y "a" "b") (alu add "a" "c") (mov y "c" "a"))
       . ((alu add "c" "b") (mov y "a" "c")))

      (((mov y "a" "z") (cmp "op" "a" "b") (mov y "a" cond))
       . ((cmp "op" "z" "b") (mov y "a" cond)))

      (((mov y cond "a") (cmp "op" cond "b") (mov y "b" cond))
       . ((cmp "op" "a" "b") (mov y "b" cond)))

      (((mov y "b" "a") (alu inc "b" zero) (mov y "a" "b"))
       . ((alu inc "a" zero) (mov y "b" "a")))

      (((mov y "b" "a") (const "x") (cmp "op" "b" "c") (mov y "b" cond))
       . ((const "x") (cmp "op" "a" "c") (mov y "b" cond)))

      ))
  (define (try-match pattern asm)
    (define vars (make-hashtable string-hash string=?))
    (let scan ([asm asm]
               [pattern pattern])
      (cond
       [(null? pattern) vars]
       [(null? asm) #f]
       [(eq? 'comment (caar asm))
        (scan (cdr asm) pattern)]
       [(not (= (length (car asm)) (length (car pattern)))) #f]
       [else
        (and (for-all
              (λ (asm match)
                (cond
                 [(eq? asm match) #t]
                 [(string? match)
                  (let ([previous (hashtable-ref vars match #f)])
                    (if previous (equal? previous asm)
                        (begin (hashtable-set! vars match asm) #t)))]
                 [else #f]))
              (car asm) (car pattern))
             (scan (cdr asm) (cdr pattern)))])))
  (define (substitute-vars vars pattern)
    (map (λ (inst)
           (map (λ (word) (if (symbol? word) word
                              (hashtable-ref vars word (void))))
                inst))
         pattern))

  (let scan ([asm asm])
    (if (null? asm) '()
        (let ([match (find (λ (pattern) (try-match (car pattern) asm))
                           patterns)])
          (if (not match) (cons (car asm) (scan (cdr asm)))
              (let* ([old (car match)]
                     [new (cdr match)]
                     [substitutions (try-match old asm)]
                     [comments '()]
                     [asm
                      (let drop ([asm asm] [skip (length old)])
                        (cond [(zero? skip) (append comments asm)]
                              [(eq? 'comment (caar asm))
                               (set! comments (append comments (list (car asm))))
                               (drop (cdr asm) skip)]
                              [else (drop (cdr asm) (- skip 1))]))])
                (append (substitute-vars substitutions new)
                        (scan asm))))))))

(define (try-optimize asm)
  (if (not (enable-optimizations)) asm
      (let optimize ([asm asm] [prev-size (length asm)])
        (let* ([asm (asm-remove-unreachable-code asm)]
               [asm (asm-remove-unused-labels asm)]
               [asm (asm-pattern-optimizations asm)]
               [size (length asm)])
          (if (< size prev-size)
              (optimize asm size) asm)))))

(define (function-asm function ir lifetimes)
  (define argument-frame-size)

  (define inline-context #f)
  (define inline-tail-call #t)
  (define inline-stack '())
  (define label-prefix "")
  (define inline-fail)
  (define function-references '())

  (define asm '())
  (define (emit! code)
    (set! asm (append (reverse code) asm)))

  (define (ref! fn ir-line var)
    `(ref ,var ,fn ,ir-line))
  (define (def! fn ir-line var)
    `(def ,var ,fn ,ir-line))

  (define (approx-code-length code)
    (length
     (filter (λ (i) (not (memq (car i) '(comment label))))
             (asm-pattern-optimizations
              (asm-remove-unreachable-code
               (asm-load-consts
                (asm-register-assignment
                 (asm-register-allocation
                  lifetimes (reverse code)))))))))

  (define (builtin fn instr line out-var)
    (record-case
     instr
     [cmp (op a b)
          (let* ([op (case op [== 'eq] [!= 'neq]
                           [< 'less] [<= 'less-or-eq]
                           [(> >= zero) (void)])]
                 [a (ref! fn line a)]
                 [b (ref! fn line b)]
                 [out (def! fn line out-var)])
            (emit! `((mov y ,out ,a)
                     (cmp ,op ,out ,b)
                     (mov y ,out cond))))]

     [load (addr) (let* ([addr (ref! fn line addr)]
                         [out (def! fn (+ 1 line) out-var)])
                    (emit! `((load ,out ,addr))))]

     [fn-addr (function)
              (set! function-references (cons function function-references))
              (emit! `((const ,(function-label function))
                       (mov y ,(def! fn line out-var) const)))]

     [(call addr-call)
      (tail-call function . args)
      (define address-call? (eq? (car instr) 'addr-call))
      (define ret-addr
        (string-append label-prefix
                       (symbol->string (symgen "ret"))))

      (define fast-argument-count (min 6 (length args)))
      (define register-arguments
        (map (λ (var) (ref! fn line var))
             (list-head args fast-argument-count)))
      (define stack-arguments (list-tail args fast-argument-count))
      (define fn-addr
        (if address-call?
            'cond `(const-ref ,(function-label function))))
      (define-values (restore-asm restore-refs)
        (values asm function-references))
      (define (restore)
        (set! asm restore-asm)
        (set! function-references restore-refs))

      (let* ([call-cost (call/cc (λ (cc) (λ (x) (restore) (cc x))))]
             [inline-retry (call/cc (λ (cc) cc))])
        (cond
         [(and (enable-inlining)
               (number? call-cost)
               (< (length inline-stack) 3)
               inline-retry
               (not address-call?)
               (not (find (λ (frame) (eq? frame fn)) inline-stack)))
          (let ([return-var (def! fn line out-var)]
                [args (map (λ (val) (ref! fn line val)) args)])
            (fluid-let
                ([inline-context (cons* return-var ret-addr args)]
                 [label-prefix (symbol->string (symgen function))]
                 [inline-stack (cons (cons* fn line) inline-stack)]
                 [inline-tail-call (and inline-tail-call tail-call)]
                 [inline-fail (λ () (restore) (inline-retry #f))])
              (emit! `((comment ,(format "inline ~s" function))
                       (inline ,fn ,line)))
              (next function (symbol-hashtable-ref ir function #f) 0)
              (emit! `((label ,ret-addr)
                       (inline-end ,fn ,function)))
              (when (< call-cost
                       (- (approx-code-length asm)
                          (approx-code-length restore-asm)))
                (inline-fail))))]

         [(and tail-call inline-tail-call (enable-tail-calls))
          ;; argument shuffle:
          ;; first copy out the 'safe' arguments that fit below current frame
          ;; write the rest to the top of the stack in reverse order
          ;; copy those back while growing the frame
          ;; finally move the stack to the beginning of the argument section
          (when address-call?
            (emit! `((mov y cond ,(ref! fn line function)))))

          (let* ([args (map (λ (var) (ref! fn line var))
                            stack-arguments)]
                 [safe-args-count
                  (min argument-frame-size (length args))]
                 [stack-args-count (- (length args) safe-args-count)])
            (emit! `((comment ,(format "tail-call safe ~s stack ~s"
                                       safe-args-count stack-args-count))))

            ;; temporarily use ret as a argument section pointer
            (when (not (zero? safe-args-count))
              (emit! `((alu dec stack zero) (store stack ret)
                       (mov y ret frame)
                       (const ,argument-frame-size)
                       (alu add ret const)))
              (for-each
               (λ (ref) (emit! `((alu dec ret zero)
                                 (store ret ,ref))))
               (list-head args safe-args-count))
              (emit! `((load ret stack) (alu inc stack zero))))

            (when (not (zero? stack-args-count))
              (for-each
               (λ (ref) (emit! `((alu dec stack zero) (store stack ,ref))))
               (list-tail args safe-args-count)))

            (emit! `((call-register-arguments . ,register-arguments)))

            (when (not (zero? stack-args-count))
              (emit!
               `((alu add stack (const-ref ,stack-args-count))))
              (for-each
               (λ (_) (emit! `((alu dec stack zero) (load v7 stack)
                               (alu dec frame zero) (store frame v7))))
               (iota stack-args-count)))

            (when (< (length args) argument-frame-size)
              ;; shrink the frame
              (emit! `((const ,(- argument-frame-size (length args)))
                       (alu add frame const))))

            (emit! `((mov y stack frame)
                     (alu add stack (const-ref ,(length args)))))
            (emit! `((mov y ip ,fn-addr)))

            (when (and (enable-inlining)
                       (not (number? call-cost)))
              (call-cost (- (approx-code-length asm)
                            (approx-code-length restore-asm))))
            (when (not address-call?)
              (set! function-references (cons function function-references))))]

         [else
          (when address-call?
            (emit! `((mov y cond ,(ref! fn line function)))))
          ;; save ret, frame
          (emit! `((alu dec stack zero)
                   (store stack ret)
                   (alu dec stack zero)
                   (store stack frame)
                   ;; save registers v0-v7
                   (call-save-registers ,fn ,(+ line 1))))

          ;; stack arguments
          (when (not (null? stack-arguments))
            ;; save this stack position for reading off the arguments later
            (emit! `((mov y ret stack)))
            (for-each
             (λ (arg position)
               (let ([var (ref! fn line arg)])
                 (emit! `((alu dec stack zero) (store stack ,var)))))
             stack-arguments (enumerate stack-arguments)))

          (emit! `(;; arrange the fast arguments
                   (call-register-arguments . ,register-arguments)
                   ;; advance to the new frame position
                   (mov y frame stack)))

          (when (not (null? stack-arguments))
            ;; stack <- argument section
            (emit! `((mov y stack ret))))

          (emit! `(;; ret <- here (ip)
                   (const ,ret-addr) (mov y ret const)
                   ;; load fn address, jump
                   (mov y ip ,fn-addr)
                   ;; return point
                   (label ,ret-addr)))

          (let ([out (def! fn line out-var)])
            (emit! `(;; out <- return value
                     (mov y ,out v0)
                     ;; restore registers v0-v7
                     (call-restore-registers ,fn ,(+ 1 line))
                     ;; restore previous frame
                     (load frame stack) (alu inc stack zero)
                     ;; restore ret
                     (load ret stack) (alu inc stack zero))))

          (when (and (enable-inlining)
                     (not (number? call-cost)))
            (call-cost (- (approx-code-length asm)
                          (approx-code-length restore-asm))))

          (when (not address-call?)
            (set! function-references (cons function function-references)))

          ]))]

     [const (value) (let* ([out (def! fn line out-var)])
                      (emit! `((mov y ,out (const-ref ,value)))))]
     [+ (a b)
        (let* ([a (ref! fn line a)]
               [b (ref! fn line b)]
               [out (def! fn line out-var)])
          (emit! `((mov y ,out ,a)
                   (write ,out)
                   (alu add ,out ,b))))]

     [- (a b)
        (let* ([a (ref! fn line a)]
               [b (ref! fn line b)]
               [out (def! fn line out-var)])
          (emit! `((mov y ,out ,a)
                   (write ,out)
                   (alu sub ,out ,b))))]

     [else (error "asm" (format "unknown builtin ~s" instr))]))

  (define (next fn ir line)
    (when (not (null? ir))
      (let ([instr (car ir)])
        (emit! `((comment ,(format "~s ~s: ~s" fn line instr))))

        (record-case
         instr
         [set (var val) (let* ([val (ref! fn line val)]
                               [var (def! fn (+ 1 line) var)])
                          (emit! `((mov y ,var ,val)
                                   (write ,var))))]
         [def () (void)]

         [value (var instr) (builtin fn instr line var)
                (emit! `((write ,(def! fn line var))))]

         [store (addr val) (let* ([val (ref! fn line val)]
                                  [addr (ref! fn line addr)])
                             (emit! `((store ,addr ,val))))]

         [branch (condition jump)
                 (let ([test (ref! fn line condition)])
                   (emit! `((mov y cond ,test)
                            (const ,(string-append
                                     label-prefix (symbol->string jump)))
                            (mov cond ip const))))]

         [jump (jump)
               (emit! `((const ,(string-append
                                 label-prefix (symbol->string jump)))
                        (mov y ip const)))]

         [label (id)
                (emit! `((label ,(string-append
                                  label-prefix (symbol->string id)))))]

         [function
          (name args)
          (when (not inline-context)
            (set! argument-frame-size (- (length args) (min (length args) 6)))
            (emit! `((label ,(function-label name)))))]

         [fn-arg
          (var position)
          (if (not inline-context)
              (if (< position 6)
                  (emit! `((register-argument ,position ,var)))
                  (let ([val (def! fn line var)])
                    (emit! `((alu dec stack zero)
                             (load ,val stack)
                             (write ,val)))))
              (let* ([inline-args (cddr inline-context)]
                     [val (list-ref inline-args position)]
                     [var (def! fn line var)])
                (emit! `((mov y ,var ,val)
                         (write ,var)))))]

         [function-body
          (_) (when (not inline-context)
                (emit! '((alu sub stack (const-ref :frame-size)))))]

         [return (var)
                 (let* ([val (ref! fn line var)])
                   (if (not inline-context)
                       (emit! `(;; restore caller's stack
                                ;; pop the stack arguments
                                (mov y v0 ,val)
                                (mov y stack frame)
                                (alu add stack (const-ref ,argument-frame-size))
                                (mov y ip ret)))
                       (emit! `((mov y ,(car inline-context) ,val)
                                (write ,(car inline-context))
                                (const ,(cadr inline-context))
                                (mov y ip const)))))]

         [print (x) (emit! `((print ,(ref! fn line x))))]

         [else (error "asm" (format "unknown ir form ~s" instr))]))

      (next fn (cdr ir) (+ line 1))))

  (next function (symbol-hashtable-ref ir function #f) 0)
  (cons* (reverse asm) function-references))

(define (generate-asm ir)
  (define (ir-fn-name fn) (cadr (car fn)))
  (let* ([names (map ir-fn-name ir)]
         [functions (make-hashtable symbol-hash symbol=?)]
         [lifetimes (make-hashtable symbol-hash symbol=?)]
         [_ (for-each
             (λ (name ir)
               (symbol-hashtable-set! functions name ir)
               (symbol-hashtable-set! lifetimes name (lifetime-analysis ir)))
             names ir)]
         [fn-asm
          (let scan-call-graph ([queue '(main)] [seen '()])
            (let* ([name (car queue)]
                   [asm (function-asm name functions lifetimes)]
                   [calls (cdr asm)] [asm (car asm)]
                   [seen (cons name seen)]
                   [calls (filter (λ (fn) (not (memq fn seen))) calls)]
                   [calls
                    (fold-left (λ (calls fn)
                                 (if (memq fn calls) calls (cons fn calls)))
                               '() calls)]
                   [queue (append (cdr queue) calls)]
                   [seen (append calls seen)]
                   [asm (asm-register-allocation lifetimes asm)]
                   [asm (asm-register-assignment asm)]
                   [asm (asm-load-consts asm)]
                   [asm (if (not (enable-optimizations)) asm
                            (asm-pattern-optimizations asm))])
              (cons asm (if (null? queue) '()
                            (scan-call-graph queue seen)))))]
         [asm (fold-left append '() fn-asm)]
         [asm (append
               `((comment 'init)
                 (const ".halt")
                 (mov y ret const)
                 (const ,(ram-size))
                 (mov y frame const)
                 (mov y stack const)
                 (const ,(function-label 'main))
                 (mov y ip const))
               asm
               '((label ".halt")))]
         [asm (try-optimize asm)])
    asm))


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
           (printf ";; ~x\n" (cadr (car asm)))
           (next-line (cdr asm) line)]
          [(eq? (caar asm) 'label)
           (printf " ~x:\n" (cadr (car asm)))
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
    (printf "~o\n" result)

    ;; (print-asm asm)
    ;; (for-each
    ;;  (λ (a b)
    ;;    (printf "~16,b ~s\n" b a))
    ;;  bin (binary bin))

    ;; (for-each (λ (i) (printf "~6s\n" (fxand #xff i)))
    ;;           (binary bin))
    ;; (printf "\n")
    ;; (for-each (λ (i) (printf "~6s\n" (fxsrl i 8)))
    ;;           (binary bin))

    (let-values ([(registers ram cycles) (vm bin data)])
      (set! result
            (string-append
             (format "~25a" "")
             (format "~8s" cycles)
             (format "~8o  " (format "~3,1f%" (* 100. (memory-usage ram))))))
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
    (- 1 (/ longest-run size))))

(run-l5 "expr"
        '((fn (main)
              (= a 13)
              (= b 5)
              (= c 12)
              (- (+ (+ a c) (- b b)) b)))
        '()
        (λ (asm registers ram)
          (= 20 (read-register registers 'v0))))

(run-l5 "reuse"
        '((fn (main)
              (= a 9)
              (+ a (+ 9 9))))
        '()
        (λ (asm registers ram)
          (= 27 (read-register registers 'v0))))

(run-l5 "spill"
        '((fn (main)
              (+ 1 (+ 2 (+ 3 (+ 4 (+ 5 (+ 6 (+ 7 (+ 8 9))))))))))
        '()
        (λ (asm registers ram)
          (= 45 (read-register registers 'v0))))

(run-l5 "control"
        '((fn (main) (if (== 0 1) (prog 1 2)
                         (prog (if (!= 0 1) 4 3)))))
        '()
        (λ (asm registers ram)
          (= 4 (read-register registers 'v0))))

(run-l5 "fncall"
        '((fn (main) (foo 2 3))
          (fn (foo a b) (bar a b 7 11))
          (fn (bar q w e r) (+ q (+ w (+ e (- r 10))))))
        '()
        (λ (asm registers ram)
          (= 13 (read-register registers 'v0))))

(run-l5 "inline"
        '((fn (main) (= a (foo 1)) a)
          (fn (foo a) (= b (bar (+ a 2))) b)
          (fn (bar b) (= c (+ b 3)) c))
        '()
        (λ (asm registers ram)
          (= 6 (read-register registers 'v0))))

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
          (= 28657 (read-register registers 'v0))))

(run-l5 "recursion"
        '((fn (main) (fib (load 0)))
          (fn (fib n)
              (if (< n 2) 1
                  (+ (fib (- n 1))
                     (fib (- n 2))))))
        '(20)
        (λ (asm registers ram)
          (= 10946 (read-register registers 'v0))))

(when (enable-tail-calls)
  (run-l5 "tail-call"
          '((fn (main) (spin 0 4095))
            (fn (spin n x) (if (< n x) (spin (+ n 1) x) n)))
          '() (λ (asm registers ram) (> .01 (memory-usage ram)))))

(run-l5 "arg-spill"
        '((fn (a a0 a1 a2 a3 a4 a5 a6 a7 a8 a9)
              (b a1 a2 a3 a4 a5 a6 a7 a8 a9 a0))
          (fn (b a0 a1 a2 a3 a4 a5 a6 a7 a8 a9)
              (c a1 a2 a3 a4 a5 a6 a7 a8 a9 a0))
          (fn (c a0 a1 a2 a3 a4 a5 a6 a7 a8 a9)
              (d a1 a2 a3 a4 a5 a6 a7 a8 a9 a0))
          (fn (d a0 a1 a2 a3 a4 a5 a6 a7 a8 a9)
              (e a1 a2 a3 a4 a5 a6 a7 a8 a9 a0))
          (fn (e a0 a1 a2 a3 a4 a5 a6 a7 a8 a9)
              (f a1 a2 a3 a4 a5 a6 a7 a8 a9 a0))
          (fn (f a0 a1 a2 a3 a4 a5 a6 a7 a8 a9)
              (g a1 a2 a3 a4 a5 a6 a7 a8 a9 a0))
          (fn (g a0 a1 a2 a3 a4 a5 a6 a7 a8 a9) a1)
          (fn (main)
              (a 0 1 2 3 4 5 6 7 8 9)))
        '()
        (λ (asm registers ram)
          (= 7 (read-register registers 'v0))))

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
          (= 65535 (read-register registers 'v0))))

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
          (= 45 (read-register registers 'v0))))

(run-l5
 "cmp"
 '((fn (zero? p) (== p 0))
   (fn (main) (zero? 0)))
 '()
 (λ (asm registers ram) (= 1 (read-register registers 'v0))))


(run-l5
 "gc"
 `((fn (nil? p) (== 0 p))

   (fn (mmb-metadata-size) 3)
   (fn (mmb-next p) (load p))
   (fn (mmb-next-set! p addr) (store p addr))
   (fn (mmb-size p) (load (+ p 1)))
   (fn (mmb-size-set! p v) (store (+ p 1) v))
   (fn (mmb-reachable p) (load (+ p 2)))
   (fn (mmb-reachable-set! p s) (store (+ p 2) s))

   (fn (mmb-data p) (+ p 3))
   (fn (mmb-past p) (+ (mmb-data p) (mmb-size p)))

   (fn (mmb-create! addr size)
       (mmb-next-set! addr 0)
       (mmb-size-set! addr size)
       (mmb-reachable-set! addr -1))

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
                 (if (<= (+ (mmb-metadata-size) size) gap) p
                     (malloc-find-space next size)))))

   (fn (malloc size)
       (= at (malloc-find-space 0 size))
       (= new (mmb-past at))
       (mmb-create! new size)
       (mmb-next-set! new (mmb-next at))
       (mmb-next-set! at new)
       (return (+ (mmb-metadata-size) new)))

   (fn (free p)
       (mmb-reachable-set! p 0)
       (= p (- p (mmb-metadata-size)))
       (if (nil? p) (return 0) (prog 0))
       (= prev (mmb-find-parent 0 p))
       (mmb-next-set! prev (mmb-next p))
       1)

   (fn (boehm-reset-reachability root)
       (= next (mmb-next root))
       (if (nil? next) 0
           (prog (mmb-reachable-set! next 0)
                 (boehm-reset-reachability next))))
   (fn (boehm-scan-reachable-region block)
       (= a (mmb-data block))
       (= b (mmb-past block))
       (= found 0)
       (while (!= a b)
              (= new (boehm-reachable (load a)))
              (if (== new 0) 0 (= found 1))
              (++ a))
       found)
   (fn (boehm-valid-block block)
       (if (< 2 block)
           (if (< block ,(/ (ram-size) 2)) 1 0) 0))

   (fn (marked-reachable? addr)
       (== (mmb-reachable addr) -1))

   (fn (boehm-reachable-scan root block)
       (if (== root block)
           (if (marked-reachable? block) 0
               (prog
                (mmb-reachable-set! block -1)
                ;; scan for further live pointers
                (boehm-scan-reachable-region block)))
           (if (nil? (mmb-next root)) 0
               (boehm-reachable-scan (mmb-next root) block))))
   (fn (boehm-reachable addr)
       (= block (- addr (mmb-metadata-size)))
       (if (boehm-valid-block block)
           (boehm-reachable-scan 0 block)
           0))
   (fn (munge-stack s k)
       (if (< s 1131) 1131
           (+ k (- k (munge-stack (- s k) k)))))
   (fn (boehm-free-unreachable p)
       (= next (mmb-next p))
       (if (nil? next) 0
           (if (marked-reachable? next)
               (boehm-free-unreachable next)
               (prog (free (+ next (mmb-metadata-size)))
                     (boehm-free-unreachable p)))))
   (fn (boehm-gc)
       (munge-stack 2771 113)
       (= root 0)
       (boehm-reset-reachability 0)
       (mmb-reachable-set! root -1)
       (= stack ,(/ (ram-size) 2))
       (while (< stack ,(ram-size))
              (boehm-reachable (load stack))
              (++ stack))
       (boehm-free-unreachable root))

   (fn (gc-init) (mmb-size-set! 0 2))
   (fn (gc-alloc size)
       (= allocated (+ size (load 4)))
       (store 4 allocated)
       (if (< allocated 128) 0
           (prog (store 4 0)
                 (boehm-gc)))
       (malloc size))

   (fn (nil) (:fn-addr nil))
   (fn (cons x l)
       (= cell (gc-alloc 2))
       (store cell x)
       (store (+ 1 cell) l)
       cell)
   (fn (car l) (load l))
   (fn (cdr l) (load (+ 1 l)))
   (fn (null? l) (== (:fn-addr nil) l))

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

   (fn (waste-space)
       (sum (map (:fn-addr double)
                 (filter (:fn-addr even?)
                         (iota 20)))))

   (fn (main) (gc-init)
       (waste-space)
       (waste-space)
       (waste-space)
       (waste-space)))
 '()
 (λ (asm registers ram)
   (> .8 (memory-usage ram))
   (= 180 (read-register registers 'v0))))
