;;;; SK(I) combinator calculus in Scheme

;;; Features:
;;; - Parsing expression into fully parenthesized tree
;;; - Reduction of the leftmost combinator
;;; - Generating a stream of reductions
;;; - Definition of new variables, implemented through
;;;   a frame adjusted by def statements
;;; - A driver loop that incorporates definitions as commands

;;; Evaluator, streams

(define (sk-driver-loop)
  (newline) (display "SK => ")
  (let ((output (sk-eval (read))))
      (if (equal? output 'quit)
        "Goodbye."
        (begin (newline) 
               (display ";Value: ") 
               (display output) 
               (newline)
               (sk-driver-loop)))))

;; extend definitions to take an optional numeric argument to specify the number of arguments
(define (sk-eval input)
  (cond ((null? input) input)
        ((atom? input) input)
        ((equal? (car input) 'quit)
         'quit)
        ((equal? (car input) 'define)
         (apply define-comb! (cdr input))
         (apply define-macro! (cdr input))
         (cadr input))
        ((equal? (car input) 'defmacro)
         (apply define-macro! (cdr input))
         (cadr input))
        ((equal? (car input) 'defun)
         (let ((comb-exp (decrypt (cons 'lambda (cddr input)))))
           ; (define-comb! (cadr input) comb-exp) [in cases like the y-combinator]
           (define-macro! (cadr input) comb-exp)
           (sk-eval (list 'give-def (cadr input)))))
        ((equal? (car input) 'reset)
         (reset-dict! dictionary))
        ((equal? (car input) 'reset-macros)
         (reset-macro! macro-dictionary))
        ((equal? (car input) 'reduce)
         (reduce-exp (cadr input)))
        ((equal? (car input) 'give-def)
         (cadr (look-up (cadr input) macro-dictionary)))
        ((equal? (car input) 'expand)
         (create-lambda (least-reduced (make-list (cadr input)))))
        ((equal? (car input) 'equal?)
         (equal? (least-reduced (make-list (cadr input)))
                 (least-reduced (make-list (caddr input)))))
        (else (eval-stream (reduce-stream input)))))

;;       (if (or (contains-pred? macro? (make-list (cadr input))) ;combs are macros too
;;               (contains-pred? macro? (make-list (caddr input))))
;;           (equal? (sk-eval (make-list (cadr input)))
;;                   (sk-eval (make-list (caddr input))))
;;           (equal? (least-reduced (make-list (cadr input)))
;;                   (least-reduced (make-list (caddr input))))))

;; in (p (s i i)) it can't find the shortest element
;; detecting non-terminating sequences through thresholds
;;  instead of storing the shortest element, keep read elements in another list, 
;;  go through items in the list and compare them to the current item,
;;  if the current item occurs in the list return the shortest element of the list,
;;  if the current item contains an element of the list plug the original into it
(define (eval-stream stream)
  (define (min-item i1 i2) ;checks for complexity through length (adjust for variables)
    (let ((l1 (deep-length i1)) (l2 (deep-length i2)))
      (if (< l1 l2) i1 i2)))
  (define (check org shr fst rst count)
    (cond ((= count 0) (list 'irreducible org shr fst))
          ((equal? fst (stream-car rst)) fst) ;find a way to simplify results into defined variables if any
          ((equal? fst shr)
           (list 'irreducible shr))
          ((contains-exp? shr (stream-car rst))
           (replace-exp shr org (stream-car rst)))
          (else (check org
                       (min-item fst shr) 
                       (stream-car rst) 
                       (stream-cdr rst)
                       (- count 1)))))
  (check (stream-car stream)  
         (stream-car (stream-cdr stream))
         (stream-car (stream-cdr (stream-cdr stream))) 
         (stream-cdr (stream-cdr (stream-cdr stream)))
         100))

(define (reduce-stream exp)
  (cons-stream exp (reduce-stream (reduce-exp exp))))

;;; Core of the algorithm

;; implement variable application later
;; e.g. (s k) -> (s k), but (lambda (x y) (s k x y)) -> (lambda (x y) y)
(define (reduce-exp exp)
  (define (look-for-nested exp)
    (cond ((null? exp) '())
          ((atom? exp) exp)
          ((atom? (car exp))
           (cons (car exp)
                 (look-for-nested (cdr exp))))
          (else
            (cons (reduce-exp (first-flatten (car exp)))
                  (look-for-nested (cdr exp))))))
  (cond ((null? exp) exp)
        ((atom? exp) exp)
        ((pair? (car exp))
         (append-new (reduce-exp (first-flatten (car exp)))
                     (look-for-nested (cdr exp))))
        ((null? (cdr exp)) 
         (car exp))
        ((applicable? (car exp)
                      (cdr exp) dictionary)
         (look-for-nested (apply-exp (car exp) (cdr exp) dictionary)))
        ((macro? (car exp))
         (reduce-exp (append-new (get-definition (car exp))
                                 (cdr exp))))
        ((and (number? (car exp))
              (> (car exp) 10))
         (reduce-exp (append-new (expand-num (car exp))
                                 (cdr exp))))
        (else (look-for-nested exp)))) 
;; if car exp or cdr exp cannot be reduced either, keep it in parentheses
;; do not use bare appends, but make it left-associative by default
;; (s i i x) -> (x (x))
;; gives ;The object (), passed as an argument to safe-cdr, is not a pair.

(define (applicable? comb exp dict)
  (define (count num lst)
    (cond ((= num 0) #t)
          ((null? lst) #f)
          (else (count (-1+ num) (cdr lst)))))
  (cond ((pair? comb) #f)
        ((atom? exp) #f)
        ((contains-comb? comb dict)
         (let ((args (arg-number comb dict)))
           (count args exp)))
        (else 
          ;; (error "Undefined operation -- APPLICABLE?" comb)
          #f))) ;variables like x that shouldn't be adjusted
           
(define (apply-exp comb exp dict)
  ((arg-apply comb dict) exp))
;;(if (primitive? comb)
;;  (let ((expanded (append (arg-def comb dict) exp)))
;;    (apply-exp (car expanded) (cdr expanded) dict))))

(define (apply-k exp)
  (cons (car exp) (cddr exp)))

(define (apply-s exp)
  (let ((z (caddr exp)) (rest (cdddr exp)))
    (append (list (car exp) z)
            (list (list (cadr exp) z))
            rest)))

;; create sk-expression for an arbitrary number
(define (expand-num num)
  (if (<= num 10)
      num
      (list '+ (remainder num 10)
               (list '* 10 (expand-num (quotient num 10))))))
          
;; deep search for child inside parent (application left-associative)
;; perhaps abstract these two and reduce-exp
;; (a ((b c) d) e) should register the same as (a (b c d) e)
(define (contains-exp? child parent)
  (define (look-for-nested ch par)
    (cond ((null? par) #f)
          ((atom? (car par))
           (look-for-nested ch (cdr par)))
          (else
            (or (contains-exp? ch (car par))
                (look-for-nested ch (cdr par))))))
  (define (deep-contains? ch par)
    (cond ((null? par) #f)
          ((atom? (car par))
           (or (equal? ch (car par))
               (deep-contains? ch (cdr par))))
          (else 
           (or (deep-contains? ch (car par))
               (deep-contains? ch (cdr par))))))
  (cond ((null? child) #t)
        ((atom? child) 
         (deep-contains? child parent))
        ((not (pair? parent)) #f)
        ((equal? (car child) (car parent)) 
         (or (contains-exp? (cdr child) (cdr parent))
             (look-for-nested child parent)))
        (else (look-for-nested child parent))))
;  (if (not (pair? parent))
;      (equal? child parent)
;      (or (contains-exp? child (car parent))
;          (contains-exp? child (cdr parent)))))

;; replace all occurrences of old with new inside parent
;; unnecessary parens when new is an atom and old is not
(define (replace-exp old new parent)
  (define (look-for-nested ol ne pa)
      (cond ((null? pa) '())
            ((atom? pa) pa)
            ((atom? (car pa))
             (cons (car pa)
                   (look-for-nested ol ne (cdr pa))))
            (else
              (append (list (replace-exp ol ne (car pa)))
                      (look-for-nested ol ne (cdr pa))))))
  (define (replace-atom ol ne pa)
    (cond ((null? pa) '())
          ((equal? ol pa) ne)
          ((atom? pa) pa)
          ((equal? ol (car pa))
           (cons ne (replace-atom ol ne (cdr pa))))
          (else 
           (cons (replace-atom ol ne (car pa)) 
                 (replace-atom ol ne (cdr pa))))))
  (define (starts-with? child par)
    (cond ((null? child) #t)
          ((null? par) #f)
          (else (and (equal? (car child) (car par))
                     (starts-with? (cdr child) (cdr par))))))
  (define (remove-at-start ol par)
    (if (null? ol)
        par
        (remove-at-start (cdr ol) (cdr par))))
  (first-flatten 
    (cond ((null? old) parent)
          ((null? parent) parent)
          ((atom? old)
           (replace-atom old new parent))
          ((equal? old (car parent)) 
           (append (list new) (look-for-nested old new (cdr parent))))
          ((starts-with? old parent)
           (append (list new) 
                   (look-for-nested old new (remove-at-start old parent))))
          (else (look-for-nested old new parent)))))

;;; The dictionary
          
(define (make-dictionary lst)
  (let ((comb-list lst))
    (define (set-list! new-list)
      (set! comb-list new-list)
      'ok)
    (lambda (m)
      (cond ((equal? m 'get) comb-list)
            ((equal? m 'set) set-list!)
            (else 
              (error "Unknown command -- DICTIONARY" m))))))

(define (get-dict dict)
  (dict 'get))
  
(define (set-dict! dict new)
  ((dict 'set) new))
        
(define (arg-number comb dict)
  (cadr (look-up comb dict)))
                
(define (arg-apply comb dict)
  (caddr (look-up comb dict)))
  
(define (look-up comb dict)
  (define (iter dict-list)
    (cond ((null? dict-list) 
           (error "Undefined operation -- LOOK-UP" comb))
          ((equal? comb (caar dict-list))
           (car dict-list))
          (else (iter (cdr dict-list)))))
  (iter (get-dict dict)))

(define (contains-comb? comb dict)
  (define (iter comb lst)
    (cond ((null? lst) #f)
          ((equal? comb (caar lst)) #t)
          (else (iter comb (cdr lst)))))
  (iter comb (get-dict dict)))
    
;; perhaps instantiate these in sk-driver-loop

(define dictionary 
  (make-dictionary (list (list 's 3 apply-s) (list 'k 2 apply-k))))
        
(define macro-dictionary
  (make-dictionary '()))
  
(define (reset-dict! dict)
  ((dict 'set) (list (list 's 3 apply-s) (list 'k 2 apply-k))))
  
(define (reset-macro! dict)
  ((dict 'set) (filter (lambda (binding) (contains-comb? (car binding) dictionary))
                       (dict 'get))))
  
(define (define-macro! sym def)
  (define (remove-macro sym lst)
    (filter (lambda (binding) (not (equal? sym (car binding)))) lst))
  (set-dict! macro-dictionary 
             (cons (list sym def) 
                   (remove-macro sym (get-dict macro-dictionary)))))

(define (macro? sym)
  (and (contains-comb? sym macro-dictionary)
       (not (contains-comb? sym dictionary))))
  
(define (get-definition sym)
  (cadr (look-up sym macro-dictionary)))

;; (define (primitive? arg)
;;   (or (equal? arg 's)
;;       (equal? arg 'k)))

;; (define (arg-def comb dict)
;;   (if (primitive? comb)
;;       (error "Inapplicable operation -- ARG-DEF" comb)
;;       (cadr (look-up comb dict))))
      
;; (define symbol-stream ;symbols used in substitution, forbid from adding to dictionary
;;   (cons-stream '- (stream-map add-symbol symbol-stream))) 

(define (symbol-concat sym1 sym2)
  (string->symbol (list->string (append (string->list (symbol->string sym1))
                                        (string->list (symbol->string sym2))))))

(define (integers-starting-from n)
  (cons-stream n (integers-starting-from (1+ n))))
  
(define argument-stream ; arg1 arg2 etc.
  (stream-map (lambda (x) (symbol-concat 'arg (string->symbol (number->string x)))) 
              (integers-starting-from 1)))

(define (first-n-symbols n)
  (define (iter n syms)
    (if (= n 0)
        '()
        (cons (head syms)
              (iter (-1+ n) (tail syms)))))
  (iter n symbol-stream))

;; takes result of least-reduced, gives number of last symbol in it
(define (last-num expr)
  (define (number-check symbol)
    (define (iter num stream)
      (if (equal? symbol (head stream))
          num
          (iter (1+ num) (tail stream))))
    (iter 1 symbol-stream))
  (reduce-left max 0 (map number-check (deep-flatten expr))))

;; When I calculate the arg number, I shouldn't count the arguments of the last result,
;;   but how many arguments least-reduced required in order to get to the result
;;   otherwise k would be taken to require only one argument, for example
(define (define-comb! comb def)
  (define (remove-comb comb lst)
    (filter (lambda (binding) (not (equal? comb (car binding)))) lst))
  (let* (; (num (subt (arg-number (car def) dictionary) (length def)))
         (least (least-reduced def))
         (expanded (make-list (cadr least)))
         (num (car least))
         (app (generate-apply expanded num))
         (rest-dict (remove-comb comb (get-dict dictionary))))
    (set-dict! dictionary (cons (list comb num app) rest-dict))))

;; The idea is to record the behavior of a combinator instead of just plugging it in.
;; Better yet, calculate num here as the smallest number for which the result
;; doesn't contain any operands other than the variables.
;; The argument number should be derived from the expression that this gives.
;; a function that takes the first num elements of the list
;; and matches them against args
;;  (let* ((args (head symbol-stream num))
;;         (exp (append def args)) ;expanded
;;         (res (eval-stream (reduce-stream exp)))
;;         ()))
(define (generate-apply expan num) 
  (lambda (expr) ;doesn't evaluate insides before application
    (let* ((sep (separate-until num expr))
           (args (car sep))
           (rest (cdr sep)))
      (append-new (match-symbols expan argument-stream args)
                  rest))))

;; make it return the first irreducible expression if any
;; make it so, if def isn't defined, it just gives def
(define (least-reduced def)
  (define (sym-streams symbols) ;(-) (- --) (- -- ---) etc.
    (cons-stream (list (stream-car symbols))
                 (stream-map (lambda (x) (append (list (stream-car symbols)) x)) 
                             (sym-streams (stream-cdr symbols)))))
  (define sym-stream ;(1 -) (2 - --) etc.
    (enumerate-stream (sym-streams argument-stream)))
  (define (no-free-vars? expr)
    (accumulate boolean-and #t (map (lambda (comb) (contains? comb (deep-flatten (first-n (car expr) argument-stream)))) 
                                    (deep-flatten (cadr expr)))))
  (stream-car (stream-filter no-free-vars? 
                             (stream-map (lambda (inp) (list (car inp) 
                                                             (make-list (sk-eval (append def (cadr inp))))))
                                         sym-stream))))
;;(define (least-reduced def)
;;  (define argument-stream
;;    (stream-map (lambda (x) (list 'arg x)) (integers-starting-from 0)))
;;  (define (sym-streams symbols)
;;    (cons-stream (list (stream-car symbols))
;;                 (stream-map (lambda (x) (append (list (stream-car symbols)) x)) 
;;                             (sym-streams (stream-cdr symbols)))))
;;  (define sym-stream ;(1 (-)) (2 (- --)) etc.
;;    (enumerate-stream (sym-streams symbol-stream)))
;;  )

;;   (b b b - -- --- ----) -> (- (-- ---- ----))
;; how about I wrap the symbols instead, not the arguments? then there would
;;   be no need for unwrapping and wrapping would be incorporated in sym-streams instead
(define (match-symbols sym-exp syms args)
  (define (wrap item)
    (list 'wrap item))
  (define (unwrap tree)
    (cond ((null? tree) '())
          ((atom? tree) tree)
          ((atom? (car tree))
           (cons (car tree)
                 (unwrap (cdr tree))))
          ((equal? (caar tree) 'wrap)
           (cons (unwrap (cadar tree)) 
                 (unwrap (cdr tree))))
          (else
           (cons (unwrap (car tree))
                 (unwrap (cdr tree))))))
  (define (match-symbol sym-exp sym arg)
    (if (null? sym-exp)
        '()
        (let ((fst (car sym-exp))
              (rst (cdr sym-exp)))
          (if (pair? fst)
              (cons (if (equal? (car fst) 'wrap)
                        fst
                        (match-symbol fst sym arg))
                    (match-symbol rst sym arg))
              (cons (if (equal? fst sym)
                        arg
                        fst)
                    (match-symbol rst sym arg))))))
  (if (null? args)
      sym-exp
      (unwrap (match-symbols (match-symbol sym-exp 
                                   (head syms) 
                                   (wrap (car args)))
                             (tail syms)
                             (cdr args)))))
 
(define (create-lambda reduced-exp)
  (list 'lambda 
        (first-n (car reduced-exp) argument-stream) 
        (make-atom (cadr reduced-exp))))
                             
;;; Creating sk-expressions for arbitrary lambda expressions (lambda args body)
;;; The algorithm could be composed of these steps:
;;;  - Deleting unused arguments
;;;  - Repeating repeated arguments
;;;  - Rearranging arguments and other symbols to conform to (deep-flatten body)
;;;  - Parenthesizing expressions from deep to shallow
;;;  - Composing all these operations together based on the number of symbols in the body
;;; But instead, I will simply adopt an inductive definition of lambda expressions.
;;; Now that I have all these lambda tools here, maybe the next thing I should do is to
;;;   work with more complex functional programming stuff and extend these notions to
;;;   the things I've already defined, as in match-symbols, look-for-nested, etc.
;;;   Maybe dictionary would store not functions, but lambda expressions which would then
;;;   be applied to an expression from the left, provided it is applicable.
;;;   Then least-reduced can be simplified too.

(define (decrypt lambda-exp)
  (cond ((variable? lambda-exp) 
         lambda-exp)
        ((application? lambda-exp) 
         (first-flatten (list (make-atom (decrypt (applying lambda-exp)))
                              (make-atom (decrypt (applied lambda-exp))))))
        ((lambda? lambda-exp)
         (let ((var (lambda-variable lambda-exp))
               (body (lambda-body lambda-exp)))
             (cond ((equal? (make-list body) (make-list var))
                    (list 'i))
                   ((not (free? var body))
                    (list 'k (make-atom (decrypt body))))
                   ((application? body)
                    (if (and (equal? (make-list var) (make-list (applied body)))
                             (not (free? var (applying body))))
                        (make-list (decrypt (applying body)))
                        (list 's (make-atom (decrypt (make-lambda var (applying body))))
                                 (make-atom (decrypt (make-lambda var (applied body)))))))
                   ((lambda? body)
                    (decrypt (make-lambda var (decrypt body)))))))
         (else (error "Invalid expression -- DECRYPT" lambda-exp))))

(define (variable? exp)
  (if (atom? exp)
      #t
      (singleton? exp)))

(define (application? exp)
  (and (pair? exp))
       (not (lambda? exp)))

;; (define (if-singleton exp)
;;  (if (and (pair? (car exp))
;;           (null? (cdr exp)))
;;      (car exp)
;;      exp))
(define (applying exp)
  (if (singleton? exp)
      (car exp)
      (but-last exp)))
      
(define (applied exp)
  (if (singleton? exp)
      '()
      (last exp)))
      
(define (lambda? exp)
  (and (pair? exp)
       (equal? (car exp) 'lambda)
       (not (null? (cdr exp)))
       (not (null? (cddr exp)))
       (pair? (cadr exp))))
       
(define (lambda-variable exp)
  (caadr exp))
  
(define (lambda-body exp)
  (if (null? (cdadr exp))
      (caddr exp)
      (list 'lambda (cdadr exp) (caddr exp))))
      
(define (free? var exp)
  (cond ((atom? exp) 
         (equal? var exp))
        ((null? (cdr exp)) 
         (equal? var (car exp)))
        ((application? exp)
         (or (free? var (applying exp))
             (free? var (applied exp))))
        ((lambda? exp)
         (if (equal? var (lambda-variable exp))
             #f
             (free? var (lambda-body exp))))))
      
(define (make-lambda var body)
  (if (lambda? body)
      (list 'lambda (cons var (cadr body)) (caddr body))
      (list 'lambda (list var) (make-atom body))))

;;; Tools
        
(define (atom? exp)
  (not (or (pair? exp)
           (null? exp))))

(define (contains? item lst)
  (cond ((null? lst) #f)
        ((equal? item (car lst)) #t)
        (else (contains? item (cdr lst)))))
        
(define (append-new l1 l2)
  (let ((i1 (make-list l1))
        (i2 (make-list l2)))
    (append i1 i2)))

(define (subt a b)
  (if (< a b) 0 (- a b)))
  
(define (make-list x)
  (if (atom? x)
      (list x)
      x))

(define (singleton? x)
  (and (pair? x)
       (null? (cdr x))
       ;(not (pair? (car x)))
     ))

(define (make-atom x)
  (if (pair? x)
      (if (null? (cdr x)) (car x) x)
      x)) 
;; reduce-left (use (reduce-left list/cons '() lst) to associate lists leftwise)
(define (accumulate step zero lst)
  (if (null? lst)
      zero
      (accumulate step (step zero (car lst)) (cdr lst))))
 
;; and not allowed to be passed as a first class function     
(define (boolean-and x y)
  (and x y))
  
(define (add-symbol sym)
  (string->symbol (list->string (cons #\- (string->list (symbol->string sym))))))
  
;; (define (flatten x)
;;   (cond ((null? x) '())
;;         ((pair? x) (append (flatten (car x)) (flatten (cdr x))))
;;         (else (list x))))
(define (flatten lst)
  ;(reduce-right append-new '() lst)
  (if (pair? lst)
      (append-new (car lst)
                  (flatten (cdr lst)))
      (make-list lst)))
(define (deep-flatten lst)
  (if (pair? lst)
      (append-new (deep-flatten (car lst))
                  (deep-flatten (cdr lst)))
      (make-list lst)))

;; (separate-until 2 '(a b c d)) -> '((a b) c d)
;; maybe adjust the algorithm to make it tail-recursive
;; append-new is a bane to this program
(define (separate-until n lst)
  (if (= n 1)
      (cons (list (car lst)) (cdr lst))
      (let ((res (separate-until (-1+ n) (cdr lst))))
        (cons (cons (car lst) (car res)) 
              (cdr res)))))
  
(define (deep-length lst)
  (cond ((null? lst) 0)
        ((atom? lst) 1)
        (else (+ (deep-length (car lst))
                 (deep-length (cdr lst))))))
                           
(define (enumerate-stream stm)
  (define (iter num stm)
    (cons-stream (list num (stream-car stm))
                 (iter (1+ num) (stream-cdr stm))))
  (iter 1 stm))
  
(define (first-flatten exp)
  (if (pair? (car exp))
      (first-flatten (append (car exp) (cdr exp)))
      exp))

(define (first-n n stm)
  (if (= n 0)
      '() 
      (cons (stream-car stm)
            (first-n (-1+ n) (stream-cdr stm)))))

(define (contains-pred? pred lst)
  (reduce-left (lambda (x y) (or x y)) #f (map pred lst)))

(define (but-last exp)
 (if (null? (cdr exp))
     '()
     (cons (car exp) 
           (but-last (cdr exp)))))

(define (last exp)
 (if (null? (cdr exp))
     (car exp)
     (last (cdr exp))))

;;; (define (separate-until n lst)
;;;   (define (separate-iter n l1 l2)
;;;     (if (= n 0)
;;;         (cons l1 l2))))

;;; first finding: (k s s s k s s k k s k) = s
;;; Binary tree implementation might be necessary - (s k (s k k k))
;;;   also possibly use placeholder variables like x, that aren't applied 
;;;   (applicable? returns false for them)
;;;   (s i i) works on variables, but not on itself (algorithm expands too much)
;;; Adjust it to preserve defined names for i and whatnot
;;; Consider initializing the dictionary in sk-driver-loop; that way you can just
;;;   pass it as a parameter and not construct a whole new object

;;; Later come up with tools to convert SKI expressions into lambdas, play with 
;;;   their form, use Church encoding, etc.

;;; s i x y -> y (x y)