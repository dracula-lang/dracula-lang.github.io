(in-package "ACL2")

;; This book defines an abstract data type for
;; lambda calculus syntax, including constructors,
;; predicates (weak and strong), and accessors.

;; A LambdaCalculusTerm (LCTerm) is one of:
;; - Symbol
;; - (list 'abs Symbol LCTerm)
;; - (list 'app LCTerm LCTerm)

;; lc-abs : Symbol LCTerm -> LCTerm
;; Constructs an abstraction.
(defun lc-abs (var body)
  (list 'abs var body))

;; lc-app : LCTerm LCTerm -> LCTerm
;; Constructs an application.
(defun lc-app (fun arg)
  (list 'app fun arg))

;; abs? : Any -> Boolean
;; Reports whether a value is an abstraction.
;; Weak predicate only, does not check substructure.
(defun abs? (v)
  (and (true-listp v)
       (= (length v) 3)
       (eq 'abs (car v))))

;; app? : Any -> Boolean
;; Reports whether a value is an application.
;; Weak predicate only, does not check substructure.
(defun app? (v)
  (and (true-listp v)
       (= (length v) 3)
       (eq 'app (car v))))

;; abs-var : LCTerm[abs] -> Symbol
;; Produces the formal argument of an abstraction.
(defun abs-var (abs)
  (cadr abs))

;; abs-body : LCTerm[abs] -> LCTerm
;; Produces the body of an abstraction.
(defun abs-body (abs)
  (caddr abs))

;; app-fun : LCTerm[app] -> LCTerm
;; Produces the function of an application.
(defun app-fun (app)
  (cadr app))

;; app-arg : LCTerm[app] -> LCTerm
;; Produces the argument of an application.
(defun app-arg (app)
  (caddr app))

;; lc-term? : Any -> Boolean
;; Reports whether a value is a lambda calculus term.
(defun lc-term? (v)
  (declare (xargs :measure (acl2-count v)))
  (cond
    ((atom v) (symbolp v))
    ((abs? v) (and (symbolp (abs-var v))
                   (lc-term? (abs-body v))))
    ((app? v) (and (lc-term? (app-fun v))
                   (lc-term? (app-arg v))))
    (t nil)))

