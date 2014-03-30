(in-package "ACL2")

(include-book "lc")

;; This file uses the LC book's lambda calculus syntax
;; to define functions to calculate free variables and
;; term substitution.

;; free-vars : LCTerm -> Symbol-List
;; Produces the set of free variables in a term.
(defun free-vars (term)
  (cond
    ((symbolp term) (list term))
    ((abs? term)
     (remove (abs-var term)
             (free-vars (abs-body term))))
    ((app? term)
     (remove-duplicates
      (append (free-vars (app-fun term))
              (free-vars (app-arg term)))))))

;; lc-subst : LCTerm Symbol LCTerm -> LCTerm
;; Replaces formal with actual in term.
(defun lc-subst (term formal actual)
  (cond
    ((symbolp term)
     (if (eq formal term) actual term))
    ((abs? term)
     (if (eq formal (abs-var term))
         term
         (lc-abs (abs-var term)
                 (lc-subst (abs-body term) formal actual))))
    ((app? term)
     (lc-app (lc-subst (app-fun term) formal actual)
             (lc-subst (app-arg term) formal actual)))))

;; Proves the syntactic type of lc-subst's result.
(defthm lc-subst-preserves-terms
  (implies (and (lc-term? term)
                (symbolp formal)
                (lc-term? actual))
           (lc-term? (lc-subst term formal actual))))

;; Test cases for lc-subst:

(equal (lc-subst 'x 'x 'y) 'y)
(equal (lc-subst 'x 'y 'z) 'x)

(equal (lc-subst (lc-app 'x 'y) 'x 'z) (lc-app 'z 'y))

(equal (lc-subst (lc-abs 'x 'x) 'x 'z) (lc-abs 'x 'x))
(equal (lc-subst (lc-abs 'y 'x) 'x 'z) (lc-abs 'y 'z))

(equal (lc-subst (lc-app 'x 'x) 'x (lc-abs 'x (lc-app 'x 'x)))
       (lc-app (lc-abs 'x (lc-app 'x 'x))
               (lc-abs 'x (lc-app 'x 'x))))
