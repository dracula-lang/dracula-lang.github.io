#|
Matrix transposition using alist representation.
|#

(include-book "data-structures/list-theory"  :dir :system)
(include-book "data-structures/alist-theory" :dir :system)

;; Use deflist instead of doing a manual structural
;; recursion.  deflist produces theorems that help
;; ACL2 rewrite nat*nat-listp when it interacts
;; with the other primitive list functions.
;; e.g., (nat*nat-listp (append X Y))
;;          = (and (nat*nat-listp X)
;;                 (nat*nat-listp Y))
;; Recognize a list of pairs of natural numbers
(deflist nat*nat-listp (l)
  (lambda (x) 
    (and (consp x) 
         (natp (car x)) 
         (natp (cdr x)))))

;; Recognize a matrix.
(defun matrix? (x)
  (and (alistp x)
       (nat*nat-listp (domain x))))

;; Produce the entry in the matrix M at the given 
;; row and column.  Produces nil when row and col 
;; are out of bounds.
(defun matrix-ref (M row col)
  (if (endp M)
      nil
      (if (equal (caar M) (cons row col))
          (cdar M)
          (matrix-ref (cdr M) row col))))

;; Produce a matrix row whose entries are 
;; consecutive numbers starting from `start'
(defun build-row (row cols start)
  (if (zp cols)
      nil
      (acons (cons (1- row) (1- cols)) start
             (build-row row (1- cols) (1+ start)))))

;; Produce a matrix of numbers with the given size
;; and whose entries are drawn from 
;; (start, start+1, ..., start+(rows*cols)).
;; The matrices are (0,0)-indexed.
(defun build-matrix (rows cols start)
  (if (zp rows)
      nil
      (append (build-row rows cols start)
              (build-matrix (1- rows) cols (+ start cols)))))

#|
Let's pause here and try to prove that build-matrix really
does produce a matrix.

To do this, we must prove that build-matrix produces an 
alist whose keys are pairs of natural numbers (why?).
If we inspect the definition of build-matrix, we see that
the items in the produced alist are actually coming from 
build-row.  build-matrix simply appends these rows togther
to form a larger alist.

That means that we must prove that build-row produces alists
whose keys are natural numbers.  

(Note that this is a pattern:  when we want to prove something
about a function that calls helper functions, we must
first prove theorems about the helper functions themselves.)

We have just discovered the theorems that we need:
(1) build-row produces alists
(2) these alists have keys that are pairs of natural numbers.
ACL2 can prove both of these easily.
|#
(defthm build-row-always-produces-an-alist
  (alistp (build-row rows cols start)))

(defthm build-row-produces-natural-keys
  (implies (posp rows)
           (nat*nat-listp 
            (domain (build-row rows cols start)))))
#|
Often ACL2 needs to be told what kind of inputs a function
receives before it can predict anything about the output.
We were able to get away without doing so in the first of these
theorems, but we must specify that `rows' is a positive integer
in the second.  

The game here is to specify just enough information for ACL2 
to proceed, but to not overconstrain the system.
The fewer hypotheses that occur in your implications, the
easier it is for ACL2 to use the theorems in the ensuing
development.
|#

#| At this point, ACL2 can prove that build-matrix produces
a matrix.  If you look at the end of the proof output
under `Summary', you'll see 
...
 (:REWRITE BUILD-ROW-ALWAYS-PRODUCES-AN-ALIST)
 (:REWRITE BUILD-ROW-PRODUCES-NATURAL-KEYS)
...
This indicates that ACL2 has indeed used the lemmas we just
proved in order to prove build-matrix-produces-matrix.
|#
(defthm build-matrix-produces-matrix
  (implies (and (posp rows) (posp cols) (integerp start))
           (matrix? (build-matrix rows cols start))))

#|
Now we turn to matrix transposition.  If M is a matrix,
then (transpose M) is a matrix whose rows are exactly the
columns of M.  This operation is easily accomplished using
our representation of matrices:
|#

;; Consume (cons i j) and produce (cons j i)
(defun flip (pair)
  (cons (cdr pair) (car pair)))

;; Consume a list of pairs and produce a new list
;; where each pair is flipped.
(defun flip-all (x)
  (if (endp x)
      nil
      (cons (flip (car x)) (flip-all (cdr x)))))


;; Produce a matrix whose rows are just the columns
;; of the given matrix.
(defun transpose (x)
  (let ((indices  (domain x))
        (elements (range  x)))
    (pairlis$ (flip-all indices) elements)))

#|
ACL2 can easily prove that transpose produces a matrix
when it is given a matrix.  We're lucky here in that we 
actually do not have to state any lemmas about flip-all 
or flip.  

Remember though that ACL2 often needs theorems about helper 
functions before being able to cope with more complicated 
functions that call the helpers.
|#
(defthm transpose-preserves-matrix?
  (implies (matrix? x)
           (matrix? (transpose x))))

#|
Here is the main result.  It says that the element at
position (i,j) in M appears at position (j,i) in
(transpose M).  ACL2 can prove this without the
prior theorem `transpose-preserves-matrix?'.
|#
(defthm transpose-is-correct-wrt-matrix-ref
  (implies t ;(matrix? M)
           (equal (matrix-ref (transpose M) i j)
                  (matrix-ref M j i))))

;;; EOF