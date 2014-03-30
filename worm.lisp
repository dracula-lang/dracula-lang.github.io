;;;; A Worm Game
;;;; Author: Matthias Felleisen
;;;; Translated from PLT Scheme to ACL2 by Dale Vaillancourt

#| *** Introduction ***
This code is meant to be read as a tutorial on building and reasoning about
graphical programs written in DrScheme's ACL2 Language Level.  We will assume
that the reader is familiar with the basics of programming in ACL2 at the level
covered in ACL2's 'Walking Tour':
   http://www.cs.utexas.edu/users/moore/acl2/v2-9/A_Walking_Tour_of_ACL2.html

Please read this from within DrScheme and set the Language Level to 
"ACL2 Beginner".  If you are unfamiliar with a built-in form or function, then
you can highlight it with the mouse and press 'F1' to access its documentation.

Before continuing, you should of course play the game for a few minutes :)

The remainder of this document/source-code is organized into roughly six 
sections.  The next section explains what Teachpacks are.  Then there is one
section for each datatype in the game: FOOD, WORM, and the WORLD.  Then
there is a section RUN that puts everything together to get the game started.  The
final section is THEOREMS and contains theorems that we prove about the game.
|#

#| *** The World and Rand Teachpacks ***
A teachpack is a module that provides additional functions and data to your 
program.  For the Worm game, we will take advantage of two teachpacks.  The
first one is the World teachpack, and it provides two kinds of functions:
  1. functions for creating and drawing shapes
  2. functions for managing the state of the interface
You may access detailed documentation for the World teachpack by searching for
"world" in Help Desk, but we will explain the functionality used in the Worm
game as it occurs in the code that follows.

The rand teachpack provides one function that allows you to generate random
numbers:
  ;; rand : Number Number -> Number
  (rand max last-random-number) produces a natural number less than `max'.
  The second argument is the last random number that was produced.

We will use this for placing the worm-food (the green dots) at arbitrary 
locations on the game board.

|#
(include-book "world" :dir :teachpacks)
(include-book "rand"  :dir :teachpacks)
(include-book "data-structures/structures" :dir :system)
(include-book "data-structures/list-theory" :dir :system)

#| *** ACL2's built-in books ***
We take advantage of ACL2's built-in book to reason about arithmetic.
|#
(include-book "arithmetic-3/extra/top-ext" :dir :system)

#| *** Playing Field ***
The dimensions of our playing field will be 400x300.
The coordinate system that we will use puts (0,0) in the upper-left corner.
The x-coordinate increases as we move right, and the y-coordinate increases
as we move down.
|#
(defconst *WIDTH*  150)
(defconst *HEIGHT* 150)

#| *** FOOD Datatype ***
We will represent the food simply by its position on the playing field. As such,
we will need to make sure that we only create food instances whose coordinates
are within the *WIDTH* and *HEIGHT* we defined above.  We will define a
predicate to recognize such well-formed food objects.  In addition, we define
the initial food position, and functions to produce the next food,
draw the food, and to determine the position of the food.

The `posn' datatype is provided by the World teachpack.  In particular, we have
available these functions:
- To create a posn:
  make-posn : Number Number -> posn?
- To determine if a value is a posn:
  posn? : Any -> Boolean
- To produce the x-coordinate of a posn:
  posn-x : posn? -> Number
- To produce the y-coordinate of a posn:
  posn-y : posn? -> Number
|#
;; food? : Any -> Boolean
(defun food? (x) (posn? x))

;; food-well-formed : food? -> Boolean
;; Is the given food within the playing field?
(defun food-well-formed (p)
  (let ((x (posn-x p))
        (y (posn-y p)))
    (and (integer-range-p 0 (1+ *WIDTH*) x) ;; is 0 <= x < *WIDTH* + 1 ?
         (integer-range-p 0 (1+ *HEIGHT*) y)))) ;; similarly for y

;; The initial food position.
;; The number 1382728371 is an arbitrary initial "seed" for the random
;; number generator.  Changing this will yield a different sequence of
;; food positions when the game is played.
(defconst *initial-food* 
  (make-posn (rand *WIDTH* (initial-seed)) 
             (rand *HEIGHT* (next-seed (initial-seed)))))

;; new-food : seedp -> food?
;; Produce the next food location given the current one.
(defun new-food (s)
  (make-posn (rand *WIDTH* s) (rand *HEIGHT* (next-seed s))))

;; food-image : food Scene -> Scene
;; Produce a Scene like the given one, but with a green
;; dot at the position of the given food.
(defun food-image (f scene)
  (place-image (circle 3 'solid 'blue) (posn-x f) (posn-y f) scene))

;; food-posn : food? -> posn?
;; Determine the position of the given food.
(defun food-posn (f) f)
;;; END OF FOOD Datatype

#| *** WORM Datatype ***
Now we turn to the representation of the worm.  A worm is a structure consisting
of three pieces:  a velocity, a head, and a tail.  The velocity is a symbol that
indicates the current direction: 'up, 'down, 'left, or 'right.

Worms are divided into segments, and the worm grows by one segment when it eats
a piece of food.  The worm's head is a single segment, and the tail is a list
of segments.  
|#

;; Velocity:
(defconst *VELOCITY* '(up down left right))
(defun velocity? (a) (and (symbolp a) (consp (member-eq a *VELOCITY*))))

;; Velocity Velocity -> Boolean
;; Do the given velocities indicate opposite directions?
(defun velocity-opposite? (a b)
  (cond
    ((eq 'up a) (eq 'down b))
    ((eq 'down a) (eq 'up b))
    ((eq 'left a) (eq 'right b))
    ((eq 'right a) (eq 'left b))))

;; We represent a segment by its position.  When we
;; draw it, it will be a circle of radius 5 centered
;; at this position.
(defun segment? (x) (posn? x))
(defconst *RADIUS* 5)
(defconst *DIAMETER* (* 2 *RADIUS*))

;; list-of-segments? : Any -> Boolean
;; Is every member of the given list a segment?
(deflist list-of-segments? (l) segment?)
;; It's important to use `deflist' to define such specialized list predicates
;; because ACL2 will automatically generate lots of free theorems to help
;; automate the reasoning process later on.  If we were not interested
;; in automated reasoning, we could simply use the equivalent structurally 
;; recursive definition to avoid producing the free theorems:
#|
 (defun list-of-segments? (l)
   (if (consp l)
       (and (segment? (car l)) (list-of-segments (cdr l)))
       (null l)))
|#


#| Structure definitions
Now we encounter our first structure definition:
|#
(defstructure worm 
  (velocity (:assert (velocity? velocity)))
  (head     (:assert (segment? head)))
  (body     (:assert (list-of-segments? body))))
#|
This structure definition says that a worm is a structure consisting of
three parts named velocity, head, and body.  The (:assert ...) forms indicate
that velocity is a velocity?, that head is a segment?, and that body is
a list-of-segments?.

The definition generates a family of functions for building and manipulating
worms.  Here are their contracts and purpose statements:
;; Is the given value a worm?
 - worm-p : Any -> Boolean

;; Create a worm 
 - worm : velocity? segment? list-of-segments? -> worm-p

;; Produce the given worm's velocity
 - worm-velocity : worm-p -> velocity?

;; Produce the given worm's head segment
 - worm-head : worm-p -> segment?

;; Produce the given worm's body (or tail)
 - worm-body : worm-p -> list-of-segments?

Note that the constructor `worm' does *not* check that the given arguments
satisfy the predicates specified in the (:assert ...) expressions.  Nothing
stops us from saying:
  (defconst *not-really-a-worm* (worm 'up (make-posn 0 10) (list 17)))
This is not a well-formed worm because (list 17) is not a list of segments.

The predicate `worm-p' will check the constraints prescribed by (:assert ...): 
  (worm-p *not-really-a-worm*)
produces nil (because (list 17) is *not* a list of segments).

So worm-p will only produce t on well-formed worms... won't it?  Consider this
worm:
  (defconst *a-worm???* (worm 'up (make-posn 10 10) (list (make-posn 50 50))))

This worm is surely not well-formed:  its head is disconnected from its tail!
A worm must have an additional well-formedness constraint:  the head must be
adjacent to the first segment of the tail, and every consecutive pair of segments
in the tail must be adjacent.  

When are two segments adjacent?  We know that each segment is a circle of
diameter *DIAMETER*.  Further, given our definition of *VELOCITY*, the worm
can only move vertically and horizontally.  So that means that an adjacent pair
of segments must have the same x-coordinates, and their y-coordinates differ
by *DIAMETER*.  Or, their x-coordinates differ by *DIAMETER*, and they have
the same y-coordinates.
|#
;; adjacent? : Segment Segment -> Boolean
(defun adjacent? (seg-1 seg-2)
  (let ((x1 (posn-x seg-1))
        (y1 (posn-y seg-1))
        (x2 (posn-x seg-2))
        (y2 (posn-y seg-2)))
    (or (and (= x1 x2) (= (abs (- y1 y2)) *DIAMETER*))
        (and (= y1 y2) (= (abs (- x1 x2)) *DIAMETER*)))))

;; consecutive-segments-adjacent? : list-of-segments? -> boolean?
;; Is every consecutive pair of segments in this list adjacent?
(defun consecutive-segments-adjacent? (los)
  (if (consp los)
      (or (null (cdr los))
          (and (adjacent? (car los) (cadr los))
               (consecutive-segments-adjacent? (cdr los))))
      (null los)))
#|
Now we can state formally what it means for a worm to be well-formed.
|#
;; worm-well-formed? : worm-p -> Boolean
(defun worm-well-formed? (w)
  (let ((tail (worm-body w))
        (head (worm-head w)))
    (consecutive-segments-adjacent? (cons head tail))))
#| Example:
(defconst *w*
  (worm 'up
        (make-posn 10 10)
        (list (make-posn 20 10) (make-posn 30 10) (make-posn 30 20))))
(worm-p *w*)            ;; should produce t
(worm-well-formed? *w*) ;; should produce t
|#

#|
Now we define several useful functions on worms.
|#
;; worm-new : velocity? Number Number -> worm-p
;; Produce a worm with velocity v at the coordinates (x,y), with no tail.
(defun worm-new (v x y) (worm v (make-posn x y) nil))

;; worm-length : worm-p -> Number
;; Produce the number of segments in the given worm.
(defun worm-length (w) (+ (len (worm-body w)) 1))

;; Segment Velocity -> Segment
;; Move a segment one step in direction specified by vel
(defun segment-move (seg vel)
  (let ((x (posn-x seg))
        (y (posn-y seg)))
    (cond
      ((eq vel 'up) (make-posn x (- y *DIAMETER*)))
      ((eq vel 'down) (make-posn x (+ y *DIAMETER*)))
      ((eq vel 'left) (make-posn (- x *DIAMETER*) y))
      ((eq vel 'right) (make-posn (+ x *DIAMETER*) y)))))

;; worm-move : worm-p -> worm-p
;; Move a whole worm one step in the direction it's facing.
(defun worm-move (w)
  (let ((head (worm-head w))
        (vel  (worm-velocity w))
        (body (worm-body w)))
    (let ((new-head (segment-move head vel))
          (new-tail (butlast (cons head body) 1)))
      (worm vel new-head new-tail))))

;; worm-move/eat : worm-p -> worm-p
;; Move the worm one step in the direction it's facing, but add an extra
;; tail segment.
(defun worm-move/eat (w)
  (let ((head (worm-head w))
        (vel  (worm-velocity w))
        (body (worm-body w)))
    (let ((new-head (segment-move head vel))
          (new-tail (cons head body)))
      (worm vel new-head new-tail))))

;; worm-image/acc : list-of-segments? Scene -> Scene
;; Produces a Scene like the given one, but with each segment drawn on it.
(defun worm-image/acc (segs r)
  (if (endp segs)
      r
      (let ((f (car segs)))
        (worm-image/acc (cdr segs)
                        (place-image (circle 5 'solid 'red) (posn-x f) (posn-y f) r)))))
;; worm-image : worm-p Scene -> Scene
;; Produce a Scene like the given one, but with the worm drawn on it.
(defun worm-image (w image)
  (let ((h (worm-head w)))
    (place-image (overlay (circle 5 'solid 'red)
                          (rectangle 2 4 'solid 'black))
                 (posn-x h) (posn-y h)
                 (worm-image/acc
                  (worm-body w)
                  image))))

;; worm-change : worm-p velocity? -> worm-p
;; Produce a worm facing in the given direction and that has moved one step.
(defun worm-change (w v)
  (worm-move (worm v (worm-head w) (worm-body w))))

;; worm-posn : worm-p -> posn?
;; Determine the position of the worm's head.
(defun worm-posn (w) (worm-head w))

;; worm-outside? : worm-p -> Boolean
;; Is the given worm outside the playing field?
(defun worm-outside? (w)
  (let ((h (worm-head w)))
    (not (and (<= 0 (posn-x h)) (<= (posn-x h) *WIDTH*) 
              (<= 0 (posn-y h)) (<= (posn-y h) *HEIGHT*)))))

;; worm-ate-self? : worm-p -> Boolean
;; Does the worm's head overlap with any segment in its body?
(defun worm-ate-self? (w)
  (let ((h (worm-head w)))
    (member-equal h (worm-body w)))) ;; instead of posn=? ...

;; worm-would-eat-self? : worm-p velocity? -> Boolean
;; Would the worm run into itself if it turned in the given direction?
(defun worm-would-eat-self? (w v)
  (and (velocity-opposite? (worm-velocity w) v) (= (len (worm-body w)) 1)))

;; sqr : Number -> Number
;; compute the square of x.
(defun sqr (x) (* x x))

;; Posn Posn -> Number
; N.B. There is no square root, so we compute the square of the distance.
(defun distance-squared (p q)
  (let ((xp (posn-x p))
        (xq (posn-x q))
        (yp (posn-y p))
        (yq (posn-y q)))
    (+ (sqr (- xp xq)) (sqr (- yp yq)))))

(defun worm-close-to? (w p)
  (<= (distance-squared (worm-posn w) p) (sqr *DIAMETER*)))

#| Test cases for WORM functions
We have now written some nontrivial code, so a few test cases are in order.
|#
(defconst *worm-move-test-1*
  (equal (worm-move (worm 'up (make-posn 10 10) nil))
         (worm 'up (make-posn 10 0) nil)))
(defconst *worm-move-test-2*
  (equal (worm-move (worm 'up (make-posn 10 10) (list (make-posn 10 20))))
       (worm 'up (make-posn 10 0) (list (make-posn 10 10)))))

(defconst *worm-move/eat-test-1*
  (equal (worm-move/eat (worm 'up (make-posn 10 10) nil))
         (worm 'up (make-posn 10 0) (list (make-posn 10 10)))))
(defconst *worm-move/eat-test-2* 
  (equal (worm-move/eat (worm 'up (make-posn 10 0) (list (make-posn 10 10))))
       (worm 'up (make-posn 10 -10)
             (list (make-posn 10 0) (make-posn 10 10)))))

(defconst *worm-change-test* 
  (equal (worm-change (worm 'up (make-posn 10 10) nil) 'left)
         ;; worm-change also moves the worm in the new direction.
         (worm 'left (make-posn 0 10) nil)))
;;; END OF WORM

#| *** WORLD Datatype ***
The world is a structure that represents the state of the game.  At any
given time, we must know the current food and the current worm.


N.B.: `world' is a reserved word in ACL2, and so we cannot use
      (defstructure world ...) to create the datatype.
|#
(defstructure the-world
  (seed (:assert (posp seed)))
  (worm (:assert (worm-p worm)))
  (food (:assert (food? food))))
;; for readability, we just rename the predicate:
(defun world? (w) (the-world-p w))
#|
We must also define three functions:
* world-next : World -> World
world-next will be called every time the clock ticks.  Its job is to produce
a new world by moving the worm one step.  It might also produce the end-of-game
world if it detects that the worm is out of bounds or has eaten itself.

* world-change : World Key -> World
world-change is responsible for updating the world when a keypress is detected.
(The arrow keys will control the direction of the worm.)

* world-image : World -> Image
world-image is responsible for drawing a world.  It will be called whenever the
world changes.

We first define a few helper functions:
|#

;; nat->string : natural-number -> string
;; Produce a string representing the given number in base 10.
(defun nat->string (num)
;; N.B.:  ACL2 version 2.9.2 has explode-nonnegative-integer, but it only 
;; consumes two arguments.  Omit the `10' if you want to submit this to 
;; version 2.9.2 of ACL2.
;; The DrScheme/ACL2 package implements version 2.9.3 of ACL2.  If you
;; wish simply to run this code, leave the `10' present.
  (if (natp num)
      (let ((chars (explode-nonnegative-integer num 10 nil)))
        (coerce chars 'string))
      "nat->string:  given a non-number"))

#|
;; stop : String World -> World
;; Produce the final world by calling `end-of-time' from the World teachpack.  
;; It generates a message indicating the score.
(defun stop (msg w)
  (end-of-time
   (concatenate 'string
                msg 
                " (score: " (nat->string (len (worm-body w))) ")")))
|#

;; World -> Boolean
;; Is the worm close to the food in the given world?
(defun worm-close-to-food? (w)
  (worm-close-to? (the-world-worm w)  (food-posn (the-world-food w))))

;; game-over : World -> Boolean
;; Did the worm crash into a wall or itself?
(defun game-over (w)
  (or (worm-outside? (the-world-worm w))
      (worm-ate-self? (the-world-worm w))))

;; world-next : World -> World
;; Produce the next world from the given one by moving the worm one step.
;; If the world is out of the playing field or has eaten itself, game-over.
;; If the world is near food, it eats the food and a new food will be placed.
(defun world-next (u)
  (let ((s (the-world-seed u))
        (w (the-world-worm u))
        (f (the-world-food u)))
    (cond
;;      ((worm-outside? w) (stop "the worm hit the wall" w))
;;      ((worm-ate-self? w) (stop "the worm ate itself" w))
      ((worm-close-to-food? u) (the-world (next-seed (next-seed s))
                                          (worm-move/eat w) 
                                          (new-food s)))
      (t (the-world s (worm-move w) f)))))

;; world-change : World (union characterp velocity?) -> World
;; Produce a new world where the direction of the worm is altered according
;; to the arrow key pressed.  Other keys are ignored.
(defun world-change (w key)
  (cond ((characterp key) w)
        ((velocity? key)
         (let ((wrm (the-world-worm w)))
           (the-world (the-world-seed w)
                      (worm-change wrm key)
                      (the-world-food w))))
        (t w)))

;; world-image : World -> Image
;; Produce an image of the given world.
(defun world-image (w)
  (worm-image (the-world-worm w) (food-image (the-world-food w) (empty-scene *WIDTH* *HEIGHT*))))
;;; END OF WORLD

#| *** RUN ***
Here is the code that gets the game started.  We create an initial world with
the worm in the middle right of the playing field and the initial food.
After that, we inform the World Teachpack about the functions that it should
use to update the world on clock ticks and keypresses.  We also tell it how
to draw the world.
|#
(defconst *initial-world* 
  (the-world (next-seed (next-seed (initial-seed)))
             (worm-new 'left *WIDTH* (nonnegative-integer-quotient *HEIGHT* 2))
             *initial-food*))
#|
Now we get the ball rolling by calling big-bang.  It consumes the width and
height of the playing field, a number indicating how often the clock ticks, and
the initial world.  In this case, the clock ticks every 1/10 second.
|#
(big-bang *WIDTH* *HEIGHT* 1/5 *initial-world*)

;; Every time the world changes, the it must be redrawn.  We provide
;; on-redraw with the function that produces an image given a world.
(on-redraw world-image)

;; At each clock tick, the worm must move a step in the direction it faces.
;; on-tick-event consumes the function that takes the world and produces the
;; next world.
(on-tick-event world-next)

;; When a key is pressed, the world changes (the arrow keys change the
;; direction of the worm, for example).  on-key-event consumes the function
;; that produces a new world given the current world and a keyboard input.
(on-key-event world-change)

;; End the game when it's over!
(stop-when game-over)

#| *** THEOREMS ***
|#
;; We begin with an easy result:
;; Worm move preserves the structure of the worm.
;; N.B., worm-p does not check that the segments are adjacent
(defthm worm-move-preserves-worm-p
  (implies (worm-p w)
           (worm-p (worm-move w))))

;;;
;;; ADJACENT?
;;;
(defthm adjacent?-s/move-s
  (implies (velocity? velocity)
           (adjacent? seg (segment-move seg velocity))))

(defthm adjacent?-move-s/s
  (implies (velocity? velocity)
           (adjacent? (segment-move seg velocity) seg)))

(defthm cons-preserves-consecutive-segments-adjacent?
  (implies (and (adjacent? s (car los))
                (consecutive-segments-adjacent? los))
           (consecutive-segments-adjacent? (cons s los))))
;; We can also prove that adjacent commutes, but the theorem
;; is not used in the results below.

;; We disable adjacent? to prevent the prover from trying to do
;; arithmetic whenever it occurs.  All the properties that we need
;; of adjacent? should be proved above.

;; We also disable segment-move so that the rewrite rules adjacent?-s/move-s
;; will fire before the prover rewrites the call to segment-move with
;; its definition.
(in-theory (disable adjacent? segment-move))

;;;
;;; The next 3 theorems rewrite functions that use accumulators into 
;;; ones that do not.  ACL2 has a hard time reasoning about the former.
;;;

;; reverse will rewrite into revappend by default (the accumulator-
;; style reverse).  We prefer structural recursion for reasoning.
(defthm reverse/nil
  (equal (reverse nil) nil))

(defthm reverse/cons
  (equal (reverse (cons a b))
         (append (reverse b) (list a))))
(in-theory (disable reverse)) ; hide the accumulator-style definition

;; Similarly for first-n-ac.
(defthm first-n-ac/eliminate-accumulator
  (implies (and (true-listp acc)
                (<= n (len l)))
           (equal (first-n-ac n l acc)
                  (append (reverse acc) (firstn n l)))))

;; When (firstn n L) is non-empty, its car is just that of L
(defthm car/firstn
  (implies (firstn n L)
           (equal (car (firstn n L))
                  (car L))))

;; When the worm moves, we drop the last segment of the tail.
;; This of course preserves that the segments are all adjacent.
(defthm firstn-preserves-consecutive-segments-adjacent?
  (implies (consecutive-segments-adjacent? segs)
           (consecutive-segments-adjacent?
            (firstn n segs))))

;; Finally, we prove an interesting property:
(defthm worm-move-preserves-well-formedness
  (implies (and (worm-p w) (worm-well-formed? w))
           (worm-well-formed? (worm-move w)))
  :hints (("Goal" :in-theory (enable butlast))))

(defun worm-overlaps? (w)
  (let ((head (worm-head w))
        (tail (worm-body w)))
    (not (no-duplicatesp-equal (cons head tail)))))

(defun body-overlaps? (w)
  (not (no-duplicatesp-equal (worm-body w))))

(defthm butlast-clause-1
  (implies (<= (len xs) k)
           (equal (butlast xs k) nil))
  :hints (("Goal" :in-theory (enable butlast))))

(defthm butlast-clause-2
  (implies
   (and (< k  (len xs)) (natp k))
   (equal (butlast (cons x xs) k)
          (cons x (butlast xs k))))
  :hints (("Goal" :in-theory (enable butlast))))

(defun butlast/recursive (xs k)
  (cond
    ((not (natp k)) nil)
    ((<= (len xs) k) nil)
    (t (cons (car xs) (butlast/recursive (cdr xs) k)))))

(defthm butlast=butlast/recursive
  (implies (and (true-listp xs)
                (natp k))
           (equal (butlast xs k) (butlast/recursive xs k)))
  :hints (("Goal" :in-theory (enable butlast))))

(defthm member-equal/butlast/recursive
  (implies (and (true-listp xs)
                (natp k)
                (not (member-equal x xs)))
           (not (member-equal x (butlast/recursive xs k)))))

(defthm no-duplicates/butlast/recursive
  (implies (and (true-listp xs)
                (natp k)
                (<= k (len xs))
                (no-duplicatesp-equal xs))
           (no-duplicatesp-equal (butlast/recursive xs k))))

(defthm no-duplicates/butlast
  (implies (and (true-listp xs)
                (natp k)
                (<= k (len xs))
                (no-duplicatesp-equal xs))
           (no-duplicatesp-equal (butlast xs k)))
  ;:hints (("Goal" :in-theory (e/d (butlast) ())))
  )

(defthm worm-move-preserves-uncrossed-tail
  (implies (and (worm-p w) (not (worm-ate-self? w)) (not (body-overlaps? w)))
           (not (body-overlaps? (worm-move w)))))

(defthm worm-move/eat-preserves-uncrossed-tail
  (implies (and (worm-p w) (not (worm-ate-self? w)) (not (body-overlaps? w)))
           (not (body-overlaps? (worm-move/eat w)))))

(defthm world-next-preserves-uncrossed-tail
  (implies (and (world? u)
                (not (worm-ate-self? (the-world-worm u)))
                (not (body-overlaps? (the-world-worm u))))
           (not (body-overlaps? (the-world-worm (world-next u))))))

(defthm key-event-preserves-uncrossed-tail
  (implies (and (world? u)
                (not (worm-ate-self? (the-world-worm u)))
                (not (body-overlaps? (the-world-worm u)))
                (key-eventp k))
           (not (body-overlaps? (the-world-worm (world-change u k))))))

(defthm world-next-preserves-well-formedness
  (implies (and (world? u)
                (not (worm-ate-self? (the-world-worm u)))
                (not (body-overlaps? (the-world-worm u)))
                (worm-well-formed? (the-world-worm u)))
           (worm-well-formed? (the-world-worm (world-next u))))
  :hints (("Goal" :in-theory (enable butlast))))

#|
Combined with the fact that the initial worm is well-formed, this constitutes
a significant safety property of the program.
|#

#| *** EXERCISES ***
1.  Try to prove that worm-eat preserves well-formedness.
|#
