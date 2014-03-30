#|
This is a simple program that uses the World teachpack to illustrate how to
build a program that responds to keyboard events.  Run the program, and then
try pressing some keys.  The program will print the events that it has
received into a window.

For purposes of illustrating a simple preservation theorem, we limit the window
to displaying at most 500 characters of output.  The theorem at the bottom
simply verifies that the program's output is bounded above at every clock tick.
|#

(include-book "world" :dir :teachpacks)

;; World = String
(defconst *width* 500) ;; the initial world
(defconst *world0* "") ;; the width of the world display

;; World KeyEvent -> World
;; add the event to the world, with tag
(defun echo (w ke)
  (cond
    ((symbolp ke) 
     (string-append w (string-append "symbol " (string ke))))
    (t (string-append w (string-append "char " (string ke))))))

;; World -> World
;; truncate a world that has become too large
(defun shorten (w)
  (cond
    ((> (image-width (text w 11 'red)) *width*) "")
    (t w)))

;; World -> Image
;; Draws the world by simply rendering the string using font size 11 and
;; color red.
(defun image (w) (text w 11 'red))

;; run program run
(big-bang *width* 20 1/10 *world0*)
(on-tick-event shorten)
(on-key-event echo)
(on-redraw image)

(defthm world-size-is-bounded-above
  (implies (stringp w)
           (<= (shorten w) *width*)))
