
(defun read-doubles-from-file (filename)
  (with-open-file (stream filename)
    (loop for line = (read-line stream nil 'eof)
          until (eq line 'eof)
          collect (read-from-string
                    (concatenate 'string (string-trim '(#\Space) line) "0d0")))))
;; (defparameter *zeta-zeroes* (read-doubles-from-file "zeta-im-zeroes.txt"))

(load "li.lisp")

(defconstant +li2+ (stdli 2.0d0))

;; Li(x) = li2(x) = li(x) - li(2)
(defun li2 (x) (- (stdli x) +li2+))

;; Count of primes
(load "primes.lisp")

;;
;; J(x) and periodic terms
;; J(x) is f(x) in http://mathworld.wolfram.com/RiemannPrimeCountingFunction.html
;;

;; calculates J(n) over count of primes function
(defun j-over-primes (n)
  (loop for k from 1 with x do (setf x (expt n (/ 1 k))) until (< x 2)
        sum (/ (count-of-primes 1 (+ 1 (floor x))) k)))





