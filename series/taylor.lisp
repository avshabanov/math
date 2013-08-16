;;
;; Introducing generic algorithm that calculates Taylor series for
;; arbitrary function by using straight calculation.
;;
;; The provided file contains also a version of Taylor (Maclauren) series
;; that might be calculated with the arbitrary precision by using lisp ratios.


#+repl (declaim (optimize (safety 0) (debug 0) (speed 3) (space 2)))

;; used in Taylor series
(defun factorial (n)
  "Calculates factorial of the given non-negative integer number."
  (declare (type integer n))
  (assert (>= n 0) (n) "n=~S is negative" n)
  (if (= n 0) 1 (the integer (* n (factorial (- n 1))))))

#+repl (factorial 10)

;; Simple implementation
(defun maclaurin-series-calculator (derivative-cst-fn &key (steps 10))
  "Returns function that calculates Maclaurin series (Taylor series with a = 0).
This function is well suited only for small values of argument x,
where -1 < x < 1. If |x| >> 1 the function will produce increasing error."
  (declare (type integer steps) (type function derivative-cst-fn))
  (lambda (x)
    (setf x (coerce x 'double-float))
    (loop for n from 0 to (- steps 1) sum
         (/ (* (funcall derivative-cst-fn n) (expt x n)) (factorial n)))))


;; Test maclaurin calculator for sinus
#+repl (let ((sin-fn (maclaurin-series-calculator
		      (lambda (step) (if (evenp step) 0
					 (if (= 1 (mod step 4)) 1 -1))))))
	 (flet ((calc (val)
		  (format t "Calculated sin(~S) = ~S, intrinsic sin = ~S~%"
			  val (funcall sin-fn val) (sin val))))
	   (calc 0.1d0)
	   (calc 0.5d0)
	   (calc (/ pi 6))
	   (calc (/ pi 3))))

;;
;; =========================================================================================
;;

;; Macro-generated version that works with ratios thus allows:
;; * arbitrary precison.
;; * relatively quick execution on ARM (or any kind of hardware without FPU).

;; TODO: rework as taylor series so that it will be possible to operate with the
;; arbitrary starting coefficient.
(defmacro def-maclaurin-fn (name derivative-cst-fn &key (steps 10))
  (declare (type integer steps))
  (let* ((x (gensym "x"))       ; source variable that holds the value of function to be calculated
	 (xpow (gensym "xpow"))         ; where the power of `x' will be accumulated
	 (result (gensym "result"))     ; result that holds the summation the series summation
	 (calculation-forms
	  (apply #'append
		 (loop for n from 0 to steps collect
                      ;; precalculated coefficient == f'(a) / 1!, f''(a) / 2!, f'''(a) / 3! etc.
		      (let ((coef (/ (eval `(funcall ,derivative-cst-fn ,n))
				     (factorial n))))
                        (check-type coef (or integer ratio) "non-integer or ratio value")
                        ;; generate plain series of:
                        ;;   incf... - result accumulating sequences
                        ;;   setf... - power of x calculation sequences
			(append
			 (unless (= 0 coef)
			   (list `(incf ,result (* ,coef ,xpow))))
			 (unless (= n steps)
			   (list `(setf ,xpow (* ,xpow ,x))))))))))
    `(defun ,name (,x)
       (declare (type (or ratio integer) ,x))
       (let ((,xpow 1)
	     (,result 0))
	 ,@calculation-forms
	 ,result))))

#+repl (macroexpand-1 '(def-maclaurin-fn test2
			(lambda (step) (if (evenp step) 0
					(if (= 1 (mod step 4)) 1 -1)))))

;; Calculates sinus by operating on ratios (no floating point!)
(def-maclaurin-fn ratio-sin
    (lambda (step) (if (evenp step) 0
		       (if (= 1 (mod step 4)) 1 -1)))
  :steps 18)

;; Calculating e^x
(def-maclaurin-fn ratio-e
    (lambda (step) (declare (ignore step)) 1) :steps 18)

;; pi with 50 significant digits in a form of the rational number approximation
(defconstant +PI50+
  31415926535897932384626433832795028841971693993751/10000000000000000000000000000000000000000000000000)

;; sin pi/6 == 1/2
#+repl (let ((sin-pi/6 (ratio-sin (/ +PI50+ 6))))
	 (format t "maclaurin(sin pi/6):~% :: ratio  = ~S~% :: float = ~S~% :: real  = ~S~%"
		 sin-pi/6 (coerce sin-pi/6 'double-float) (sin (/ pi 6))))

;; e^1 == 2.718281828...
#+repl (let ((e1 (ratio-e 1)))
	 (format t "maclaurin(e^1):~% :: ratio  = ~S~% :: float  = ~S~% :: real e = ~S~%"
		 e1 (coerce e1 'double-float) (exp 1.0d0)))



