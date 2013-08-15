;;
;; Introducing generic algorithm that calculates Taylor series for
;; arbitrary function by using straight calculation.

;; TODO: cache
(defun factorial (n)
  "Calculates factorial of the given non-negative integer number."
  (declare (type integer n))
  (assert (>= n 0) (n) "n=~S is negative" n)
  (if (= n 0) 1 (* n (factorial (- n 1)))))

#+repl (factorial 10)

;; Straightforward implementation
(defun maclaurin-series-calculator (derivative-cst-fn &key (steps 10))
  "Returns function that calculates Maclaurin series (Taylor series with a = 0).
This function is well suited only for small values of argument x,
where -1 < x < 1. If |x| >> 1 the function will produce increasing error."
  (declare (type integer steps) (type function derivative-cst-fn))
  (lambda (x)
    (let ((result 0.0)
	  ;; accumulator of the power of x
	  (xpow 1.0))
      (loop for n from 0 to (- steps 1) do
	   (let ((derivative-val (funcall derivative-cst-fn n)))
	     (unless (= 0 derivative-val)    
	       (incf result (/ (* derivative-val xpow) (factorial n))))
	     ;; optimized n-th power of x, or just x^n
	     (setf xpow (* xpow x))))
      result)))


;; Test maclaurin calculator for sinus
#+repl (let ((sin-fn (maclaurin-series-calculator
		      (lambda (step) (if (evenp step) 0
					 (if (= 1 (mod step 4)) 1 -1))))))
	 (flet ((calc (val)
		  (format t "Calculated sin(~S) = ~S, intrinsic sin = ~S~%"
			  val (funcall sin-fn val) (sin val))))
	   (calc 0.1)
	   (calc 0.5)
	   (calc (/ 3.1415926 6))
	   (calc (/ 3.1415926 3))))

;; Compile-generated version that works with fractions thus allows:
;; * arbitrary precison.
;; * relatively quick execution on ARM processors.

(defmacro def-maclaurin-fn (name derivative-cst-fn &key (steps 10))
  (declare (type integer steps))
  (let* ((x (gensym "x"))
	 (xpow (gensym "xpow"))
	 (result (gensym "result"))
	 (calculation-forms
	  (apply #'append
		 (loop for n from 0 to steps collect
		      (let ((coef (/ (eval `(funcall ,derivative-cst-fn ,n))
				     (factorial n))))
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
		       (if (= 1 (mod step 4)) 1 -1))))

;; Calculating e^x
(def-maclaurin-fn ratio-e
    (lambda (step) 1))

(defconstant +PI+ 31415926535897932/10000000000000000)

;; sin pi/6 == 1/2
#+repl (let ((sin-pi/6 (ratio-sin (/ +PI+ 6))))
	 (format t "maclaurin(sin PI/6):~% :: approx = ~S~% :: float = ~S~%"
		 sin-pi/6 (* 1.0 sin-pi/6)))

;; e^1 == 2.718281828...
#+repl (let ((e1 (ratio-e 1)))
	 (format t "maclaurin(e^1):~% :: approx = ~S~% :: float = ~S~%"
		 e1 (* e1 1.0)))



