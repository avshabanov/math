;;
;; Calculating Logarithmic Integral using Ramanujan series representation


;; Euler-Mascheroni Gamma Constant
(defconstant emg 0.57721566490153286060d0)

(defun factorial (n)
  (declare (type integer n))
  (if (> n 1) (the integer (* n (factorial (- n 1)))) 1))

(defconstant +li-iterations+ 40)

(defun log-integral (x)
  "Calculates Logarithm Integral by using straightforward implementation of the
Ramanujan series"
  (setf x (coerce x 'double-float))  
  (+ emg
     (log (log x))
     (*
      (sqrt x)
      (loop for n from 1 to +li-iterations+ sum
	   (* (/ (* (if (oddp n) 1 -1) (expt (log x) n))
		 (* (factorial n) (expt 2 (- n 1))))
	      (loop for k from 0 to (floor (/ (- n 1) 2)) sum
		   (/ 1.0d0 (+ (* 2 k) 1))))))))


;; li(1000000) = 78627.549159462181919862910747947261161321874382421767 (wolframalpha)
#+repl (let ((v (log-integral 1000000)))
	 (format t "li(1000000) = ~S~%" v))


