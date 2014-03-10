;;
;; Calculating Logarithmic Integral using Ramanujan series representation


;; Euler-Mascheroni Gamma Constant
;; 0.57721566490153286060651209008240243104215933593992
(defconstant emg 0.57721566490153286060d0)

(defun factorial (n)
  (declare (type integer n))
  (if (> n 1) (the integer (* n (factorial (- n 1)))) 1))

(defconstant +li-iterations+ 40)

;; optimized, self-sufficient log integral
(defun stdli (x &optional (iterations 20))
  (let ((lnx (log x)) (fn 1) (mo -1) (lnxn 1) (sum 0) (pow2 0) (ksum 0))
    (loop for n from 1 to iterations do
          (progn
            (setf pow2 (if (> pow2 0) (* pow2 2) 1)) ; pow2 = 2^(n - 1)
            (setf fn (* fn n)) ; fn = n!
            (setf mo (- mo)) ; mo = (-1)^n
            (setf lnxn (* lnxn lnx)) ; lnxn = (ln(x))^n
            (setf ksum (+ ksum (if (oddp n) (/ 1 n) 0)))
            ;;(format t "vars = ~S~%" (list :lnxn lnxn :mo mo :fn fn :ksum ksum))
            (setf sum (+ sum (* (/ (* mo lnxn) (* fn pow2)) ksum)))))
    ;; gamma + ln(ln(x)) + sqrt(x) * sum
    (+ emg (log lnx) (* sum (sqrt x)))))

;; Exponential integral
(defun ei (x &optional (iterations 100))
  (let ((nf 1) (mo -1) (xn 1) (sum 0) (pow2 0) (ksum 0))
    (loop for n from 1 to iterations do
          (progn
            (setf pow2 (if (> pow2 0) (* pow2 2) 1)) ; pow2 = 2^(n - 1)
            (setf nf (* nf n)) ; fn = n!
            (setf mo (- mo)) ; mo = (-1)^n
            (setf xn (* xn x)) ; xn = x^n
            (setf ksum (+ ksum (if (oddp n) (/ 1 n) 0)))
            (setf sum (+ sum (* (/ (* mo xn) (* nf pow2)) ksum)))))
    ;; gamma + ln(ln(x)) + sqrt(x) * sum
    (+ emg (log x) (* sum (exp (/ x 2))))))

;; ExpIntegralEi[2] = 4.9542343560018901633795051302270352755180535624200420
;; (ei 2.0d0)       = 4.95423435600189d0
;; 
;; (ei (* (log 20.0d0) #C(0.5d0 14.134725141734693790d0))) =
;; (ei #C(1.4978661367769954d0 42.34385228490963d0))
;;    ~= #C(-0.10538411230595734d0 3.1474874894249703d0) - correct up to 6 significant digits
;;    
;; WolframAlpha>
;;    ~= ExpIntegralEi[ZetaZero[1] Log[20]]
;;    ~= -0.105384043860940+3.147487477166136 i
;;

;; unoptimized log-integral
(defun log-integral (x)
  "Calculates Logarithm Integral by using straightforward implementation of the
Ramanujan series"
  ;;(setf x (coerce x 'double-float))  
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
#+repl (let ((v (log-integral (coerce 1000000 'double-float))))
	 (format t "li(1000000) = ~S~%" v))

;; li(2 + i) = 1.411259042017801005684... + 1.224706938410302713497 * i
#+repl (let ((v (log-integral #C(2.0d0 1.0d0))))
	 (format t "li(2 + i) = ~S~%" v))


