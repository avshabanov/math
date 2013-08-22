;;
;; Experimentations on the partial factorizations


;; Depending on primes in the same dir
#+repl (load "primes.lisp")

(defun produce-partial-factorizations (limit)
  (declare (type integer limit))
  (let* ((primes (produce-primes 1 (+ (floor (sqrt limit)) 1)))
	 (last-prime-index (- (length primes) 1))
	 (productions (make-array (+ limit 1) :element-type 'bit))
	 (liouville-sum 1))
    (labels ((productions-for-prime (index prev-production odd-factors)
	       (declare (type integer index)
			(type integer prev-production)
			(type boolean odd-factors))
	       (setf (aref productions prev-production) 1)
	       (incf liouville-sum (if odd-factors -1 1))
	       (loop for i from index to last-prime-index do
		    (let ((production (* prev-production (aref primes i))))
		      (if (<= production limit)
			  (progn
			    (assert (= 0 (aref productions production)))
			    (productions-for-prime i production (not odd-factors))))))))
      (setf (aref productions 1) 1)	; 1 is always factorized
      (loop for i from 0 to last-prime-index do
	   (productions-for-prime i (aref primes i) t)))
    (values
     (loop for i from 0 to limit
	 when (= 1 (aref productions i)) collect i)
     liouville-sum)))

#+repl (produce-partial-factorizations 9)
#+repl (produce-partial-factorizations 25)
#+repl (produce-partial-factorizations 49)

#+repl (loop for i from 2 to 10000 do
	    (multiple-value-bind (factors liouville-sum) (produce-partial-factorizations i)
	      (declare (ignore factors))
	      (format t "For n = ~S liouville sum = ~S~%" i liouville-sum)))


