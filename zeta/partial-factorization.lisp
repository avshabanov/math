;;
;; Experimentations on the partial factorizations


;; Depending on primes in the same dir
#+repl (load "primes.lisp")

(defun produce-partial-factorizations (limit &key (prime-upper-bound -1))
  (declare (type integer limit))
  (let* ((max-after-prime (+ (if (< prime-upper-bound 0) limit prime-upper-bound) 1))
	 (primes (produce-primes 1 max-after-prime))
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

#+repl (produce-partial-factorizations 9 :prime-upper-bound 3)
#+repl (produce-partial-factorizations 25 :prime-upper-bound 5)
#+repl (produce-partial-factorizations 49 :prime-upper-bound 7)

;; Sqrt upper bound
#+repl (loop for i from 10000 to 10010 do
	    (multiple-value-bind (factors liouville-sum)
		(produce-partial-factorizations i
						:prime-upper-bound (floor (sqrt i)))
	      (declare (ignore factors))
	      (format t "[SQRT] For n = ~S liouville sum = ~S, lim = ~S~%"
		      i liouville-sum (/ liouville-sum (sqrt i)))))

;; Regular upper bound
#+repl (loop for i from 10000 to 10010 do
	    (multiple-value-bind (factors liouville-sum)
		(produce-partial-factorizations i)
	      (declare (ignore factors))
	      (format t "[REG]  For n = ~S: liouville sum = ~S, lim = ~S~%"
		      i liouville-sum (/ liouville-sum (sqrt i)))))

