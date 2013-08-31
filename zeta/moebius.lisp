;;
;; Möbius function summations.

#+repl (declaim (optimize (safety 0) (debug 0) (speed 3) (space 2)))

#+repl (load "primes.lisp")

;; modified moebius function: only 1 and -1 values are taken into an account
(defun build-moebius-distribution (limit)
  (declare (type integer limit))
  (let* ((primes (produce-primes 1 limit))
	 (last-prime-index (- (length primes) 1))
	 (moebius-values (make-array limit :element-type 'fixnum))
	 (productions (make-array limit :element-type 'bit)))
    (labels ((fill-prime-productions (index prev-production odd-factors)
	       (declare (type integer index)
			(type integer prev-production)
			(type boolean odd-factors))
	       (setf (aref productions prev-production) 1)
	       (setf (aref moebius-values prev-production) (if odd-factors -1 1))
	       (loop for i from index to last-prime-index do
		    (let ((production (* prev-production (aref primes i))))
		      (if (< production limit)
			  (progn
			    (assert (= 0 (aref productions production)))
			    (fill-prime-productions i production (not odd-factors))))))))
      (setf (aref productions 1) 1)	; 1 is always factorized
      (setf (aref moebius-values 1) 1)	; 1 has zero prime factors, so count it as 1
      (loop for i from 0 to last-prime-index do
	   (fill-prime-productions i (aref primes i) t)))
    moebius-values))

#+repl (compile 'build-moebius-distribution)

;;
;; REPL test

#+repl (build-moebius-distribution 20)

#+repl (let ((moebius-values (build-moebius-distribution 100))
	     (liouville-sum 0))
	 (loop
	      for mv being the element of moebius-values
	      for index from 0
	      do
	      (incf liouville-sum mv)
	      (format t "LiouvilleSum(~S) = ~S, lim = ~S~%" index liouville-sum
		      (/ liouville-sum (sqrt index)))))


;; Dump big distribution to file
#+repl (progn
	 (format t "Start writing file...~%")
	 (with-open-file (stream "/tmp/moebius-distribution-big.txt" :direction :output)
	   (let ((moebius-values (build-moebius-distribution 10000000))
		 (liouville-sum 0))
	     (loop
		for mv being the element of moebius-values
		for index from 0
		do
		  (incf liouville-sum mv)
		  (if (> index 0)
		      (format stream "~S, ~S, ~S~%" index liouville-sum
			      (/ liouville-sum (sqrt index)))))))
	 (format t "DONE!~%"))
