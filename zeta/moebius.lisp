;;
;; Möbius function summations.
;; 
;; odd prime factors: -1, even prime factors: 1, square prime: 0

#+repl (declaim (optimize (safety 0) (debug 0) (speed 3) (space 2)))

(defun build-squarefree-products (limit)
  (declare (type integer limit))
  (let* ((sentinel (+ limit 1))
         (arr (make-array (+ 1 limit) :element-type 'fixnum :initial-element sentinel)))
    (setf (aref arr 0) 0)
    (setf (aref arr 1) 1)
    (loop for i from 2 to limit do
          (when (= sentinel (aref arr i))
            (setf (aref arr i) (- i))
            ;; setf product of the next primes
            (loop for j from 2 to (min (- i 1) (floor (/ limit i))) do
                  (let ((e (aref arr j)))
                    #+repl (format t "## i=~S, j=~S, target=~S~%" i j (min (- i 1) (floor (/ limit i))))
                    (unless (= sentinel e)
                      (let* ((next (* e (- i))) (index (abs next)))
                        (if (<= index limit)
                          (setf (aref arr index) next))))))
            ;; setf to zero all the other square factors
            (loop with s = (* i i) for j from s to limit by s do
                  (setf (aref arr j) 0))))
    arr))

;; Represents moebius "mu" function - e.g. http://www.wolframalpha.com/input/?i=mu%5B9998%5D
;; builds moebius sums for each element from 0 to limit, inclusive.
(defun build-moebius-distribution (limit)
  (loop
    with products = (build-squarefree-products limit)
    for i from 0 to limit do
    (let ((elem (aref products i)))
      (setf (aref products i)
            (cond
              ((= elem 0) 0)
              ((> elem 0) (progn
                            ;; additional paranoidal verification
                            (if (> elem limit) (error "FATAL: element is greater than limit"))
                            1))
              (t -1))))
    finally (return products)))

;;
;; REPL test

#+repl (build-moebius-distribution 20)

#+repl (let ((mu (build-moebius-distribution 10000)))
         (assert (= (aref mu 10) 1))
         (assert (= (aref mu 117) 0))
         (assert (= (aref mu 598) -1))
         (assert (= (aref mu 2001) -1))
         (assert (= (aref mu 5007) 1))
         (assert (= (aref mu 9998) 1))
         (format t "OK~%"))

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
