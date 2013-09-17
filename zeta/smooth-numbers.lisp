;;
;; Experimentation with smooth numbers


(defun smooth-numbers-count (numbers upper-bound)
  (declare (type integer upper-bound))
  (let ((result (make-array (1+ upper-bound) :initial-element nil)))
    (loop for num in numbers do
	 (assert (null (aref result num)))
	 (setf (aref result num) (list 1))
	 (loop for k from 2 to (floor (/ upper-bound num)) do
	      (let ((k-info (aref result k)))
		(unless (null k-info)
		  (destructuring-bind (divisor-count) k-info
		    (let ((next-k (* k num)))
		      (assert (null (aref result next-k)))
		      (setf (aref result next-k) (list (1+ divisor-count)))))))))
    (values
     ;; total sum
     (loop
	with sum = 0
	for i being the element in result
	do (if i (incf sum))
	finally (return sum))
     ;; array with factors
     result)))


(defun ramanujan-smooth-3-num (p q n)
  (floor (/ (* (log (* p n) (log (* q n)))) (* 2 (log p) (log q)))))

#+repl (smooth-numbers-count '(2 3) 20)
#+repl (format t "count = ~S~%" (smooth-numbers-count '(2 3) 200))

#+repl (ramanujan-smooth-3-num 2 3 20)

