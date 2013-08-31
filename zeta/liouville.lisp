;; Optimized, fast calculation of all the values of the liouville function not exceeding the given limit.
;;


(defun liouville-values (limit)
  "Returns values of the liouville function from 0, inclusive, to limit, exclusive.
Time complexity is O(N * sum(k for 1 to N, k^-1)),
Space complexity is O(N)."
  (declare (type integer limit))
  ;; lv values array initialized with illegal arguments
  (let* ((lv-values (make-array limit :element-type 'integer :initial-element 0)))
    (setf (aref lv-values 1) 1) ; 1 has no prime factors
    (flet ((add-product (num lv-value)
             (declare (type integer num) (type integer lv-value))
             (assert (= 0 (aref lv-values num))
                     (num) "Number ~S factorized twice" num)
             ;; put new non-zero lv value
             (setf (aref lv-values num) lv-value)))
      (loop for num from 2 to (- limit 1) do
           (when (= 0 (aref lv-values num))
	     ;; add current product (prime number, one factor - itself)
             (add-product num -1)
	     ;; add all the possible derivative products
             (loop for i from 2 to (floor (/ (- limit 1) num)) do
		  (let ((prev-lv-value (aref lv-values i)))
		    #+repl (format t "~S x ~S (~S)~%" num i prev-lv-value)
		    (unless (= 0 prev-lv-value)
		      (let ((new-product (* i num)))
			(add-product new-product (if (> prev-lv-value 0) -1 1)))))))))
    ;; return calculated lv values
    lv-values))


#+repl (liouville-values 11)
#+repl (format t "lv=~S~%" (liouville-values 100))

#+repl (let ((v (liouville-values (+ n 1))))
	   (loop for e being the element in v sum e))

;; Official sequence at http://oeis.org/A008836
#+repl (defparameter *sample* (list 0 1 -1 -1 1 -1 1 -1 -1 1 1 -1 -1 -1 1 1 1 -1 -1 -1 -1
				    1 1 -1 1 1 1 -1 -1 -1 -1 -1 -1 1 1 1 1 -1 1 1 1 -1 -1
				    -1 -1 -1 1 -1 -1 1 -1 1 -1 -1 1 1 1 1 1 -1 1 -1 1 -1
				    1 1 -1 -1 -1 1 -1 -1 -1 -1 1 -1 -1 1 -1 -1 -1 1 1 -1
				    1 1 1 1 1 -1 1 1 -1 1 1 1 1 -1 -1 -1 1 -1))
#+repl (equal *sample* (loop for e being the element in (liouville-values 102) collect e))

#+repl (defun l-sum (n)
	 (let ((v (liouville-values (+ n 1))))
	   (loop for e being the element in v sum e)))