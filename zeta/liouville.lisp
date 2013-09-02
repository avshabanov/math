;; Optimized, fast calculation of all the values of the liouville function not exceeding the given limit.
;;


(defun liouville-values (limit)
  "Returns values of the liouville function from 0, inclusive, to limit, exclusive.
Time complexity is O(N * sum(k for 1 to N, k^-1)),
Space complexity is O(N)."
  (declare (type integer limit))
  ;; lv values array initialized with illegal arguments
  (let ((lv-values (make-array limit :element-type 'integer :initial-element 0))
        #+repl2 (misses 0) #+repl2 (total 0))
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
		    #+repl1 (format t "~S x ~S (~S)~%" num i prev-lv-value)
                    #+repl2 (if (= 0 prev-lv-value) (incf misses))
                    #+repl2 (incf total)
		    (unless (= 0 prev-lv-value)
		      (let ((new-product (* i num)))
			(add-product new-product (* prev-lv-value -1)))))))))
    #+repl2 (format t "N: ~S, Misses: ~S, Total: ~S, Ratio: ~S~%" (- limit 1)
                    misses total (coerce (/ st total) 'float))
    ;; return calculated lv values
    lv-values))

#|
Statistics on the current algorithm:

N: 10, Misses: 2, Total: 7, Ratio: 0.2857143
N: 100, Misses: 72, Total: 146, Ratio: 0.49315068
N: 1000, Misses: 1127, Total: 1958, Ratio: 0.57558733
N: 10000, Misses: 14301, Total: 23071, Ratio: 0.6198691
N: 100000, Misses: 166401, Total: 256808, Ratio: 0.6479588
N: 1000000, Misses: 1853709, Total: 2775210, Ratio: 0.6679527
N: 10000000, Misses: 20130318, Total: 29465738, Ratio: 0.6831771
|#

#+repl (liouville-values 11)
#+repl (format t "lv=~S~%" (liouville-values 100))

#+repl (let* ((n 100000) (v (liouville-values (+ n 1))))
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