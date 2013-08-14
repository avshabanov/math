
;; optimizations

;;(declare (optimize (safety 3) (debug 3) (speed 0) (space 0)))
;; ^- for functions
;;
;;(sb-ext:restrict-compiler-policy 'debug 3)
;; ^- global, sbcl
;;
;;(declaim (optimize (safety 3) (debug 3) (speed 0) (space 0)))
;; ^- global
#+repl (declaim (optimize (safety 0) (debug 0) (speed 3) (space 2)))



(defun count-of-primes (from to)
  "Finds count of primes that are located between the given
fix number (i.e. integer) arguments; from inclusive, to exclusive.
Uses 'Sieve of Erathosphen' algorithm adapted to common lisp"
  (declare (type fixnum from) (type fixnum to))
  (assert (>= to from) (to from)
	  "`to'=~S argument should be greater than `from'=~S argument" to from)
  (let* ((limit to) ; Max expected primes
	 (primes (make-array limit :element-type 'bit))
	 (count 0))
    ;; now initialize the first non-primes that pretend to be primes - 0 and 1.
    (setf (aref primes 0) 1)
    (setf (aref primes 1) 1)
    
    (loop for i from 0 to (- limit 1) do
	 (if (= 0 (aref primes i))
	     (loop for j from (* i i) to (- limit 1) by i do
		  (setf (aref primes j) 1))))

    (loop for i from from to (- to 1) do
	 (if (= 0 (aref primes i)) (incf count)))
    
    ;; return the result
    (values count primes)))

(defun produce-primes (from to)
  (multiple-value-bind (count primes-bitset) (count-of-primes from to)
    (let ((result (make-array count :element-type 'number)))
      (loop for i from from to (- to 1) with j = 0 do
           (if (= 0 (aref primes-bitset i))
               (progn
                 (setf (aref result j) i)
                 (incf j))))
      result)))

#+repl (produce-primes 2 10)
#+repl (produce-primes 2 11)
#+repl (produce-primes 0 12)
#+repl (produce-primes 1990 2020)

;; Memory-friendly version of count-of-primes
#+repl (defun count-of-primes2 (from to)
  (declare (type number from) (type number to))
  (assert (>= to from) (to from)
          "`to'=~S argument should be greater than `from'=~S argument" to from)
  (let* ((limit (floor (sqrt to)))
         (known-primes (produce-primes 0 limit))
         (count 0))

    (flet ((is-prime (num)
             (loop for pn being the elements of known-primes do
                  (if (> pn num) (return-from is-prime nil))
                  (if (not (= 0 (mod num pn))) (return-from is-prime nil)))
             t))
      (loop for i from from to (- to 1) do
         (if (is-prime i) (incf count))))
    
    count))

#+repl (count-of-primes2 0 100)

;; Test
#+repl (progn
	 (assert (= 4 (count-of-primes 0 10))) ; primes: 2, 3, 5, 7
	 (assert (= 168 (count-of-primes 0 1000)))
	 (assert (= 1061 (count-of-primes 1000 10000))))

;; Performance (tougher) test
#+repl (progn
	 (assert (= 75 (count-of-primes 1000000 1001000))))

#+repl (count-of-primes 0 10)
#+repl (let ((n (count-of-primes 0 1000)))
	 n)




;;
;; Repl tests
;;


#+repl (let ((a (make-array 10 :element-type 'bit)))
	 (setf (aref a 0) 1)
	 a)

#+repl (let ((a (make-array 10 :element-type 'fixnum)))
	 (setf (aref a 0) 2)
	 (setf (aref a 1) 3)
	 (format t "a = ~a~%" a)
	 (values))