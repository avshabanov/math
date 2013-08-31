;;
;; Fast implementation for retrieving the values of Möbius function
;; for the natural numbers sequence.
;;
;; This implementation conforms to the "official" definition of this function:
;; http://en.wikipedia.org/wiki/M%C3%B6bius_function


(defun upper-bound-count-of-primes (limit)
  "Calculates an upper bound estimation for prime numbers in the range [0..limit],
excluding limit itself. The following formula is used to count such an upper bound:
pi(n) < [1.25506 * (n / ln(n))] for n >= 17."
  (declare (type integer limit))
  (if (< limit 17) limit
      ;; This might be improved to stick to the integer arithmetics only by
      ;; using precalculated values for natural logarithm -
      ;; as only 44 values are needed for 64-bit integer.
      (+ 1 (coerce (floor (/ (* 62753.0 limit) (* 50000.0 (log limit)))) 'integer))))

#+repl (upper-bound-count-of-primes 10)
#+repl (upper-bound-count-of-primes 100)
#+repl (upper-bound-count-of-primes 20000)

(defun produce-moebius-values (limit)
  (declare (type integer limit))
  (let* ((factorization-flags (make-array limit :element-type 'bit))
         ;; moebius values array initialized with illegal arguments
         (moebius-values (make-array limit :element-type 'integer :initial-element 2))
         ;; prime products (number, count of factors)
         (products (make-array limit))
         (product-count 0)
         last-product-index
         num-square)
    (setf (aref moebius-values 0) 0)    ; 0 - exceptional case
    (setf (aref moebius-values 1) 1)    ; 1 has no prime factors
    (flet ((add-product (num count-of-factors)
             (declare (type integer num) (type integer count-of-factors))
             (assert (= 0 (aref factorization-flags num))
                     (num) "Number ~S factorized twice" num)
             ;; set factorization flag for the new product
             (setf (aref factorization-flags num) 1)
             ;; put new non-zero moebius value
             (setf (aref moebius-values num) (if (oddp count-of-factors) -1 1))
             ;; introduce new product
             (setf (aref products product-count) (cons num count-of-factors))
             (incf product-count)))
      (loop for num from 2 to (- limit 1) do
           (when (= 0 (aref factorization-flags num))
             (setf last-product-index (- product-count 1))
             ;; set factorization flags for numbers with square factors
             (setf num-square (* num num))             
             (loop with square-factor = num-square
                while (< square-factor limit)
                do
                  (progn
                    ;; mark factorization flag
                    (setf (aref factorization-flags square-factor) 1)
                    ;; moebius value == 0 for numbers with squared prime factor
                    (setf (aref moebius-values square-factor) 0)
                    ;; proceed to the next square factor
                    (incf square-factor num-square)))
             ;; add current product (prime number, one factor - itself)
             (add-product num 1)
             ;; add all the derivative products
             (loop for i from 0 to last-product-index do
                  (destructuring-bind (product . count-of-factors) (aref products i)
                    (let ((new-product (* product num)))
                      #+repl (if (< new-product limit)
                                 (format t "~S x ~S = ~S, cf=~S~%"
                                         num product new-product
                                         (1+ count-of-factors)))
		      ;; add product that is not beyond limits;
		      ;; actually we have a room for optimizations here: if we can count
		      ;; on the sorted products collection we'd interrupt loop as soon as
		      ;; the product is greater than the limit; also we need not to search for
		      ;; a products for numbers greater than [limit/2].
                      (if (< new-product limit)
                          (add-product new-product (1+ count-of-factors)))))))))
    ;; return calculated moebius values
    (values moebius-values factorization-flags)))

;; Mertens function, see http://oeis.org/A028442
#+repl (defun mertens (n)
         (declare (type integer n))
         (let ((moebius-values (produce-moebius-values (+ n 1))))
           (loop for i from 1 to n sum (aref moebius-values i))))
;; M(x) is zero for: 2, 39, 40, 58, 65, 93, 101, 145, 149, 150,
;;                   159, 160, 163, 164, 166, 214, 231, 232, 235, 236, 238, 254,
#+repl (mertens 159)

#+repl (defun rest-as-list (arr)
         (rest (loop for n being the element in arr collect n)))

#+repl (produce-moebius-values 10)
#+repl (produce-moebius-values 78)
;; http://oeis.org/A008683
#+repl (format t "values = ~S" (produce-moebius-values 26))

#+repl (let* ((limit 100))
         (loop
              with v = (produce-moebius-values limit)
              with sum = 0
              for i from 1 to (- limit 1)
            do (progn
                 (incf sum (aref v i))
                 (format t "M(~S) = ~S~%" i sum))))

#+repl (defparameter *m78* (list 1 -1 -1 0 -1 1 -1 0 0 1 -1 0 -1 1 1 0 -1 0 -1 0 1 1 -1 0 0 1 0 0 -1 -1 -1 0 1 1 1 0 -1 1 1 0 -1 -1 -1 0 0 1 -1 0 0 0 1 0 -1 0 1 0 1 1 -1 0 -1 1 0 0 1 -1 -1 0 1 -1 -1 0 -1 1 0 0 1))
