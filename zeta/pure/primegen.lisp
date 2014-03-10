
#+repl (declaim (optimize (safety 3) (debug 3) (speed 0) (space 0)))
#+repl (declaim (optimize (safety 0) (debug 0) (speed 3) (space 2)))

(defun next-sieve-state (sieve-state)
  (let ((n (+ 1 (car sieve-state)))
        (s (loop for (prime counter) in (cdr sieve-state)
                 collect (list prime
                               (let ((counter (+ counter 1)))
                                 (if (= prime counter) 0 counter))))))
    (cons n (if 
              (= (loop for (prime counter) in s sum (if (= 0 counter) 1 0)) 0)
              ;; next prime - appears only if there is no prime counters
              ;; - their absence indicates, that n mod p != 0, which means that
              ;; n is a prime number.
              (cons (list n 0) s)
              ;; not a prime
              s))))

#+repl (next-sieve-state '(1))
#+repl (next-sieve-state '(3 (3 0) (2 1)))
#+repl (next-sieve-state *)

(defun recur-sieve-state (sieve-state n)
  (if (> n 0)
    (recur-sieve-state (next-sieve-state sieve-state) (- n 1))
    sieve-state))

(defun nth-sieve-state (n) (recur-sieve-state '(1) n))

#+repl (nth-sieve-state 10)


