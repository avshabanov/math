

#+repl (load "untyped-lambda-calculus.lisp")

(eval-in-context local-eval
  (local-eval '(progn
                ;; Church booleans
                (let true (lambda tr (lambda fl tr)))
                (let false (lambda tr (lambda fl fl)))
                (let test (lambda l (lambda m (lambda n ((l m) n)))))
                (let and (lambda b (lambda c ((b c) false))))

                ;; true a b
                (trace ((true a) b))

                ;; test true u v
                (trace (((test true) u) v))

                ;; and true false
                (trace ((and true) false))

                ;; and true true
                (trace ((and true) true))

                ;; test false u v
                (trace (((test false) u) v)))))


(eval-in-context local-eval
  (local-eval '(progn
                ;; Church numerals
                (let c0 (lambda s (lambda z z)))
		(let c1 (lambda s (lambda z (s z))))
		(let c2 (lambda s (lambda z (s (s z)))))
		(let c3 (lambda s (lambda z (s (s (s z))))))
		(let c4 (lambda s (lambda z (s (s (s (s z)))))))
		(let c5 (lambda s (lambda z (s (s (s (s (s z))))))))
		(let c6 (lambda s (lambda z (s (s (s (s (s (s z)))))))))
		(let c7 (lambda s (lambda z (s (s (s (s (s (s (s z))))))))))

		;; Church booleans
		(let true (lambda tr (lambda fl tr)))
                (let false (lambda tr (lambda fl fl)))

		;; Church pairs
		(let pair (lambda f (lambda s (lambda b ((b f) s)))))
		(let fst (lambda p (p true)))
		(let snd (lambda p (p false)))
		
		(let scc (lambda n (lambda s (lambda z (s ((n s) z))))))
		(let plus (lambda m (lambda n
				      (lambda s
					(lambda z
					  ((m s) ((n s) z)))))))
		(let times (lambda m (lambda n ((m (plus n)) c0))))
		;; times2 is the alternative representation of times
		(let times2 (lambda m
			      (lambda n
				((m
				  (n
				   (lambda k
				     (lambda s
				       (lambda z (s ((k s) z)))))) c0)))))
		;; m^n
		(let pow (lambda m (lambda n ((n (times m)) c1))))
		;; m-n
		(let ss (lambda p ((pair (snd p)) (scc (snd p)))))
		(let prd (lambda m (fst ((m ss) ((pair c0) c0)))))
		(let sub (lambda m (lambda n ((n prd) m))))

                ;; is zero?
                (let iszro (lambda m ((m (lambda x fls)) tru)))

		(trace (((scc c3) 's) 'z))
		(trace ((((plus c2) c3) 's) 'z))
		
		(trace ((((times c5) c2) 's) 'z))
		(trace ((((times c2) c3) 's) 'z))

		(trace ((((pow c3) c2) 's) 'z))
		(trace ((((pow c2) c3) 's) 'z))
		(trace-and-reset-evals)

		(trace (((prd c2) 's) 'z)) (trace-and-reset-evals)
		(trace (((prd c3) 's) 'z)) (trace-and-reset-evals)
		(trace (((prd c4) 's) 'z)) (trace-and-reset-evals)
		(trace (((prd c5) 's) 'z)) (trace-and-reset-evals)
		
		(trace ((((sub c7) c3) 's) 'z)) (trace-and-reset-evals)
		)))

(eval-in-context local-eval
  (local-eval '(progn
                ;; Church lists
                (let nil (lambda c (lambda n n)))
                ;; h - list element, t - existing list
                ;; church list [x, y, z] ==> (c x (c y (c z n))), c - fold function, n - initial arg
                (let cons (lambda h (lambda t (lambda c (lambda n ((c h) ((t c) n)))))))

                (trace ((nil 'c) 'n))
                (trace ((((cons 1) ((cons 2) ((cons 3) nil))) 'c) 'n))
                )))

#|

;; # (((SCC C3) 'S) 'Z) -> ('S ('S ('S ('S 'Z))))
;; # ((((PLUS C2) C3) 'S) 'Z) -> ('S ('S ('S ('S ('S 'Z)))))
;; # ((((TIMES C5) C2) 'S) 'Z) -> ('S
                                   ('S
                                    ('S
                                     ('S
                                      ('S ('S ('S ('S ('S ('S 'Z))))))))))
;; # ((((TIMES C2) C3) 'S) 'Z) -> ('S ('S ('S ('S ('S ('S 'Z))))))
;; # ((((POW C3) C2) 'S) 'Z) -> ('S
                                 ('S
                                  ('S ('S ('S ('S ('S ('S ('S 'Z)))))))))
;; # ((((POW C2) C3) 'S) 'Z) -> ('S ('S ('S ('S ('S ('S ('S ('S 'Z))))))))

|#