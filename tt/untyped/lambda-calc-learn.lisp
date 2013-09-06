

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



