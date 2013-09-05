;;
;; Represents evaluator for experimenting on the built-in lambda calculus DSL

(defclass eval-context ()
  ((bindings :initform (make-hash-table) :reader bindings)))

;; TODO
(defun bind-std-functions ())

;; untyped lambda calculus or lisp-in-lisp

(defun eval-expr (context expr)
  (declare (type eval-context context))
  (cond
    ((typep expr 'symbol) (let ((binding (gethash expr (bindings context))))
                            (if binding binding expr)))
    ;; TODO: cons
    (t (error "Unknown expression type ~S" expr))))

#+repl (let ((ec (make-instance 'eval-context)))
         (flet ((ev (expr) (format t "eval(~S) = ~S~%" expr (eval-expr ec expr))))
           (ev 'a)
           #+test (ev '(progn (let id (lambda s s)) (id u)))
           nil))

