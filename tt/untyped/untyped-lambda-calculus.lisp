;;
;; Represents evaluator for experimenting on the built-in lambda calculus DSL

(defclass eval-context ()
  ((bindings :initform (make-hash-table) :reader bindings)))

(defun binding (sym context)
  (declare (type symbol sym) (type eval-context context))
  (gethash sym (bindings context)))

(defun eval-0 (context form)
  "Evaluation bootstrap function"
  (format t "---> evaluating ~S~%" form)
  (cond
    ((symbolp form) (let ((b (binding form context))) (if b b form)))
    ((consp form) (destructuring-bind (fn-id &rest args) form
		    (let ((bfn (binding fn-id context)))
		      (apply bfn args))))
    (t (error "Unknown form ~S" form))))

(defun bind-std-functions (context)
  (declare (type eval-context context))
  (macrolet ((put-fn-binding (id args &body body)
	       `(setf (gethash ',id (bindings context))
		      (lambda ,args ,@body))))
    (put-fn-binding progn (&rest forms)
		    (format t " #-> forms = ~S~%" forms)
		    (let (result)
		      (loop for form in forms do (setf result (eval-0 context form)))
		      result))
    (put-fn-binding let (sym val)
		    (check-type sym symbol "Symbol expected")
		    (setf (gethash sym (bindings context))
			  (cond
			    ((consp val)
			     (destructuring-bind (lv-id var body) val
			       (assert (eq lv-id 'lambda) (val) "Unknown form ~S" val)
			       (lambda (x)
				 (subst x var body))))
			    (t val))))))

#+repl (let ((ec (make-instance 'eval-context)))
	 (bind-std-functions ec)
         (flet ((ev (expr)
		  (format t "=============================~%")
		  (format t "eval ~S = ~S~%" expr (eval-0 ec expr))))
           (ev 'a)
	   (ev '(progn a))
           (ev '(progn (let id (lambda s s)) (id u)))
           nil))


