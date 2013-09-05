;;;
;;;
;;; Represents evaluator for experimenting on the built-in
;;; untyped, call-by-value lambda calculus DSL.
;;;
;;;


(defclass eval-context ()
  ((bindings :initform (make-hash-table) :reader bindings)))

(defun binding (sym context)
  "Helper for accessing the particular symbolic binding from the evaluation context"
  (declare (type symbol sym) (type eval-context context))
  (gethash sym (bindings context)))

(defun apply-0 (lambda-form arg)
  "Lambda calculus application bootstrap function"
  (destructuring-bind (lv-id var body) lambda-form
    (assert (eq lv-id 'lambda) (lambda-form) "Non-lambda form ~S" lambda-form)
    (subst arg var body)))

(defun eval-0 (context form)
  "Top-level lambda calculus evaluation bootstrap function extended with special forms,
provided in the context bindings"
  (let ((result
	 (cond
	   ((symbolp form) (let ((b (binding form context))) (if b b form)))
	   ((consp form) (destructuring-bind (fn-id &rest args) form
			   ;; try eval fn as cons
			   ;; TODO: change it
			   ;;(if (consp fn-id) (setf fn-id (eval-0 context fn-id)))
			   ;; find binding at last
			   (let ((bfn (binding fn-id context)))
			     (cond
			       ;; special form function
			       ((functionp bfn) (apply bfn args))
			       ;; lambda application
			       ((consp bfn)
				(apply #'apply-0 bfn args))
			       ;; form as is
			       ((null bfn) form)
			       ;; unknown form
			       (t (error "Unknown binding for form ~S: ~S" form bfn))))))
	   (t (error "Unknown form ~S" form)))))
    (format t "---: evaluating ~S -> ~S~%" form result)
    result))

(defun bind-std-functions (context)
  (declare (type eval-context context))
  (macrolet ((put-fn-binding (id args &body body)
	       `(setf (gethash ',id (bindings context))
		      (lambda ,args ,@body))))
    ;; PROGN special form
    (put-fn-binding progn (&rest forms)
		    (let (result)
		      (loop for form in forms do (setf result (eval-0 context form)))
		      result))
    ;; LET special form
    (put-fn-binding let (sym val)
		    (check-type sym symbol "Symbol expected")
		    (setf (gethash sym (bindings context)) val))))

#+repl (let ((ec (make-instance 'eval-context)))
	 (bind-std-functions ec)
         (flet ((local-eval (expr)
		  (format t "=============================~%")
		  (format t "eval ~S = ~S~%" expr (eval-0 ec expr))))
           (local-eval 'a)
	   (local-eval '(progn a))
           (local-eval '(progn (let id (lambda s s)) (id u)))
	   (local-eval '(progn
			 (let true (lambda tr (lambda fl tr)))
			 (let false (lambda tr (lambda fl fl)))
			 ;; -- application
			 (false a)
			 (true a)
			 ;;((true a) b) - TODO: make it work!
			 ))
           nil))


