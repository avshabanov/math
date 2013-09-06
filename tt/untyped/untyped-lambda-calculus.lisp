;;;
;;;
;;; Represents evaluator for experimenting on the built-in
;;; untyped, call-by-value lambda calculus DSL.
;;;
;;; This is the extended form of pure Church's lambda calculus, that is
;;; extended with special forms (to allow to define named functions) and
;;; numbers (to make it possible to do folding).
;;; This does not "corrupt" purity of the original lambda calculus, but makes it
;;; "richer" and more compact.
;;;


(defclass eval-context ()
  ((bindings :initform (make-hash-table) :reader bindings)))

(defun binding (sym context)
  "Helper function for accessing the particular symbolic binding from the evaluation context"
  (declare (type symbol sym) (type eval-context context))
  (gethash sym (bindings context)))


(defun eval-0 (context form)
  "Top-level lambda calculus evaluation function extended with special forms,
provided in the context bindings"
  (format t ";;  # evaluating ~S~%" form)
  (flet ((eval-lambda-form (lambda-form &rest args)
           (assert (= 1 (length args)) (form)
                   "Only one argument expected to invoke lambda form ~S" form)
           (destructuring-bind (lambda-sym var body) lambda-form
             (assert (eq lambda-sym 'lambda) (lambda-form)
                     "Unable to evaluate non-lambda form ~S" lambda-form)
             ;; do the necessary substitutions
             (subst (first args) var body))))
    (cond
      ;; numbers and keywords - evaluated AS IS
      ((typep form '(or keyword number)) form)
      ;; symbol form (bound or free variable)
      ((symbolp form) (let ((b (binding form context))) (if b b form)))
      ;; special form or lambda application
      ((consp form) (destructuring-bind (fn-id &rest args) form
                      (cond
                        ;; symbolic leading form
                        ((symbolp fn-id)
                         (let ((bound-form (binding fn-id context)))
                           (cond
                             ;; special form
                             ((functionp bound-form) (apply bound-form args))
                             ;; lambda application, (lambda {var} {body})
                             ((consp bound-form)
                              (eval-lambda-form bound-form args))
                             ;; form as is, evaluation has not been done
                             ((null bound-form) form)
                             (t (error "Unknown binding for function in form ~S" form)))))
                        ;; function ID is itself a function call
                        ((consp fn-id)
                         (if (eq 'lambda (first fn-id))
                             ;; built-in application form
                             (eval-lambda-form fn-id args)
                             ;; nested special form?
                             (let ((fev (eval-0 context fn-id)))
                               (if (equal fn-id fev)
                                   ;; unable to evaluate, result is the same as the source form
                                   form
                                   ;; try evaluate again with the 'expanded' form
                                   ;; TODO: what about divergent combinators?
                                   (eval-0 context (cons fev args))))))
                        ;; unknown function type
                        (t (error "Don't know how to evaluate form ~S" form)))))
      ;; unknown form
      (t (error "Unknown form ~S" form)))))

(defun bind-special-forms (context)
  (declare (type eval-context context))
  (macrolet ((put-fn-binding (id args &body body)
	       `(setf (gethash ',id (bindings context))
		      (lambda ,args ,@body))))
    ;; PROGN special form
    (put-fn-binding progn (&rest forms)
		    (let (result)
		      (loop for form in forms do
                           (setf result (eval-0 context form))
                           (format t ";;    # result -> ~S~%" result))
		      result))
    ;; LET special form
    (put-fn-binding let (sym val)
		    (check-type sym symbol "Symbol expected")
		    (setf (gethash sym (bindings context)) val))))



;;
;; REPL tests

#+repl (defmacro eval-in-context (eval-sym &body body)
         (let ((ec (gensym "eval-context"))
               (expr (gensym "expr")))
           `(let ((,ec (make-instance 'eval-context)))
              (bind-special-forms ,ec)
              (flet ((,eval-sym (,expr)
                       (format t "=============================~%")
                       (format t "eval ~S = ~S~%" ,expr (eval-0 ,ec ,expr))))
                ,@body))))

#+repl (eval-in-context local-eval
         (local-eval 'a))

#+repl (eval-in-context local-eval
         (local-eval '(progn (let id (lambda s s)) (id u))))

#+repl (eval-in-context local-eval
         (local-eval '(((lambda p (lambda q p)) t1) t2)))

#+repl (eval-in-context local-eval
         (local-eval '(progn
			 (let true (lambda tr (lambda fl tr)))
			 (let false (lambda tr (lambda fl fl)))
			 ;; -- application
			 (false a)
			 (true a)
			 ((true a) b)
			 )))
