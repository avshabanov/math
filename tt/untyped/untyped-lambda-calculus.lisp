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
  ((bindings :initform (make-hash-table) :reader bindings)
   ;; number of evaluations, for statistics purposes
   (num-evals :initform 0 :accessor num-evals)))


(defun eval-0 (context form)
  "Top-level lambda calculus evaluation function extended with special forms"
  #+repl (format t ";;  # evaluating ~S~%" form)
  (incf (num-evals context))
  (flet ((binding (sym context)
           "Helper function for accessing the particular symbolic binding from the evaluation context"
           (declare (type symbol sym) (type eval-context context))
           (gethash sym (bindings context)))
         (eval-lambda-form (lambda-form args)
           (assert (= 1 (length args)) (form)
                   "Only one argument expected to invoke lambda form ~S" form)
           (destructuring-bind (lambda-sym var body) lambda-form
             (assert (eq lambda-sym 'lambda) (lambda-form)
                     "Unable to evaluate non-lambda form ~S" lambda-form)
             ;; do the necessary substitutions
             (let ((result (subst (first args) var body)))
               (eval-0 context result)))))
    (cond
      ;; numbers and keywords - evaluated AS IS
      ((typep form '(or keyword number)) form)
      ;; symbol form (bound or free variable)
      ((symbolp form) (let ((b (binding form context))) (if b b form)))
      ;; special form or lambda application
      ((consp form) (destructuring-bind (fn-id &rest args) form
                      (cond
                        ((symbolp fn-id) ; symbolic leading form
                         (let ((bound-form (binding fn-id context)))
                           (cond
                             ;; special form
                             ((functionp bound-form) (apply bound-form args))
                             ;; lambda application, (lambda {var} {body})
                             ((consp bound-form) (eval-lambda-form bound-form args))
                             ;; form as is, evaluation has not been done
                             ((null bound-form) form)
                             (t (error "Unknown binding for function in form ~S" form)))))
                        ((consp fn-id)  ; function ID is itself a function call
                         (if (eq 'lambda (first fn-id))
                             ;; built-in application form
                             (eval-lambda-form fn-id args)
                             ;; nested special form?
                             (let ((fev (eval-0 context fn-id)))
                               (if (equal fn-id fev)
                                   ;; unable to evaluate, result is the same as the source form
                                   (cons fn-id (loop for a in args collect
						    (eval-0 context a)))
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
                           #+repl (format t ";;  ### result -> ~S~%" result))
		      result))
    ;; LET special form
    (put-fn-binding let (sym val)
		    (check-type sym symbol "Symbol expected")
		    (setf (gethash sym (bindings context)) val))
    ;; TRACE special form
    (put-fn-binding trace (form)
                    (format t ";; # ~S -> ~S~%" form (eval-0 context form)))
    ;; TRACE-AND-RESET-EVALS special form
    (put-fn-binding trace-and-reset-evals ()
		    (format t ";; [STAT] num-evals = ~S~%" (num-evals context))
		    (setf (num-evals context) 0))))



;;
;; REPL tests

;; convenient evaluation for tests
(defmacro eval-in-context (eval-sym &body body)
  (let ((ec (gensym "eval-context"))
        (expr (gensym "expr")))
    `(let ((,ec (make-instance 'eval-context)))
       (bind-special-forms ,ec)
       (flet ((,eval-sym (,expr)
                (format t "=============================~%") ; for trace
                #-repl (eval-0 ,ec ,expr)
                #+repl (format t "eval ~S = ~S~%" ,expr (eval-0 ,ec ,expr))))
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
