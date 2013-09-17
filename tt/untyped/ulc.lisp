;;
;; Another implementation of the lambda calculus evaluator extended with special forms
;;
;; This extension allow multiple arguments to be passed to the function
;;

(defclass eval-context ()
  ((bindings :initform (make-hash-table) :reader bindings)
   (toplev-eval-fn :initform (error "No toplevel evaluation function")
                   :initarg :toplev-eval-fn
                   :reader toplev-eval-fn)))

;; Toplevel evaluation function
(defun toplev-eval (form context)
  (declare (type eval-context context))
  (funcall (toplev-eval-fn context) form context))


;; evaluates form in the given context, inner function that should be root of all the evaluations
;; this is the very primitive version of the evaluation function
(defun eval-0 (form context)
  (declare (type eval-context context))
  #+repl (format t ";; eval-0 ~S~%" form)
  (cond
    ;; numbers, keywords and strings - evaluate AS IS
    ((typep form '(or string keyword number)) form)
    ;; symbol form - we should get here only if symbol really needs evaluation
    ((symbolp form) (let ((bound-form (gethash form (bindings context))))
                      (if bound-form bound-form (error "Unbound symbol ~S" form))))
    ;; cons: special form or lambda application
    ((consp form) (destructuring-bind (id &rest args) form
                    (let ((evaluated-id (toplev-eval id context)))
                      (cond
                        ;; function - eval as is (product of special form evaluation)
                        ((functionp evaluated-id) (apply evaluated-id context args))
                        ;; cons - eval again from the top level
                        ((consp evaluated-id)
                         (toplev-eval (cons evaluated-id args) context))
                        ;; unknown form
                        (t (error "Unknown function id in ~S" form))))))
    ;; unknown form
    (t (error "Unknown form ~S" form))))


(defun bind-special-form (context form-id handler)
  (declare (type eval-context context))
  (let ((prev-handler (gethash form-id (bindings context))))
    (if prev-handler (error "Duplicate binding for ~S form" form-id))
    (setf (gethash form-id (bindings context)) handler)))

;;
;; Standard special forms
;;

;; special form progn
(defun %progn (context &rest forms)
  (let (result)
    (loop for form in forms do
         (setf result (toplev-eval form context)))
    result))

(defun %let (context sym value)
  (check-type sym symbol "Symbol expected")
  (setf (gethash sym (bindings context)) value))

(defun %trace (context form)
  (format t ";; # ~S -> ~S~%" form (toplev-eval form context)))

(defun %lambda (context arg-name body)
  (declare (ignore context))
  (lambda (context a1)
    (declare (ignore context))
    (subst a1 arg-name body)))

(defun %eval (context form)
  (let ((result (toplev-eval form context)))
    (cond
      ((functionp result) form)
      ((consp result) (if (equal result form) form (toplev-eval result context)))
      (t result))))

;; same as LAMBDA special form, but allows multiple arguments
(defun %lambda* (context arg-names body)
  (declare (ignore context))
  (let (last-form lambda-form)
    (loop for arg in arg-names do
         (if last-form
             (let ((f `(lambda ,arg)))
               (nconc last-form (list f))
               (setf last-form f))
             (setf lambda-form (setf last-form `(lambda ,arg)))))
    (nconc last-form (list body))
    (lambda (context &rest args)
      (let ((invocation-form lambda-form))
        (loop for arg in args do
             (setf invocation-form (list invocation-form arg)))
        #+repl (format t ";; * (LAMBDA* ~S ~S) . ~S => ~S~%"
		       arg-names body args invocation-form)
        (toplev-eval invocation-form context)))))

(defun add-standard-special-forms (context)
  (bind-special-form context 'progn #'%progn)
  (bind-special-form context 'let #'%let)
  (bind-special-form context 'trace #'%trace)
  (bind-special-form context 'eval #'%eval)
  (bind-special-form context 'lambda #'%lambda)
  (bind-special-form context 'lambda* #'%lambda*))

;;
;; REPL tests

(defmacro eval-in-context (context-sym eval-sym toplev-eval-fn &body body)
  (let ((form (gensym "form")))
    `(let ((,context-sym (make-instance 'eval-context
					:toplev-eval-fn (if (null ,toplev-eval-fn)
							    #'eval-0
							    ,toplev-eval-fn))))
       (add-standard-special-forms ,context-sym)
       (flet ((,eval-sym (,form) (toplev-eval ,form ,context-sym)))
         ,@body))))

#+repl (eval-in-context
           ec ev nil
         (format t "==============~%")
         (ev '(progn (trace 1))))

#+repl (eval-in-context
           ec ev nil
         (format t "==============~%")
         (ev '(progn
               (let id (lambda x x))
               (trace (id 1)))))

#+repl (eval-in-context
           ec ev nil
         (format t "==============~%")
         (ev '(progn
               (let tr (lambda tr (lambda fl tr)))
               (trace ((tr 1) 2)))))

#+repl (eval-in-context
           ec ev nil
         (format t "==============~%")
         (ev '(progn
               (let true (lambda* (tr fl) tr))
               (let false (lambda* (tr fl) fl))
               (let and (lambda* (b c) ((b c) false)))
               (trace (eval (and true false))))))

#+repl (eval-in-context
           ec ev nil
         (format t "==============~%")
         (ev '(progn
               (let true (lambda tr (lambda fl tr)))
               (let false (lambda tr (lambda fl fl)))
               (let and (lambda b (lambda c ((b c) false))))
               (trace (eval ((and true) false))))))

#+repl (eval-in-context
	   ec ev nil
	 (format t "==============~%")
	 (bind-special-form ec 'spy (lambda (ctx v) (declare (ignore ctx v))))
	 (ev
	  '(progn
	    ;; Church lists
	    (let nil (lambda c (lambda n n)))
	    ;; h - list element, t - existing list
	    ;; church list [x, y, z] ==> (c x (c y (c z n))), c - fold function, n - initial arg
	    (let cons (lambda h (lambda t (lambda c (lambda n ((c h) ((t c) n)))))))

	    (trace ((nil 'c) 'n))
	    (trace ((((cons 1) ((cons 2) ((cons 3) nil))) cons.) 0))
	    )))