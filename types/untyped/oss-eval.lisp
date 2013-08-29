;;
;; Illustrates evaluation for the small-step operation semantics

(defclass grammar ()
  ((value-map :initform (make-hash-table) :reader value-map)
   (rule-map :initform (make-hash-table) :reader rule-map)))

;; Main grammar creation function
(defun make-grammar (&key values rules)
  (let* ((g (make-instance 'grammar))
	 (vmap (value-map g))
	 (rmap (rule-map g)))
    ;; init value mapping
    (loop for v in values do
	 (check-type v (or number symbol))
	 (unless (null (gethash v vmap)) (error "Duplicate value ~S" v))
	 (setf (gethash v vmap) v))
    ;; init rules mapping
    (loop for rule in rules do
	 (check-type rule cons)
	 (destructuring-bind (rfn pattern product) rule
	   (cond
	     ((eq '-> rfn)
	      (check-type pattern cons)
	      (check-type product keyword))
	     (t (error "Unrecognized rule ~S" rule)))))
    g))

#+repl (defparameter *g-a-1* (make-grammar
			      :values '(true false)
			      :rules '((-> (if true :then :else) :then)
				       (-> (if false :then :else) :else))))


;; Generic evaluator
(defun toplev-eval (expr g)
  (check-type g grammar)
  (cond
    ((keywordp expr) (error "Keyword values forbidden, got ~S" expr))
    ((or (numberp expr) (symbolp expr))
     (let ((v (gethash expr (value-map g))))
       (if v v (error "Non-value expression ~S that pretend to be a value" expr))))
    ((consp expr)
     (destructuring-bind (fn-id &rest args) expr
       (error "TODO: impl")))
    (t (error "Invalid expression ~S" expr))))


;;
;; REPL

#+repl (let ((g (make-grammar :values '(true false)
			      :rules '((-> (if true :then :else) :then)
				       (-> (if false :then :else) :else)))))
	 (values
	  (toplev-eval 'true g)))