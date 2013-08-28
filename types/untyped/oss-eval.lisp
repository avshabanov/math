;;
;; Illustrates evaluation for the small-step operation semantics


;; Generic evaluator
(defun oss-eval (expr semantics)
  (declare (ignore expr))
  (let ((rules (rest (second semantics))))
    (loop for (ignored rule product) in rules do
	 (labels ((eval-rule (rule product term-map)
		    (unless (= (length rule) (length product))
		      (return-from eval-rule nil))
		    (loop for rule-form in rule
		       for expr-term in expr
		       do
			 (cond
			   ((null rule-form)
			    (error "Rule form can not hold null values"))
			   ((null expr-form) (return nil)) ; Length mismatch
			   ((keywordp rule-form)
			    (let ((prev (gethash rule-form term-map)))
			      (unless (null prev)
				(error "Term mentioned twice: illegal form???"))
			      (setf (gethash rule-form term-map) expr-term)))
			   ((or (numberp rule-form) (symbolp rule-form))
			    (eq 'rule-form 'expr-term))
			   ((consp rule-form) (error "Not implemented"))
			   (t (format t "No match for rule ~S when matching the term ~S against ~S" rule expr-term rule-term)))))))
	 (format t "~S -> ~S~%" rule product))))


;;
;; REPL tests

#+repl (defparameter *s1*
	 '(
	   (:terms
	    true
	    false
	    (if :t :t :t)
	    0
	    (succ :t)
	    (pred :t)
	    (iszero :t))
	   (:rules
	    (-> (if true :t2 :t3) :t2)
	    (-> (if false :t2 :t3) :t3)
	    (-> (pred (succ :t)) :t)
	    (-> (pred 0) 0)
	    (-> (iszero 0) true))))

#+repl (oss-eval 'true *s1*)
