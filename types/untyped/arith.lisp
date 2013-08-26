;;
;; An attempt to specify operational semantics for untyped arithmetics in
;; a short and concise lisp DSL form.


(defmacro def-semantics (name terms evaluation-relation)
  ;; TODO: analyze
  `(defparameter ,name (list ',terms ',evaluation-relation)))

;;
;; Sample

(def-semantics booleans ((:terms
			     true
			     false
			     (if :term then :term else :term))
			    (:values
			     true
			     false)) ; <- Syntax
  ;; Evaluation (see chapter 3.5, Fig. 3.1)
  ((:E-IfTrue
    ;; if true then t2 else t3   ->   t2
    (if true then :t2 else :t3 -> :t2))
   (:E-IfFalse
    (if false then :t2 else :t3 -> :t3))
   (:E-If
    ;;                     t1   ->   t1'
    ;; -----------------------------------------------------
    ;;  if t1 then t2 else t3   ->   if t1' then t2 else t3
    (/ (:t1 -> :t1-q1)
       ((if :t1 then :t2 else :t3) -> (if :t1-q1 then :t2 else :t3))))))

;; alt
(defparameter alt-boolean-semantics
  '(
    (:terms true false (if :term :term :term))
    (:evaluation
     ;; Structure:
     ;; (rule <NAME> <PREMISE> / <LHS> -> <RHS>)
     (rule :if-true nil
      (if true :t2 :t3) :t2)
     (rule :if-false nil
      (if false :t2 :t3) :t3)
     (rule :if (-> :t1 :t1-2)
      (if :t1 :t2 :t3) (if :t1-2 :t2 :t3)))))

(defun evaluate-rule (rule semantics)
  t)

#+repl (check-rule-instance 'alt-boolean-semantics
			    (if (if true false true) (if false false true) true))
