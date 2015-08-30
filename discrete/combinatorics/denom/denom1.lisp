;;
;; Illustrates the solution of problem of representing certain integer sum with
;; the money of given denominations.
;;
;; In this particular problem we are given with the finite set of coins of different
;; denomination and we must find all the possible solution to represent certain sum with that
;; coins. Coins of same denominations but different positions should be treated as different ones,
;; thus the same sum with same sequence from the denominations point of view may be represented in
;; certain situations by different coins what counts as different possible solution.

(defun represent-sum (sum coins)
  (declare (type integer sum))
  (cond
    ((typep coins 'array) nil)
    ((typep coins 'list) (setf coins (make-array (length coins) :initial-contents coins)))
    (t (error "Unsupported coins type, given coins=~S" coins)))
  (let (result
        (seq (make-array (length coins)))
        (last-index (- (length coins) 1))
        (seq-pos 0))
    (labels ((search-step (cur-sum coins-pos)
               #+repl (format t "cur-sum = ~S~%" cur-sum)
               (cond
                 ((= cur-sum sum)
                  (setf result (nconc result (list (loop for i from 0 to (- seq-pos 1) collect (aref seq i))))))
                 ((<= cur-sum sum)
                  (loop for i from coins-pos to last-index do
                       (let ((coin-val (aref coins i)))
                         (setf (aref seq seq-pos) (cons coin-val i))
                         (incf seq-pos)
                         (search-step (+ cur-sum coin-val) (1+ i))
                         (decf seq-pos)))))))
      (search-step 0 0))
    result))

#+repl (represent-sum 10 '(5 5 2 4 1 4))

#+repl (let* ((coins '(5 5 2 4 1 4))
              (sum 10)
              (result (represent-sum sum coins)))
         (loop for sums in result do
              (format t "~S = " sum)
              (loop
                 for (coin-val . coin-pos) in sums
                 for i from 0
                 do
                   (progn
                     (if (> i 0) (format t " + "))
                     (format t "~S (coin #~S)" coin-val coin-pos)))
              (format t ";~%")))
