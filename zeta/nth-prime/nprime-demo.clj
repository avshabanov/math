
;; Debug variables for tracing lambda calc execution
(def ^:dynamic *stat-call* (atom 0))
(def stat-enabled false) ; debug will be turned off if false (and thus *won't affect exection*)


;;
;; Helpers
;;

(defmacro %
  "Helper macro for defining lambda functions (each function always takes exactly one argument).
  (% x {body}) is a rough equivalent of (fn x {callable-form}).
  This macro also transforms lambda function body into the callable form, so that the sequence of terms is
  transformed into the list of function calls so that each function is called with exactly one argument, e.g.:
  a b c d -> (((a b) c) d)
  See also lc macro for seeing how body tranformation works."
  [var-name & body]
  (let [unfold-body (condp = (count body)
                      0 (assert false "Unable to unfold body of no elements")
                      1 (first body)
                      2 body
                      (reduce
                        (fn [c e] (list c e))
                        (take 2 body)
                        (nthrest body 2)))]
    `(fn [~var-name]
       ~(if stat-enabled `(do (swap! *stat-call* inc) ~unfold-body) unfold-body))))

;; (macroexpand-1 '(% x x d))

(defmacro lc
  "Helper Macro for calling lambda calculus functions.
  Transforms a given list to the list of nested calls,
  so that each function in this list is called only once.
  Does not work recursively.
  E.g.:
    (lc a b c d) -> (((a b) c) d)
    (lc a (b c) d) -> ((a (b c)) d)
  "
  [& body]
  (reduce
    (fn [c e] (list c e))
    (take 2 body)
    (nthrest body 2)))

;;
;; Lambda Calculus Entities
;;

;;
;; Church numerals and arithmetic operations
;;

;; base church numerals: zero and successor function
(def zero (% s (% z z))) ; <=> (def zero (fn [s] (fn [z] z)))
(def succ (% n (% s (% z s ((n s) z)))))

;; convenience definition of the church number one
(def one (succ zero))

;; infinite sequence of Church numerals
(def N (iterate succ zero))
;; Illustration: (map (fn [x] (lc x inc 0)) (take 5 N))


;;
;; Next Prime Calc
;;

(defn pdna-prime? [pdna]
  (reduce (fn [elem [x y]] (and elem (not (= y 0)))) true pdna))

(assert (pdna-prime? []))
(assert (pdna-prime? [[1 2]]))
(assert (pdna-prime? [[1 1] [0 2] [3 4]]))
(assert (not (pdna-prime? [[1 0]])))
(assert (not (pdna-prime? [[1 1] [4 2] [3 0]])))
(assert (not (pdna-prime? [[1 1] [4 0] [3 2]])))
(assert (not (pdna-prime? [[1 0] [4 5] [3 2]])))

(defn inc-pdna [pdna]
  (map
    (fn [[prime residue]]
      [prime (let [r (inc residue)]
               (if (= r prime) 0 r))])
    pdna))

(defn next-pdna [number expected-index prime-index pdna]
  (if (pdna-prime? pdna)
    (do
      (if (= expected-index prime-index)
        pdna
        (next-pdna (inc number) expected-index (inc prime-index) (cons [number 1] (inc-pdna pdna)))))
    (next-pdna (inc number) expected-index prime-index (inc-pdna pdna))))

(assert (= [] (next-pdna 2 0 0 [])))
(assert (= [[2 1]] (next-pdna 2 1 0 [])))
(assert (= [[3 2] [2 1]] (next-pdna 2 2 0 [])))
(assert (= [[11 2] [7 6] [5 3] [3 1] [2 1]] (next-pdna 2 5 0 [])))
;; 101-th prime number == 547
(assert (= 547 (let [[x y] (first (next-pdna 2 100 0 []))] (+ x y))))

;; (dotimes [i 100] (println "pi(" i ") =" (next-pdna 2 i 0 [])))

;;
;; Tests
;;

;; calls lambda expression and uses 'inc' (+1) as a sequence function
;; and 0 (zero) as zero function
(defmacro numcall [& body]
  (let [extbody (concat body '(inc 0))]
    `(lc ~@extbody)))


(dotimes [i 9]
  (assert (= i (numcall (nth N i)))))

;; (map (fn [[prime residue]] residue) [[1 2] [3 4]])
