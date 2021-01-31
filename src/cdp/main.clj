(ns cdp.main
  (:require [clojure.set :as set]
            [cdp.evolution :as evo]
            [cdp.random :as random]
            [clojure-csv.core :as csv]
            [clojure.java.io :as io]))

; helper functions

(defn safe-divide [a b]
  (if (zero? b)
    0
    (/ a b)))

(defn safe-mod [a b]
  (if (zero? b)
    0
    (mod a b)))

; Define the environment.

(def env
  (let [arithmetic-op (fn [op] (fn [f1 f2]
                                 (fn [l]
                                   (map op
                                        (f1 l)
                                        (f2 l)))))]
    {'+ (arithmetic-op +')
     '- (arithmetic-op -')
     '* (arithmetic-op *')
     '/ (arithmetic-op safe-divide)
     'mod (arithmetic-op safe-mod)
     '= (fn [f1 f2]
          (fn [l]
            (map #(if (= %1 %2) 1 0)
                 (f1 l)
                 (f2 l))))
     '> (fn [f1 f2]
          (fn [l]
            (map #(if (> %1 %2) 1 0)
                 (f1 l)
                 (f2 l))))
     'and (fn [f1 f2]
           (fn [l]
             (map #(if (and (not (== 0 %1)) (not (== 0 %2))) 1 0)
                  (f1 l)
                  (f2 l))))
     'or (fn [f1 f2]
           (fn [l]
             (map #(if (or (not (== 0 %1)) (not (== 0 %2))) 1 0)
                  (f1 l)
                  (f2 l))))
     'reduce-and (fn [f]
            (fn [l]
              (list (if (reduce #(and %1 (not= 0 %2))
                                true
                                (f l))
                      1
                      0))))
     'reduce-or (fn [f]
           (fn [l]
             (list (if (reduce #(or %1 (not= 0 %2))
                               true
                               (f l))
                     1
                     0))))
     'not (fn [f]
            (fn [l]
              (map #(if (= % 0) 1 0)
                   (f l))))
     'if (fn [cond f1 f2]
           (fn [l]
             (let [cond-value (cond l)]
               (if (and (not (empty? cond-value))
                        (not= (first cond-value) 0))
                 (f1 l)
                 (f2 l)))))
     'each-if (fn [cond f1 f2]
                (fn [l]
                  (map #(if (not= %1 0) %2 %3)
                       (cond l)
                       (f1 l)
                       (f2 l))))
     'floor (fn [f]
              (fn [l]
                (map #(long (Math/floor %))
                     (f l))))
     'ceil (fn [f]
             (fn [l]
               (map #(long (Math/floor %))
                    (f l))))
     'identity (fn []
                 (fn [l]
                   l))
     'rest (fn [f]
             (fn [l]
               (rest (f l))))
     'butlast (fn [f]
                (fn [l]
                  (or (butlast (f l)) '())))
     'first (fn [f]
              (fn [l]
                (take 1 (f l))))
     'last (fn [f]
             (fn [l]
               (take 1 (reverse (f l)))))
     'reverse (fn [f]
                (fn [l]
                  (reverse (f l))))
     'concat (fn [f1 f2]
               (fn [l]
                 (concat (f1 l) (f2 l))))
     'constant (fn [c]
                 (fn [l] c))}))

; Define the distribution.

(defn dist []
  (apply
   random/weighted-choice
   (map vector
        [3 (list '+ :SUBTREE :SUBTREE)]
        [3 (list '- :SUBTREE :SUBTREE)]
        [3 (list '* :SUBTREE :SUBTREE)]
        [3 (list '/ :SUBTREE :SUBTREE)]
        [3 (list 'mod :SUBTREE :SUBTREE)]
        [2 (list '= :SUBTREE :SUBTREE)]
        [2 (list '> :SUBTREE :SUBTREE)]
        [1 (list 'and :SUBTREE :SUBTREE)]
        [1 (list 'or :SUBTREE :SUBTREE)]
        [1 (list 'reduce-and :SUBTREE)]
        [1 (list 'reduce-or :SUBTREE)]
        [2 (list 'not :SUBTREE)]
        [15 (list 'if :SUBTREE :SUBTREE :SUBTREE)]
        [2 (list 'each-if :SUBTREE :SUBTREE :SUBTREE)]
        [1 (list 'floor :SUBTREE)]
        [1 (list 'ceil :SUBTREE)]
        [10 (list 'identity)]
        [2 (list 'rest :SUBTREE)]
        [2 (list 'butlast :SUBTREE)]
        [2 (list 'first :SUBTREE)]
        [2 (list 'last :SUBTREE)]
        [3 (list 'reverse :SUBTREE)]
        [2 (list 'concat :SUBTREE :SUBTREE)]
        [8 (list 'constant (rand-nth '((0) (1) (2))))]
        [8 (list 'constant (map (if (> (rand) 0.5)
                                  (fn [x]
                                    (* 2 (random/double-sided-rand-exp)))
                                  (fn [x]
                                    (random/double-sided-rand-geom 0.6)))
                                (range (inc (random/rand-geom 0.7)))))])))

; Read the data file describing the value/label pairs for the iris problem.

(def raw-data
  (apply interleave
         (partition 50
                    (butlast (with-open [file (io/reader (io/resource "data/iris.data"))]
                               (csv/parse-csv (slurp file)))))))

; Compute the list of data values in the data set.

(def data-values (mapv (fn [row]
                         (map read-string
                              (butlast row)))
                       raw-data))

; Compute the list of data labels in the data set.

(def data-labels (mapv (fn [row]
                         ({"Iris-setosa" 0
                           "Iris-versicolor" 1
                           "Iris-virginica" 2}
                          (last row)))
                       raw-data))

(defn goal-counter
  "A goal counter for the iris problem. Returns a list of up to 150 sets
   containing statement/label pairs which properly classify some data value."
  [statements labels]
  (let [pairs (map vector statements labels)]
    (into {}
          (filter #(not (empty? (second %)))
                  (map (fn [index data-label]
                         [index
                          (into #{} (filter (fn [[statement label]]
                                              (and (= (count statement) 1)
                                                   (== index (:index label))
                                                   (== (first statement) data-label)))
                                            pairs))])
                       (range)
                       data-labels)))))

(defn conflict-counter
  "A goal counter for the iris problem. Returns a list of up to 150 sets
   containing statement/label pairs which properly classify some data value."
  [statements labels]
  (let [pairs (map vector statements labels)]
    (into {}
          (filter #(not (empty? (second %)))
                  (map (fn [index data-label]
                         [index
                          (into #{} (filter (fn [[statement label]]
                                              (and (= (count statement) 1)
                                                   (== index (:index label))
                                                   (#{0 1 2 0.0 1.0 2.0} (first statement))
                                                   (not (== (first statement) data-label))))
                                            pairs))])
                       (range)
                       data-labels)))))

(defn conflict-predicate
  "Conflict predicate for the iris problem. Returns true when a statement/label
   pair properly classifies some data value."
  [statement label]
  (and (= (count statement) 1)
       (#{0 1 2 0.0 1.0 2.0} (first statement))
       (not (== (first statement) (nth data-labels (:index label))))))

(defn evaluate
  "A function that is executed after each evolutionary step. Computes and
   prints the current 'score' of the state, where the 'score' is defined
   as the number of data values such that there is at least one
   statement/label pair that correctly classifies it, and no statement/label
   pairs that incorrectly classify it."
  [execution-state]
  (let [statements (:statements execution-state)
        labels (:labels execution-state)
        result (filter (fn [index]
                         (let [data-label (nth data-labels index)
                               matches (filter (fn [[statement label]]
                                                 (and (= (count statement) 1)
                                                      (#{0 1 2 0.0 1.0 2.0} (first statement))
                                                      (= index (:index label))))
                                               (map vector
                                                    statements
                                                    labels))
                               matches-correct? (map (fn [[statement label]]
                                                       (== (first statement) data-label))
                                                     matches)]
                           (reduce #(and %1 %2)
                                   (not (empty? matches))
                                   matches-correct?)))
                       (range (count data-labels)))
        result-count (count result)]
    (println (str "Score: " result-count))))

(defn label-predicate
  "Label predicate for the iris problem. Returns true if and only if the 'life'
   a label is greater than 0."
  [label]
  (> (:life label)
     0))

(defn label-generator
  "Label generator for the iris problem. Returns a label with the same index
   as the input, but 1 less 'life'."
  [label]
  (assoc label
         :life (dec (:life label))))

(defn invariant-statements
  "Returns a set of invariant statements for the iris problem. When no argument
   is provided returns a list of 150 statements, each of which is a list of 4
   numbers describing the attributes of an iris flower. When a number is
   provided for the `num` an argument, will return `num` statements rather than
   all 150."
  [& [num]]
  (let [num (or num (count data-values))]
    (vec (take num data-values))))

(defn invariant-labels
  "Returns a set of invariant labels for the Iris problem. When no argument is
   provided returns a list of 150 labels, but when a number `num` is provided
   as an argument it will return `num` labels rather than 150. Each label
   consists of a map with two values: :life and :index. :index describes which
   in the dataset this statement/label pair refers to, and is inherited to all
   statements derived from this one. :life is used to limit the number of
   deductive steps that can be taken from this statement/label pair. Whenever
   a new statement/label pair is derived from this one it will have 1 less
   'life', and a statement/label pair with 0 'life' cannot be used to derive
   any further statement/label pairs." 
  [& [num]]
  (mapv (fn [index]
          {:life 3 :index index})
        (range (or num (count data-values)))))

(defn iris-evolve
  "Attempts to evolve a set of rules over for solving the iris problem.
   Evolution takes place of `steps` steps. If `data-points` is specified,
   this process will attempt to classify only the first `data-points` data
   values, rather than all 150. `statement-cap` and `label-cap` can be used
   to place an upper limit on the number of statements and labels,
   respectively, that the evolutionary process will keep after each step.
   Setting these caps can help the evolutionary process run faster by preveting
   it from accumulating too many unnecessary rules."
  [steps & [data-points rule-cap statement-cap output-interval]]
  (let [result (evo/evolve (invariant-statements data-points)
                           (invariant-labels data-points)
                           env
                           dist
                           label-predicate
                           label-generator
                           goal-counter
                           conflict-counter
                           steps
                           (or rule-cap ##Inf)
                           (or statement-cap ##Inf)
                           3
                           0.25
                           0.5
                           evaluate
                           (or output-interval 25))]
    (println (str "\nFinal evaluation:"))
    (evaluate result)))