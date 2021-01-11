(ns cdp.evolution
  (:require [clojure.set :as set]
            [cdp.language :as lang]))

; An "executation state" (also referred to simply as a "state") is a map
; containing the keys :rules, :statements, :labels, :progress, and :records.
; :rules should map to a vector of program trees, while :statements should map
; to a vector of statements (the form of the statements can be anything, it
; just depends on the nature of the problem being solved), and :labels maps to
; a vector of labels with the same length as the :statements vector. :progress
; should map to a vector of integers the same size as the :rules vector. Each
; integer in :progress is interpreted as an index describing how many
; statements in :statements the corresponding rule has already been applied to.
; A value of n at index i in :progress denotes that the ith rule has already
; been applied to the first i statements in :statements. :records should be a
; vector the same length as :statements, where each element is a set containing
; 0 or more maps, each of which have the keys :rule, :statement, and :label.
; The set at index i in :records denotes that the statement at index i in
; :statements can be derived from each triple in the set.

(defn combinations
  "Given a list `l` of sets, returns a list of all possible lists who's first
   element comes from the second set, second element comes from the second set,
   etc."
  [l]
  (cond
    (= (count l) 0) '()
    (= (count l) 1) (if (empty? (first l))
                      '(())
                      (map #(list %)
                           (first l)))
    :else (let [rest-combinations (combinations (rest l))]
            (if (empty? (first l))
              rest-combinations
              (apply concat
                     (map (fn [val]
                            (map #(conj % val)
                                 rest-combinations))
                          (first l)))))))

(defn statement-generators
  "Given an execution state, a statement/label pair within that state, and two
   lists of the invariant statements and corresponding invariant labels,
   returns a set of all sets of rules within the execution state that would
   cause the statement/label pair to be generated from the invariant
   statements/labels. A set of rules that can generate a particular statement/
   label pair is referred to as a 'generator' of that pair." 
  [execution-state statement label invariant-statements invariant-labels]
  (let [statements (:statements execution-state)
        labels (:labels execution-state)
        records (:records execution-state)]
    ((fn f [[statement label] ignorable-pairs]
       (let [records (some (fn [index]
                             (when (and (= (nth statements index) statement)
                                        (= (nth labels index) label))
                               (nth records index)))
                           (range (count statements)))]
         (apply set/union
                (map (fn [record]
                       (let [record-rule (:rule record)
                             record-statement (:statement record)
                             record-label (:label record)
                             record-pair [record-statement record-label]]
                         (if (ignorable-pairs record-pair)
                           #{#{record-rule}}
                           (into #{} (map #(conj % record-rule)
                                          (f record-pair (conj ignorable-pairs record-pair)))))))
                     records))))
     [statement label]
     (into #{} (map vector
                    invariant-statements
                    invariant-labels)))))

(defn remove-statement
  "Given an execution state and an index, removes the statement, label, and
   record at that index. Also updates the progress field to reflect the
   removal of the statement, and removes any records which reference the
   removed statement."
  [execution-state index]
  (let [statements (:statements execution-state)
        statement (nth statements index)
        labels (:labels execution-state)
        label (nth labels index)
        without-nth (fn [v n]
                      (into (subvec v 0 n) (subvec v (inc n))))]
    (assoc execution-state
           :statements (without-nth statements index)
           :labels (without-nth labels index)
           :progress (mapv #(if (>= % index) (dec index) index)
                           (:progress execution-state))
           :records (mapv (fn [record-set]
                            (into #{} (remove #(and (= (:statement %) statement)
                                                    (= (:label %) label))
                                              record-set)))
                          (without-nth (:records execution-state) index)))))

(defn remove-orphan-statements
  "Given an execution state, a list  of invariant statements, and a list of
   corresponding invariant labels, removes all statements/label pairs in the
   state which have no record, except for those that are invariant."
  [execution-state invariant-statements invariant-labels]
  (let [invariant-set (into #{} (map vector 
                                     invariant-statements
                                     invariant-labels))]
    (loop [state execution-state
           c 0]
      (let [orphan-index (some (fn [[index statement label record-set]]
                                 (when (and (empty? record-set) (not (invariant-set [statement label])))
                                   index))
                               (map vector
                                    (range)
                                    (:statements state)
                                    (:labels state)
                                    (:records state)))]
        (if orphan-index
          (recur (remove-statement state orphan-index)
                 (inc c))
          state)))))

(defn remove-rule
  "Given an execution state, a list of invariant statements and a corresponding
   list of invariant labels, and a rule, removes the rule and all statements
   that relied upon that rule to be derived"
  [execution-state invariant-statements invariant-labels rule]
  (let [rule-index (some (fn [[index state-rule]]
                           (when (= rule state-rule)
                             index))
                         (map vector
                              (range)
                              (:rules execution-state)))
        without-nth (fn [v n]
                      (into (subvec v 0 n) (subvec v (inc n))))]
    (remove-orphan-statements (assoc execution-state
                                     :rules (without-nth (:rules execution-state) rule-index)
                                     :progress (without-nth (:progress execution-state) rule-index)
                                     :records (mapv (fn [record-set]
                                                      (into #{} (remove #(= (:rule %) rule)
                                                                        record-set)))
                                                    (:records execution-state)))
                              invariant-statements
                              invariant-labels)))

(defn find-goal-generators
  "Given an execution state, a goal counter, a list of invariant statements,
   and a list of corresponding invariant labels, returns a list of sets of
   generators responsible for accomplish each goal that the execution state
   currently accomplishes."
  [execution-state goal-counter invariant-statements invariant-labels]
  (mapv (fn [goal-set]
          (apply set/union
                 (map (fn [[statement label]]
                        (statement-generators execution-state
                                              statement
                                              label
                                              invariant-statements
                                              invariant-labels))
                      goal-set)))
        (goal-counter (:statements execution-state) (:labels execution-state))))

(defn may-remove?
  "Given a vector of sets goal generators and a set `removal` of rules to
   potentially be removed, determines whether or not the rules can be removed
   without causing any of goals to become unfulfilled."
  [goal-generators-vector removal]
  (reduce (fn [value goal-generators]
            (and value
                 (some (fn [goal-generator]
                         (empty? (set/intersection goal-generator
                                                   removal)))
                       goal-generators)))
          true
          goal-generators-vector))

(defn resolve-conflicts
  "Given an execution state, a goal counter, a conflict predicate, a list of
   invariant statements and a list of corresponding invariant labels, attempts
   to resolve all conflicts indicated by the conflict predicate by removing
   the rules that generate the conflicts. If resolving some conflict would
   require removing a set of rules that would lead to some goal becoming
   unfulfilled, then the conflict will not be resolved."
  [execution-state goal-counter conflict-predicate invariant-statements invariant-labels]
  (loop [current-state execution-state
         index 0
         unsolvable-conflicts #{}
         goal-generators-vector (find-goal-generators execution-state
                                                      goal-counter
                                                      invariant-statements
                                                      invariant-labels)]
    (if (>= index (count (:statements current-state)))
      [current-state unsolvable-conflicts]
      (let [statement (nth (:statements current-state) index)
            label (nth (:labels current-state) index)
            pair [statement label]]
        (if (and (not (unsolvable-conflicts pair))
                 (conflict-predicate statement label))
          (let [conflict-generators (statement-generators current-state
                                                          statement
                                                          label
                                                          invariant-statements
                                                          invariant-labels)
                minimal-conflict-generators (remove (fn [generator]
                                                      (some (fn [other-generator]
                                                              (and (not= generator other-generator)
                                                                   (set/superset? generator other-generator)))
                                                            conflict-generators))
                                                    conflict-generators)
                conflict-solutions (into #{} (map #(into #{} %)
                                                  (combinations minimal-conflict-generators)))
                acceptable-solution (some (fn [solution]
                                            (when (may-remove? goal-generators-vector
                                                               solution)
                                              solution))
                                          (shuffle conflict-solutions))]
            (if acceptable-solution
              (let [new-state (reduce (fn [state rule]
                                        (remove-rule state
                                                     invariant-statements
                                                     invariant-labels
                                                     rule))
                                      current-state
                                      acceptable-solution)]
                (recur new-state
                       0
                       unsolvable-conflicts
                       (find-goal-generators new-state
                                             goal-counter
                                             invariant-statements
                                             invariant-labels)))
              (recur current-state
                     (inc index)
                     (conj unsolvable-conflicts pair)
                     goal-generators-vector)))
          (recur current-state
                 (inc index)
                 unsolvable-conflicts
                 goal-generators-vector))))))

(defn execute
  "Given an execution state, an environment, a label predicate, and a label
   generator, iteratively derives new statements from the existing statements
   and rules within the execution state. Uses the label predicate to determine
   whether a statement is allowed to be used for generating new statements,
   and the label predicate to determine the label of each new statement based
   on the statement of the rule from which it was derived.
   
   Optionally, takes in a number `max-steps` that limits the number of times
   that this function will attempt to derive new statements. If `max-steps`
   is not provided, execution will continue until no new statements can be
   derived. Depending on the nature of the label predicate and generator,
   this may lead to an infinite loop."
  [execution-state env label-predicate label-generator & [max-steps]]
  (loop [steps (or max-steps ##Inf)
         state execution-state]
    (if (<= steps 0)
      state
      (let [statements (:statements state)
            labels (:labels state)
            progress (:progress state)
            cache (:computation-cache state)
            rule-index (some #(when (< (nth progress %)
                                       (count statements))
                                %)
                             (range (count progress)))]
        (if rule-index
          (let [new-progress (update progress rule-index inc)
                statement-index (nth progress rule-index)
                statement (nth statements statement-index)
                label (nth (:labels state) statement-index)]
            (recur (dec steps)
                   (if (label-predicate label)
                     (let [rule (nth (:rules state) rule-index)
                           cached-result (get cache [rule statement])
                           result (or cached-result ((lang/eval-tree rule env) statement))
                           result-label (label-generator label)
                           result-index (some #(when (and (= (nth statements %) result)
                                                          (= (nth labels %) result-label))
                                                 %)
                                              (range (count statements)))
                           new-record {:rule rule
                                       :statement statement
                                       :label label}]
                       (if result-index
                         (assoc state
                                :progress new-progress
                                :records (let [records (:records state)]
                                           (assoc records
                                                  result-index
                                                  (conj (nth records result-index)
                                                        new-record))))
                         (let [new-state (assoc state
                                                :progress new-progress
                                                :statements (conj statements result)
                                                :labels (conj labels result-label)
                                                :records (conj (:records state)
                                                               #{new-record}))]
                           (if cached-result
                             new-state
                             (assoc new-state
                                    :computation-cache (assoc cache
                                                              [rule statement]
                                                              result))))))
                     (assoc state
                            :progress new-progress))))
          state)))))

(defn evolve
  "Given a list of invariant statement, a list of corresponding invariant
   labels, an environment, a distribution, a label predicate, a label
   generator function, a goal counter, a conflict predicate, and a number of
   steps, attempts to evolve a set of rules that generate statement/label pairs
   that statisfy the goals without causing any conflicts, as measured by the
   goal counter and conflict predicate. It will do so by randomly generating
   rules using `dist, such that each rule consists of a program tree built form
   the operations in `env`. The first rules will be created randomly, and after
   that new rules are created by varying existing rules using point mutation
   and crossover operations.
   
   `invariant-statements` should be a list of statements that will always be
   present in the execution state regardless of what rules exist. For
   classification problems, these statements should consist of the data values
   that you are attempting to classify. `invariant-labels` should be a list of
   the same size containing a label for each invariant statement.
   
   `env`, the environment, should be a map which maps function names to
   functions. The functions within this map are the operations which may be
   used within the program trees that define rules.
   
   `dist`, the distribution, should be a function of 0 arguments representing
   a probability distribution used to generate program trees. It should always
   return a list of elements such that the first element is the name of some
   function in the environment, and the rest of the elements are arguments for
   that function. If any of the elements is instead :SUBTREE, that indicates
   that that element should be replaced with a subtree.
   
   `label-predicate` is a function that takes in a label and returns true or
   false. When true is returned for a label, that indicates that the
   corresponding statement may be used to generate further statements. The
   label assigned to new statements is given by applying `label-generator`,
   which should be a function that takes in a single label and returns a new
   label, to the statement used to derive the new statement.
   
   `goal-counter` should be a function that takes in a list of statements
   and a list of corresponding labels, and returns a list of sets. Each
   set in the list should contain one or more statement/label pairs that
   satisfy a ceratin goal. For a classification problem, each set should
   indicate that a particualr value is properly classified by the
   statement/label pair within the set.
   
   `conflict-predicate` should be a function that takes in a statement and
   a corresponding label, and should return a boolean describing whether or not
   that statement/label pair is considered a conflict. When this predicate
   returns true for a statement/label pair, the mind will attempt to discard
   the pair by removing the rules that lead to it's creation. For a
   classification problem, this should return true when the statement/label
   pair incorrectly classifies some data value.
   
   The evolution takes place over a number of steps, as specified by the
   `steps` input. On each step, a new rule will be generated, and the function
   will derive all statements that can possibly be derived from that rule and
   the pre-existing rules and statements. Then, the function will see if any
   of the statements that it has derived cause any conflicts, and if so it will
   attempt to remove the rules responsible for the conflicts. However, the
   function will not remove a rule if it is necessary to satisfy one of the
   goals that is currently achieved, as defined by the goal counter.
   
   `statement-cap` is an optional argument that places a limit on the number of
   statements the execution state should contain, while `rule-cap` places a
   limit on the number of rules. At each step, if the number of statements or
   rules exceeds the respective caps, the function will attempt to discard some
   rules, and the corresponding statements, until the number of rules
   statements drops below the cap. As when resolving conflicts, the function
   will never remove a rule necessary for achieving some goal, so it is not
   guaranteed that the number of rules/statements will always remain below the
   cap.
   
   `max-depth` describes the maximum depth of the program trees generated at
   the start of evolution, along with the maximum depth of new subtrees created
   during point mutation. Defaults to 4.
   
   `new-prob` describes the probability of creating a brand new rule, rather
   than mutating some existing rule, when creating a rule for each new step.
   Defaults to 0.05.
   
   `crossover-prob` describes the probability of creating a new rule through
   crossover mutation during each step of evolution. When crossover is not
   used, point mutation is used instead, so the probability of point mutation
   being used is complementary to this probability. Defaults to 0.7.
   
   Optionally, you can pass an `evaluator` function, which should expect an 
   execution state as an input. After each step `evaluator` will be executed
   with the current state as an input. This can be used to print custom
   output at each step, or keep track of the state at each step, etc.
   
   When the `verbose` flag, which defaults to false, is set to true, the
   function will print out information about the current state after each
   step of execution."
  [invariant-statements invariant-labels env dist label-predicate label-generator goal-counter conflict-predicate steps & [statement-cap rule-cap max-depth new-prob crossover-prob evaluator verbose]]
  (let [max-depth (or max-depth 4)
        new-prob (or new-prob 0.05)
        crossover-prob (or crossover-prob 0.7)]
    (when verbose
      (println (str "Starting evolution:")))
    (loop [current-step 0
           state {:rules []
                  :statements (vec invariant-statements)
                  :labels (vec invariant-labels)
                  :records (mapv (fn [x] #{}) invariant-statements)
                  :progress []
                  :computation-cache {}}
           important-rules []]
      (if (< current-step steps)
        (let [mutant-rule (some (fn [new-rule]
                                  (when (not (some #(= new-rule %)
                                                   (:rules state)))
                                    new-rule))
                                (repeatedly (fn []
                                              (if (or (empty? important-rules)
                                                      (< (rand) new-prob))
                                                (lang/random-tree env dist max-depth)
                                                (if (< (rand) crossover-prob)
                                                  (lang/crossover-mutation (rand-nth important-rules) (rand-nth important-rules))
                                                  (lang/point-mutation (rand-nth important-rules) env dist max-depth))))))
              mutated-state (assoc state
                                   :rules (conj (:rules state) mutant-rule)
                                   :progress (conj (:progress state) 0))
              progressed-state (execute mutated-state
                                        env
                                        label-predicate
                                        label-generator
                                        ##Inf)
              [resolved-state unresolvable] (resolve-conflicts progressed-state
                                                               goal-counter
                                                               conflict-predicate
                                                               invariant-statements
                                                               invariant-labels)
              final-state (loop [current-state resolved-state]
                            (if (and (< (count (:rules current-state)) rule-cap)
                                     (< (count (:statements current-state)) statement-cap))
                              current-state
                              (let [goal-generators (find-goal-generators current-state
                                                                          goal-counter
                                                                          invariant-statements
                                                                          invariant-labels)
                                    removable-rule (some (fn [rule]
                                                           (when (may-remove? goal-generators
                                                                              #{rule})
                                                             rule))
                                                         (:rules current-state))]
                                (if removable-rule
                                  (recur (remove-rule current-state
                                                      invariant-statements
                                                      invariant-labels
                                                      removable-rule))
                                  current-state))))
              goal-generators (find-goal-generators resolved-state
                                                    goal-counter
                                                    invariant-statements
                                                    invariant-labels)
              contributing-rules (vec (apply set/union
                                      (map (partial apply set/union)
                                           goal-generators)))]
          (when verbose
              (println (str "\nStep "
                            (inc current-step)
                            ":   Rules - "
                            (count (:rules final-state))
                            " ("
                            (count (vec (apply set/union
                                               (map (partial apply set/union)
                                                    (find-goal-generators final-state
                                                                          goal-counter
                                                                          invariant-statements
                                                                          invariant-labels)))))
                            "), Statements - "
                            (count (:statements final-state))
                            " ("
                            (count unresolvable)
                            "), Goals achieved - "
                            (count goal-generators))))
          (when evaluator (evaluator final-state))
          (recur (inc current-step)
                 final-state
                 contributing-rules))
        (do
          (when verbose
            (println "evolution completed with "
                     (count (:rules state))
                     " rules and "
                     (count (:statements state))
                     "statements"))
          state)))))