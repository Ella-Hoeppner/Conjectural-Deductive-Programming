(ns tests.evolution
  (:require [clojure.set :as set]
            [cdp.language :as lang]
            [cdp.main :as main]
            [cdp.evolution :as evo]))

(use 'clojure.test)

(def simple-success-state
  (evo/execute {:statements (main/invariant-statements 1)
                :labels (main/invariant-labels 1)
                :records [#{}]
                :rules ['(constant (0))]
                :progress [0]
                :computation-cache {}}
               main/env
               main/label-predicate
               main/label-generator))

(def conflict-state-1
  (evo/execute {:statements (main/invariant-statements 1)
                :labels (main/invariant-labels 1)
                :records [#{}]
                :rules ['(constant (0)) '(constant (1))]
                :progress [0 0]
                :computation-cache {}}
               main/env
               main/label-predicate
               main/label-generator))

(def conflict-state-2 '{:statements [(5.1 3.5 1.4 0.2) (0) (0) (0) (5.1 3.5 1.4 0.2) (1) (1) (5.1 3.5 1.4 0.2) (5.1 3.5 1.4 0.2)]
                      :labels
                      [{:life 3, :index 0}
                       {:life 2, :index 0}
                       {:life 1, :index 0}
                       {:life 0, :index 0}
                       {:life 2, :index 0}
                       {:life 1, :index 0}
                       {:life 0, :index 0}
                       {:life 1, :index 0}
                       {:life 0, :index 0}]
                      :records
                      [#{}
                       #{{:rule (constant (0)), :statement (5.1 3.5 1.4 0.2), :label {:life 3, :index 0}}}
                       #{{:rule (constant (0)), :statement (0), :label {:life 2, :index 0}}
                         {:rule (constant (0)), :statement (5.1 3.5 1.4 0.2), :label {:life 2, :index 0}}}
                       #{{:rule (constant (0)), :statement (1), :label {:life 1, :index 0}}
                         {:rule (constant (0)), :statement (0), :label {:life 1, :index 0}}
                         {:rule (constant (0)), :statement (5.1 3.5 1.4 0.2), :label {:life 1, :index 0}}}
                       #{{:rule (if (= (identity) (constant (0))) (constant (1)) (identity))
                          :statement (5.1 3.5 1.4 0.2)
                          :label {:life 3, :index 0}}}
                       #{{:rule (if (= (identity) (constant (0))) (constant (1)) (identity)), :statement (0), :label {:life 2, :index 0}}}
                       #{{:rule (if (= (identity) (constant (0))) (constant (1)) (identity)), :statement (1), :label {:life 1, :index 0}}
                         {:rule (if (= (identity) (constant (0))) (constant (1)) (identity)), :statement (0), :label {:life 1, :index 0}}}
                       #{{:rule (if (= (identity) (constant (0))) (constant (1)) (identity))
                          :statement (5.1 3.5 1.4 0.2)
                          :label {:life 2, :index 0}}}
                       #{{:rule (if (= (identity) (constant (0))) (constant (1)) (identity))
                          :statement (5.1 3.5 1.4 0.2)
                          :label {:life 1, :index 0}}}]
                      :rules [(constant (0)) (if (= (identity) (constant (0))) (constant (1)) (identity))]
                      :progress [9 9]
                      :computation-cache
                      {[(constant (0)) (5.1 3.5 1.4 0.2)] (0)
                       [(constant (0)) (0)] (0)
                       [(if (= (identity) (constant (0))) (constant (1)) (identity)) (5.1 3.5 1.4 0.2)] (5.1 3.5 1.4 0.2)
                       [(if (= (identity) (constant (0))) (constant (1)) (identity)) (0)] (1)}})

(defn random-state [rule-count]
  (evo/execute {:statements (main/invariant-statements 1)
                :labels (main/invariant-labels 1)
                :records [#{}]
                :rules (vec (take rule-count
                                  (repeatedly (fn []
                                                (lang/random-tree main/env
                                                                  main/dist
                                                                  3)))))
                :progress (vec (take rule-count
                                     (repeat 0)))
                :computation-cache {}}
               main/env
               main/label-predicate
               main/label-generator))

(deftest test-remove-statement
  (testing "removing single statement"
    (is (= (dec (count (:statements simple-success-state)))
           (count (:statements (evo/remove-statement simple-success-state
                                                     1))))))
  (let [all-removed-state (nth (iterate #(evo/remove-statement % 1)
                                        simple-success-state)
                               3)]
    (testing "removing all statements"
      (is (= 1
             (count (:statements all-removed-state)))))
    (testing "removing all statements resets progress"
      (is (= [0]
             (:progress all-removed-state))))
    (testing "removing all statements and executing again returns to the same state"
      (is (= simple-success-state
             (evo/execute all-removed-state
                          main/env
                          main/label-predicate
                          main/label-generator))))))

(deftest test-remove-rule
  #_(testing "removing sole rule"
    (is (= 1
           (count (:statements (evo/remove-rule simple-success-state
                                                (main/invariant-statements 1)
                                                (main/invariant-labels 1)
                                                (first (:rules simple-success-state))))))))
  (testing "removing rules is equivalent to not having a rule in the first place"
    (let [base-rule '(constant (0))
          secondary-rule '(if (= (identity) (constant (0))) (constant (1)) (identity))
          base-state (evo/execute {:statements (main/invariant-statements 1)
                                   :labels (main/invariant-labels 1)
                                   :records [#{}]
                                   :rules [base-rule]
                                   :progress [0]
                                   :computation-cache {}}
                                  main/env
                                  main/label-predicate
                                  main/label-generator)
          secondary-state (evo/execute {:statements (main/invariant-statements 1)
                                        :labels (main/invariant-labels 1)
                                        :records [#{}]
                                        :rules [base-rule secondary-rule]
                                        :progress [0 0]
                                        :computation-cache {}}
                                       main/env
                                       main/label-predicate
                                       main/label-generator)
          reduced-state (evo/remove-rule secondary-state
                                         (main/invariant-statements 1)
                                         (main/invariant-labels 1)
                                         secondary-rule)]
      (is (= (:statements base-state)
             (:statements reduced-state))))))

(deftest test-find-goal-generators
  (testing "simple success lineage"
    (is (= '[#{#{(constant (0))}}]
           (evo/find-goal-generators simple-success-state
                                          main/goal-counter
                                          (main/invariant-statements 1)
                                          (main/invariant-labels 1)))))
  (testing "simple conflict lineage"
    (is (= '[#{#{(constant (1)) (constant (0))} #{(constant (0))}}]
           (evo/find-goal-generators conflict-state-1
                                          main/goal-counter
                                          (main/invariant-statements 1)
                                          (main/invariant-labels 1))))))

(deftest test-resolve-conflicts
  (testing "resolving simple conflict"
    (is (= 1
           (count (:rules (first (evo/resolve-conflicts conflict-state-1
                                                        (evo/find-goal-generators conflict-state-1
                                                                                       main/goal-counter
                                                                                       (main/invariant-statements 1)
                                                                                       (main/invariant-labels 1))
                                                        main/conflict-predicate
                                                        (main/invariant-statements 1)
                                                        (main/invariant-labels 1)))))))))

(deftest test-evolve
  (dotimes [i 1000]
    (testing "score doesn't decreases during evolution with single input"
      (let [history (evo/evolve (main/invariant-statements 1)
                                (main/invariant-labels 1)
                                main/env
                                main/dist
                                main/label-predicate
                                main/label-generator
                                main/goal-counter
                                main/conflict-predicate
                                2
                                3
                                0.1
                                0.5
                                nil
                                false)
            [initial-score second-score] (map main/evaluate history)]
        (is (>= second-score
                initial-score))))))