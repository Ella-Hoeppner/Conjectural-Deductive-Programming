(ns cdp.language
  (:require [clojure.set :as set]))

; An "environment" (abbreviated "env") is a hashmap that maps function names
; to functions. Function names can be anything, but usually should be something
; like a symbol or keyword.

; A "distribution" (abbreivated "dist") is a function of 0 arguments that, when
; executed, returns a list where the first element is a function name. If any
; of the remaining elements in the list are :SUBTREE, that means that it should
; be replaced with a subtree.

(defn eval-tree
  "Evaluates a tree using the definitions in `env`."
  [tree env]
  (cond (and (seq? tree) (get env (first tree))) (apply (get env (first tree))
                                                        (map #(eval-tree % env) (rest tree)))
        (and (seq? tree) (= :S (first tree))) (eval-tree (second tree) env)
        :else tree))

(defn random-tree
  "Generates a random tree no deeper than `max-depth`. The tree is generated
   by sampling `dist` and recursively replacing any instances of :SUBTREE with
   further samples from `dist`. Trees generated with this function will include
   :S keywords at locations in the tree where the tree can be validly split."
  [env dist max-depth]
  (list :S
        (some (fn [sample]
                (when (or (not (some #(= % :SUBTREE) sample))
                          (> max-depth 1))
                  (conj (map (fn [arg]
                               (if (= arg :SUBTREE)
                                 (random-tree env
                                              dist
                                              (dec max-depth))
                                 arg))
                             (rest sample))
                        (first sample))))
              (repeatedly dist))))

(defn navigate-tree
  "Returns the subtree of `tree` at the location described by `path`. `path`
   should be a sequence of integers denoting which element in the list to
   select at each step. For instance, for a tree (A (B C) D), a path (1)
   would return (B C), while a path of (1 0) would return B."
  [tree path]
  (if (empty? path)
    tree
    (navigate-tree (nth tree (first path)) (rest path))))

(defn replace-subtree
  "Returns a tree where the subtree in `tree` at the location described by
   `path` is replaced with `subtree`. `path` is interpreted as in
   [[navigate-tree]]."
  [tree path replacement]
  (if (empty? path)
    replacement
    (let [index (first path)]
      (concat (take index tree)
              (conj (drop (inc index) tree)
                    (replace-subtree (nth tree index)
                                     (rest path)
                                     replacement))))))

(defn split-paths
  "Identifies and returns all paths that may be validly split. See
   [[navigate-tree]] for a description of how paths are interpreted."
  [tree]
  (if (seq? tree)
    (let [subtree-paths (apply concat
                               (map (fn [subtree index]
                                      (map #(conj % index)
                                           (split-paths subtree)))
                                    (rest tree)
                                    (rest (range))))]
      (if (= (first tree) :S)
        (conj subtree-paths '())
        subtree-paths))
    '()))

(defn point-mutation
  "Creates a mutant of `tree` by choosing a random valid path, and replacing
   the subtree at that path with a new, random subtree no deeper than
   `max-depth`."
  [tree env dist max-depth]
  (let [chosen-path (rand-nth (split-paths tree))]
    (replace-subtree tree chosen-path (random-tree env dist max-depth))))

(defn crossover-mutation
  "Creates a mutant of `base-tree` by replacing a random subtree within it with
   a random subtree from `donor-tree`."
  [base-tree donor-tree]
  (let [base-path (rand-nth (split-paths base-tree))
        donor-path (rand-nth (split-paths donor-tree))]
    (replace-subtree base-tree
                     base-path
                     (navigate-tree donor-tree donor-path))))

(defn without-splits
  "Returns a version of `tree` without all of the :S keywords, which denote
   locations where a tree is allowed to be split. This is useful for printing
   more human-readable versions of trees."
  [tree]
  (if (list? tree)
    (map without-splits
         (if (= (first tree) :S)
           (second tree)
           tree))
    tree))