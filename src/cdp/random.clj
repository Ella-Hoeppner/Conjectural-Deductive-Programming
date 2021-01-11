(ns cdp.random)

(defn normalize-weights
  "Given a sequence of numbers, returns a list of equal size that sums to 1,
   such that each element is proportional to the corresponding element in the
   input."
  [weights]
  (let [sum (apply + weights)]
    (map
     #(/ % sum)
     weights)))

(defn weighted-choice
  "Randomly chooses a value from `objects` according to the `weights` sequence.
   The chance of each object in `objects` being chosen is proportional to the
   corresponding value in `weights`."
  [weights objects]
  (let [probabilities (normalize-weights weights)]
    (loop [c (rand) p probabilities o objects]
      (if (<= c (first p))
        (first o)
        (recur (- c (first p)) (rest p) (rest o))))))

(defn rand-geom
  "Returns a sample of the geometic distribution with parameter `p`."
  [p]
  (if (> p (rand))
    (inc (rand-geom p))
    0))

(defn rand-exp
  "Returns a sample of the exponential distibution with parameter 1."
  []
  (- (Math/log (rand))))

(defn double-sided-rand-geom
  "50% of the time, returns a sample of the geometric distribution with
   parameter `p`, and returns a negative sample of the same distribution the
   other 50% of the time."
  [p]
  (* (rand-geom p)
     (rand-nth [-1 1])))

(defn double-sided-rand-exp
  "50% of the time, returns a sample of the exponential distribution, and
   returns a negative sample of the same distribution the other 50% of the
   time."
  []
  (* (rand-exp)
     (rand-nth [-1 1])))