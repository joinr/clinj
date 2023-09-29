(ns clinj.core
  (:require [clj-linear.core :as lp]))


(defn indices
  ([root n]
   (cond (number? n)
         (into (sorted-set) (map (fn [x] [root x])) (range n))
         (coll? n)
         (into (sorted-set) (map (fn [x] [root x])) n)
         :else (throw (ex-info "unknown type" {:in n}))))
  ([n] (indices (str (gensym "var")) n)))


#_
(defmacro cart [& xs]
  (let [kvs (zipmap (repeatedly (count xs) #(gensym "k")) xs)
        ks (keys kvs)]
  `(for [~@(reduce (fn [acc [k v]] (conj acc k v)) [] kvs)]
     [~@ks])))

;;https://stackoverflow.com/questions/18246549/cartesian-product-in-clojure
(defn cart
  ([xs] xs)
  ([xs ys]
   (mapcat (fn [x] (map (fn [y] (list x y)) ys)) xs))
  ([xs ys & more]
   (mapcat (fn [x] (map (fn [z] (cons x z)) (apply cart (cons ys more)))) xs)))


(defn as-index [x]
  (cond (or (keyword? x) (string? x) (number? x))   x
        :else (vec x)))
(defn cartvec [xs] (->> xs (apply cart) (mapv as-index) ))

(defn readble [idx]
  (if (coll? idx)
    (let [[root idx] idx]
      (str root "_" idx))
    idx))

(defn readable-index [idx]
  (cond (not (coll? idx)) (str idx)
        (coll? (idx 1))   (clojure.string/join "," (mapv readble idx))
        :else            (str (idx 0) "_" (idx 1))))

(defmacro set-id! []
  `(when-not ~'id
     (set! ~'id (str ~'root "(" (readable-index ~'idx) ")"))))

(deftype Var [root idx ^:unsynchronized-mutable ^String id]
  clojure.lang.IDeref
  (deref [this] (set-id!) id)
  clojure.lang.ILookup
  (valAt [this k]
    (case k :root root :idx idx :id (do (set-id!) id)
          (throw (ex-info "unknown key!" {:in k}))))
  (valAt [this k not-found]
    (case k :root root :idx idx :id (do (set-id!) id)
          not-found))
  clojure.lang.Counted
  (count [this] 3)
  clojure.lang.Seqable
  (seq [this] (seq {:root root :idx idx :id (do (set-id!) id)}))
  clojure.lang.IHashEq
  (hasheq [this] (set-id!) (hash id)))

(defn ->var [root idx] (Var. root idx nil))

(defn ->vars [root & idxs]
  (->> (for [idx (cartvec idxs)]
         [idx (->var root idx)])
       (into (sorted-map))))

;;so we know that terms are just mappings of variables to linear combinations.
;;where the map {variable coefficient} denotes the sparse mapping.
;;so we can just accumulate maps.

;;implements summation relation.
(defmacro sum [indices & body]
  `(->> (for [~@indices]  (lp/expression  ~@body))
        (reduce (fn [acc# term#]
                  (let [[k# v#] (first term#)]
                    (assoc acc# k# v#))) {})))

;;stupid toy problem.
(let [is    (indices "i" 10)
      xs    (->vars :xs is)
      odds  (->> is (eduction (filter (comp odd? second))))
      evens (->> is (eduction (filter (comp even? second))))]
  (lp/minimize
   (lp/expression (+ :evens :odds))
   (lp/constraints
     (= (sum [idx evens]
          (xs idx))
        :evens)
     (= (sum [idx odds]
          (xs idx)) :odds)
     (<= (+ :evens :odds) 20)
     (>= :evens 5)
     (>= :odds  3))))

;;more sophisticated cat food blending problem.

(def data
  "Stuff	Protein	Fat	Fibre	Salt
  Chicken	0.1	0.08	0.001	0.002
  Beef	0.2	0.1	0.005	0.005
  Mutton	0.15	0.11	0.003	0.007
  Rice	0	0.01	0.1	0.002
  Wheat	0.04	0.01	0.15	0.008
  Gel	0	0	0	0")

(def ingredient-data
  (let [fields [:Stuff :Protein :Fat :Fiber :Salt]]
    (->> data
         clojure.string/split-lines
         (drop 1)
         (map (fn [ln]
                (let [[x & xs] (clojure.string/split ln  #"\t")]
                  (zipmap fields (cons (clojure.string/trim x)
                                       (map parse-double xs))))))
         (reduce (fn [acc {:keys [Stuff] :as r}]
                   (assoc acc Stuff (dissoc r :Stuff))) {}))))
#_
{"Chicken" {:Protein 0.1, :Fat 0.08, :Fiber 0.001, :Salt 0.002},
 "Beef" {:Protein 0.2, :Fat 0.1, :Fiber 0.005, :Salt 0.005},
 "Mutton" {:Protein 0.15, :Fat 0.11, :Fiber 0.003, :Salt 0.007},
 "Rice" {:Protein 0.0, :Fat 0.01, :Fiber 0.1, :Salt 0.002},
 "Wheat" {:Protein 0.04, :Fat 0.01, :Fiber 0.15, :Salt 0.008},
 "Gel" {:Protein 0.0, :Fat 0.0, :Fiber 0.0, :Salt 0.0}}

(def costs
  {"Chicken" 0.013
   "Beef"    0.008
   "Mutton"  0.010
   "Rice"    0.002
   "Wheat"   0.005
   "Gel"     0.001})

(def requirements
  {:Protein  8
   :Fat      6
   :Fiber    2
   :Salt   0.4})

;;set for indexing.
(def ingredients (keys costs))
;;decision variables.
(def choices (->vars "ingredient" ingredients))

;;non-negativity constraints.
(def non-neg
  (for [i ingredients]
    (lp/constraint (>= (choices i) 0))))

;;formulation 1:
(defn solve []
  (lp/minimize
   (lp/expression :total-cost)
   (into (lp/constraints
           (= (sum [i ingredients] (choices i)) 100) ;;percentage total
           (= :total-cost    (sum [i ingredients] (* (costs i) (choices i))))
           (= :total-protein (sum [i ingredients]
                               (* (get (ingredient-data i) :Protein) (choices i))))
           (= :total-fat   (sum [i ingredients]
                             (* (get (ingredient-data i) :Fat) (choices i))))
           (= :total-fiber (sum [i ingredients]
                             (* (get (ingredient-data i) :Fiber) (choices i))))
           (= :total-salt (sum [i ingredients]
                            (* (get (ingredient-data i) :Salt) (choices i))))
           (>= :total-protein (requirements :Protein))
           (>= :total-fat     (requirements :Fat))
           (<= :total-fiber   (requirements :Fiber))
           (<= :total-salt   (requirements :Salt)))
         non-neg)))

;; {:total-fat 5.999999999999999,
;;  :total-fiber 0.3,
;;  :total-protein 11.999999999999998,
;;  :total-salt 0.3,
;;  #<Var@3141fc8f: "ingredient(Wheat)"> 0.0,
;;  #<Var@34020aaf: "ingredient(Rice)"> 0.0,
;;  :total-cost 0.52,
;;  #<Var@3dc7855a: "ingredient(Beef)"> 59.99999999999999,
;;  #<Var@958d799: "ingredient(Chicken)"> 0.0,
;;  #<Var@4aec7071: "ingredient(Gel)"> 40.0,
;;  #<Var@11f55d5: "ingredient(Mutton)"> 0.0}
;;fancier:

(def requirements
  {:Protein  8
   :Fat      6
   :Fiber    2
   :Salt     0.4})

(def maximums #{:Fiber :Salt})

(def daily-requirements
  (for [[r v] requirements]
    (lp/constraint
     ((if (maximums r)
        <=
        >=)
      (sum [i ingredients] (* (get (ingredient-data i) r) (choices i)))   v))))

(defn solve2 []
  (lp/minimize
   (sum [i ingredients] (* (costs i) (choices i)))
   (into (lp/constraints
           (= (sum [i ingredients] (choices i)) 100)) ;;percentage total
         (concat non-neg
                 daily-requirements))))

;; {#<Var@958d799: "ingredient(Chicken)"> 0.0,
;;  #<Var@3dc7855a: "ingredient(Beef)"> 60.0,
;;  #<Var@11f55d5: "ingredient(Mutton)"> 0.0,
;;  #<Var@34020aaf: "ingredient(Rice)"> 0.0,
;;  #<Var@3141fc8f: "ingredient(Wheat)"> 0.0,
;;  #<Var@4aec7071: "ingredient(Gel)"> 40.0}
