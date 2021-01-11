(defproject conjectural-deductive-programming "0.1.0-SNAPSHOT"
  :description "A framework for conjectural deductive programming."
  :license {:name "MIT License"
            :url "https://opensource.org/licenses/MIT"}
  :dependencies [[org.clojure/clojure "1.10.1"]
                 [clojure-csv/clojure-csv "2.0.1"]
                 [com.taoensso/tufte "2.2.0"]]
  :target-path "target/%s"
  :profiles {:uberjar {:aot :all
                       :jvm-opts ["-Dclojure.compiler.direct-linking=true"]}})
