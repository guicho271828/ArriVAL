;;;; Autogenerated ASD file for system "ARRIVAL"
;;;; In order to regenerate it, run update-asdf
;;;; from shell (see https://github.com/phoe-krk/asd-generator)
;;;; For those who do not have update-asdf,
;;;; run `ros install asd-generator` (if you have roswell installed)
;;;; There are also an interface available from lisp:
;;;; (asd-generator:regen &key im-sure)
(defsystem arrival
 :version "0.1"
 :author "Masataro Asai"
 :mailto "guicho2.71828@gmail.com"
 :license "LLGPL"
 :defsystem-depends-on ()
 :depends-on (:trivia
              :alexandria
              :iterate
              :log4cl
              :trivia.quasiquote)
 :components ((:module "src"
               :components ((:file "0-package")
                            (:file "1-fact-ordering")
                            (:file "1-flatten-types")
                            (:file "2-simulate")
                            (:file "3-main"))))
 :description "Classical planning plan validator written in modern Common Lisp"
 :in-order-to ((test-op (test-op :arrival.test))))
