#|
  This file is a part of arrival project.
  Copyright (c) 2019 Masataro Asai (guicho2.71828@gmail.com)
|#

(in-package :cl-user)

(defpackage arrival.pddl
  (:import-from :cl :and :or :not :when :-
                := :> :< :>= :<= :/ :* :+
                :nil)
  (:export :define
           :domain
           :problem
           
           :increase
           :decrease
           :assign
           :scale-up
           :scale-down
           
           :total-cost
           :minimize
           :maximize
           
           :object
           :?o :?o1 :?o2
           :exists
           :forall
           :imply
           :either

           ;; temporal stuff
           :at
           :over
           :start
           :end
           :all
           :always
           :sometime
           :within
           :at-most-once
           :sometime-after
           :sometime-before
           :always-within
           :hold-during
           :hold-after

           :total-time

           :is-violated
           )
  (:documentation "The package for loading the symbols in the input"))

(defpackage arrival
  (:shadowing-import-from :arrival.pddl :maximize :minimize :always)
  (:use :cl :iterate :alexandria :trivia :arrival.pddl))


