
(in-package :arrival)

(named-readtables:in-readtable :fare-quasiquote)

(defvar *plan*)

(declaim ((integer 0 3) *verbosity*))
(defvar *verbosity* 0
  "
Value 0   No output
Value >=1 Reports the basic progress / steps that it is checking / action effects
Value >=2 Prints the predicates and the axioms being checked
Value 3   Prints the backtracking for proving axioms")
(declaim (boolean *relaxed-planning*))
(defvar *relaxed-planning* nil)
(declaim (boolean *exclude-type-predicates-in-trace*))
(defvar *exclude-type-predicates-in-trace* nil)

(defun simulate-plan-from-file (domain problem plan-input-file callback)
  "CALLBACK is a function with no argument, that is called after the initialization and after applying each action."
  (simulate1
   (let ((*package* (find-package :arrival.pddl)))
     (when (>= *verbosity* 1)
       (format *trace-output* "; loading ~a~%" domain))
     (with-open-file (s domain)
       (read s)))
   (let ((*package* (find-package :arrival.pddl)))
     (when (>= *verbosity* 1)
       (format *trace-output* "; loading ~a~%" problem))
     (with-open-file (s problem)
       (read s)))
   (let ((*package* (find-package :arrival.pddl)))
     (when (>= *verbosity* 1)
       (format *trace-output* "; loading ~a~%" plan-input-file))
     (iter (for action in-file plan-input-file)
           (collect action)))
   callback))

;; Note: it ignores the :requirement field.

(defun simulate1 (domain problem *plan* callback)
  (match* (domain problem)
    ((`(arrival.pddl::define (arrival.pddl::domain ,domain) ,@domain-body)
      `(arrival.pddl::define (arrival.pddl::problem ,_)
          (:domain ,domain2)
         ,@problem-body))
     (if (eq domain domain2)
         (when (>= *verbosity* 1)
           (format *trace-output* "; the domain and the problem matched~%"))
         (warn "the domain name in the problem file does not match the name in the domain file"))
     (simulate2 domain-body problem-body callback))
    ((`(arrival.pddl::define (arrival.pddl::domain ,domain) ,@domain-body)
       _)
     (error "malformed problem file input"))
    ((_
      `(arrival.pddl::define (arrival.pddl::problem ,_)
          (:domain ,domain2)
         ,@problem-body))
     (error "malformed domain file input"))))

(defun simulate2 (domain problem callback)
  (when (>= *verbosity* 1)
    (format *trace-output* "; Flattening the types~%"))
  (let (*types*
        *objects*
        (*predicates*      `((= ?o1 ?o2)))
        (*predicate-types* `((= object object)))
        *actions*
        *axioms*
        *init*
        *goal*)
    (grovel-types      domain)
    (grovel-constants  domain)
    (grovel-objects    problem)
    (grovel-predicates domain)
    (grovel-init       problem)
    (grovel-goal       problem)
    (grovel-actions    domain)
    (grovel-axioms     domain)
    (simulate3 callback)))

(defvar *next-action*)
(defvar *previous-action*)
(defvar *fact-table*)
(defvar *new-fact-table*)
(defvar *axiom-table*)

(defun simulate3 (callback)
  (initialize
   (lambda ()
     (iter (for *next-action* in *plan*)
           (for *previous-action* previous *next-action*)
           (for step from 1)
           (when (>= *verbosity* 1)
             (format *trace-output* ";;;; Step ~a~%" step))
           (funcall callback)
           (let ((*new-fact-table* (copy-hash-table *fact-table*)))
             (when (>= *verbosity* 1)
               (format *trace-output* "; Applying action ~a~%" *next-action*))
             (apply-action *next-action*)
             (setf *fact-table* *new-fact-table*)
             (clrhash *axiom-table*))
           (finally
            (when (>= *verbosity* 1)
              (format *trace-output* ";;;; Goal checking~%"))
            (let ((*previous-action* *next-action*)
                  (*next-action* nil))
              (funcall callback))))
     (when (>= *verbosity* 1)
       (format *trace-output* "; checking goal condition ~a~%" *goal*))
     (if (test *goal*)
         (when (>= *verbosity* 1)
           (format *trace-output* "; goal condition satisfied~%"))
         (warn "Goal not satisfied state:~%~a~%goal~%~a"
               (facts)
               *goal*)))))

(defmacro progv* (vars vals &body body)
  "progv + printing feature."
  (once-only (vars vals)
    `(progv ,vars ,vals
       (when (and (> *verbosity* 2) ,vars)
         (format *trace-output* "~a binding ~{~a~^ ~} -> ~{~a~^ ~}~%"
                 (make-string *hold-level* :initial-element #\;)
                 ,vars ,vals))
       ,@body)))

(defun initialize (next)
  (let ((*fact-table*     (make-hash-table :test 'equal))
        (*axiom-table*    (make-hash-table :test 'equal)))

    (iter (for f in *init*)
          (setf (gethash f *fact-table*) t))

    (let ((objs (mapcar #'car *objects*)))
      (progv objs objs          ;binds objects to itself
        (funcall next)))))

(defun %in-fresh-binding (fn)
  (iter (for s in-package :arrival.pddl)
        (when (and (variablep s)
                   (boundp s))
          (collect s into variables))
        (finally
         (return
           (progv variables variables
             (map nil #'makunbound variables)
             (funcall fn))))))

(defmacro in-fresh-binding (&body body)
  `(%in-fresh-binding (lambda () ,@body)))

(defun apply-action (action)
  "Checks the precondition and
applies an action of the form (name . args) to the current state."
  (ematch action
    ((list* name args)
     (when (>= *verbosity* 1)
       (format *trace-output* "; Finding action for ~a~%" name))
     (ematch (find name *actions* :key #'second)
       ((and action-def (plist :parameters params
                               :precondition pre :effect eff))
        (assert action-def nil
                "; definition for action ~a not found" name)
        (when (>= *verbosity* 1)
          (format *trace-output* "; definition found: ~a~%" action-def)
          (format *trace-output* "; checking precondition ~a~%" pre))
        (progv* params args
          (let ((*print-circle* nil))
            (assert (test pre) nil
                    "Precondition for action ~a unsatisfied.~2%~@{ ~a = ~a~2%~}"
                    (pprint-pddl-to-string action)
                    :parameters
                    (pprint-pddl-to-string params)
                    :args
                    (pprint-pddl-to-string args)
                    :precondition
                    (pprint-pddl-to-string pre)
                    :state
                    (with-output-to-string (s) (pprint-facts s))))
          (when (>= *verbosity* 1)
            (format *trace-output* "; Precondition ~a satisfied~%" pre))
          (effect eff)))))))

(defun evaluate (value)
  "Evaluate atoms, predicates and (object/numeric) fluents."
  (ematch value
    ((type symbol)
     ;; Parameters and objects: ?x, truck
     (symbol-value value))
    ((type atom)
     ;; Numbers, but additionally strings etc. to make planner usable as a lisp library
     value)
    ((list* name args)
     ;; Fluents; either object or numeric
     (gethash (list* name (mapcar #'evaluate args)) *fact-table*))))

(defvar *hold-level* 1)
(defun holds (condition result)
  "Utility for printing the predicate test"
  (when (> *verbosity* 2)
    (format *trace-output* "~a ~a -> ~a~%"
            (make-string *hold-level* :initial-element #\;)
            (ematch condition
              ((type symbol)
               ;; Parameters and objects: ?x, truck
               condition)
              ((type atom)
               ;; Numbers, but additionally strings etc. to make planner usable as a lisp library
               condition)
              ((list* name args)
               ;; Fluents; either object or numeric
               (list* name (mapcar #'evaluate args))))
            (if result '⊤ '⊥)))
  result)

(defun test (condition)
  "Test the condition in the current state. Returns true when the condition holds."
  (ematch condition
    (nil
     t)
    (`(and ,@conditions)
      (every #'test conditions))
    (`(or  ,@conditions)
      (some #'test conditions))
    (`(imply ,a ,b)
      (test `(or (not ,a) ,b)))
    (`(not ,a)
      (if *relaxed-planning*
          t
          (not (test a))))
    (`(forall () ,body)
      (test body))
    (`(forall (,arg ,@args) ,body)
      (assert (variablep arg))
      (every (lambda (o)
               (progv* (list arg) (list o)
                 (test `(forall ,args ,body))))
             (mapcar #'car *objects*)))
    (`(exists () ,body)
      (test body))
    (`(exists (,arg ,@args) ,body)
      (assert (variablep arg))
      (some (lambda (o)
              (progv* (list arg) (list o)
                (test `(exists ,args ,body))))
            (mapcar #'car *objects*)))
    (`(= ,@args)
      (assert (= 2 (length args)) nil "Equality predicate is binary")
      (let ((args (mapcar #'evaluate args)))
        (assert (subsetp args (mapcar #'car *objects*))
                nil "Objects ~a are not registered" (set-difference args (mapcar #'car *objects*)))
        (holds condition
               (equalp (first args) (second args)))))
    (`(,(and op (or '< '> '>= '<=)) ,@args)
      (assert (= 2 (length args)) nil "Inequality predicate ~a is binary" op)
      (let ((args (mapcar #'evaluate args)))
        (dolist (arg args)
          (assert (numberp arg) nil "~a in ~a is not a number" arg `(,op ,@args)))
        (holds condition
               (apply op args))))
    
    (`(,name ,@args)
      (let ((args (mapcar #'evaluate args)))
        (assert (member name *predicates* :key #'first)
                nil "~a is not a registered predicate" name)
        (assert (subsetp args (mapcar #'car *objects*))
                nil "Objects ~a are not registered" (set-difference args (mapcar #'car *objects*)))
        (holds condition
               (if-let ((axioms (remove-if-not (lambda-match (`(:derived (,(eq name) ,@_) ,_) t)) *axioms*)))
                 (multiple-value-bind (elem exist)
                     (gethash (list* name args) *axiom-table*)
                   (if exist
                       elem
                       (progn
                         (when (>= *verbosity* 2)
                           (format *trace-output* "; Proving axiom ~a~%" `(,name ,@args)))
                         (multiple-value-bind (result discard) (prove-axiom axioms name args)
                           (unless discard
                             ;; the result is not allowed to be stored when
                             ;; it is a result of tautology; it could be made true
                             ;; from other proof path
                             (setf (gethash (list* name args) *axiom-table*)
                                   result))))))
                 ;; normal fact
                 (evaluate (list* name args))))))))

(defvar *proof-stack* nil
  "A special variable holding the proof stack as a list of axioms.
Whenever a new axiom is about to be proved/evaluated, it looks up this variable
so that it avoids tautology/infinite loop.")

(defun prove-axiom (axioms name args)
  "Prove that the axiom with the given arguments hold in the current state.
This function is not responsible for caching the result."
  
  (when (find `(,name ,@args) *proof-stack* :test #'equal)
    (when (> *verbosity* 2)
      (format *trace-output* "~a Detected a tautology in ~a; Treated as false~%"
              (make-string *hold-level* :initial-element #\;)
              `(,name ,@args)))
    (return-from prove-axiom (values nil t)))
  
  (let ((*proof-stack*
         (cons `(,name ,@args)
               *proof-stack*)))
    (some (lambda (x) (prove-axiom1 x args)) axioms)))

(defun prove-axiom1 (axiom args)
  (ematch axiom
    (`(:derived (,_ ,@params) ,body)
      (in-fresh-binding
        (progv* params args
          (let ((unbound nil)
                (*hold-level* (1+ *hold-level*)))
            (tagbody
             :start
               ;; when there is any unbound parameter,
               ;; it restarts the evaluation
               (handler-case
                   (labels ((rec (args)
                              (match args
                                (nil
                                 (test body))
                                ((list* arg rest)
                                 (some (lambda (o)
                                         (prog2
                                             (when (> *verbosity* 2)
                                               (format *trace-output* "; binding ~a -> ~a~%" arg o))
                                             (progv* (list arg) (list o)
                                               (rec rest))
                                           (when (> *verbosity* 2)
                                             (format *trace-output* "; unbinding ~a~%" arg))))
                                       (mapcar #'car *objects*))))))
                     (return-from prove-axiom1
                       (rec unbound)))
                 (unbound-variable (c)
                   (let ((name (cell-error-name c)))
                     (if (variablep name)
                         (progn
                           (when (> *verbosity* 2)
                             (format *trace-output* "; found an unbound parameter ~a in ~a~%" name body))
                           (push name unbound)
                           (go :start))
                         (signal c))))))))))))

(defun effect (condition)
  "Applies the effect of the condition.
It respects the conditional effect"
  (ematch condition
    (nil
     nil)
    (`(and ,@conditions)
      (map nil #'effect conditions))
    (`(forall () ,body)
      (effect body))
    (`(forall (,arg ,@args) ,body)
      (assert (variablep arg))
      (map nil (lambda (o)
                 (progv* (list arg) (list o)
                   (effect `(forall ,args ,body))))
           (mapcar #'car *objects*)))
    (`(when ,condition ,body)
      (when (test condition)
        (effect body)))

    ;; fluents
    (`(assign ,place ,value)
      (setf (fluent place) (fluent value)))
    (`(increase ,place ,value)
      (incf (fluent place) (fluent value)))
    (`(decrease ,place ,value)
      (decf (fluent place) (fluent value)))
    (`(scale-up ,place ,value)
      (setf (fluent place)
            (* (fluent place) (fluent value))))
    (`(scale-down ,place ,value)
      (setf (fluent place)
            (/ (fluent place) (fluent value))))
    
    (`(not (,name ,@args))
      (let ((args (mapcar #'evaluate args)))
        (assert (member name *predicates* :key #'first)
                nil "~a is not a registered predicate" name)
        (assert (subsetp args (mapcar #'car *objects*))
                nil "Objects ~a are not registered" (set-difference args (mapcar #'car *objects*)))

        (assert (not (find name *axioms* :key (lambda-match (`(:derived (,name ,@_) ,_) name))))
                nil "~a is a derived predicate" name)

        (when *relaxed-planning*
          (when (>= *verbosity* 1)
            (format *trace-output* "; Deleting ~a (ignored)~%" `(,name ,@args)))
          (return-from effect))

        (when (>= *verbosity* 1)
          (format *trace-output* "; Deleting ~30a: ~a -> ~a~%" `(,name ,@args) (if (gethash (list* name args) *new-fact-table*) '⊤ '⊥) '⊥))
        (setf (gethash (list* name args) *new-fact-table*) nil)))

    (`(,name ,@args)
      (let ((args (mapcar #'evaluate args)))
        (assert (member name *predicates* :key #'first)
                nil "~a is not a registered predicate" name)
        (assert (subsetp args (mapcar #'car *objects*))
                nil "Objects ~a are not registered" (set-difference args (mapcar #'car *objects*)))

        (assert (not (find name *axioms* :key (lambda-match (`(:derived (,name ,@_) ,_) name))))
                nil "~a is a derived predicate" name)
        
        (when (>= *verbosity* 1)
          (format *trace-output* "; Adding   ~30a: ~a -> ~a~%" `(,name ,@args) (if (gethash (list* name args) *new-fact-table*) '⊤ '⊥) '⊤))
        (setf (gethash (list* name args) *new-fact-table*) t)))))

(defun facts ()
  "Returns a list of facts that hold in the current state.
Depending on the value of the *exclude-type-predicates-in-trace*,
it includes the type predicates (true by default)"
  (iter (for (key val) in-hashtable *fact-table*)
        (when (and val
                   (if *exclude-type-predicates-in-trace*
                       (ematch val
                         ((list* name _)
                          (let ((found (find name *types* :key #'car)))
                            (when found
                              (when (>= *verbosity* 1)
                                (format *trace-output* "; Ignoring type predicate ~a~%" val)))
                            (not found))))
                       t))
          (collect key))))

(defun pprint-pddl-to-string (thing)
  "Print THING to the string, inside the PDDL package."
  (with-output-to-string (s)
    (pprint-pddl thing s)))

(defun pprint-pddl (thing &optional (s *standard-output*))
  "Print THING to the stream, inside the PDDL package."
  (let ((*package* (find-package :arrival.pddl)))
    (prin1 thing s)))

(defun pprint-facts (&optional (s *standard-output*))
  "Print the list of facts to the stream, inside the PDDL package."
  (pprint-pddl (sort (facts) #'fact<) s))

