
(in-package :arrival)

(named-readtables:in-readtable :fare-quasiquote)

(defvar *types* nil "An alist of (type . supertype).")
(defvar *objects* nil "An alist of (name . type).")
(defvar *predicates* nil "A list of predicate type signatures (head arg-types*), e.g. ((next location location) ...) ")
(defvar *fluents*  nil "A list of fluent type signatures (head arg-types* result-type) , e.g. ((content envelope paper) ...).")
(defvar *actions* nil "A list of action definitions whose types are compiled away.")
(defvar *axioms*  nil "A list of axiom definitions whose types are compiled away.")
(defvar *init*  nil "Initial state augmented with the type predicates for the objects. ")
(defvar *goal*  nil "Goal condition, whose types are compiled away. (types appears in forall/exists)")

(defun variablep (variable)
  (ematch variable
    ((symbol :name (string* #\? _))
     t)
    ((symbol)
     nil)))

(defun parse-typed-def (list)
  "Parse a list of form [obj* - type]* .
 Returns an alist of (obj . type).
 Does not handle the type inheritance.
 Untyped parameters are given the type OBJECT.
 The order is preserved.
 It does not care what the obj is. It can be a list, too.

Example: (parse-typed-def '(airport1 - airport truck1 truck2 - truck banana))

->  ((airport1 . airport) (truck1 . truck) (truck2 . truck) (banana . object))

Example: (parse-typed-def '((deposit ?p - person) - number (content ?e - envelope) - paper))

->  (((deposit ?p - person) . number) ((content ?e - envelope) . paper))

"
  (let (db
        buffer)
    (labels ((add (s type)
               (push (cons s type) db))
             (rec (list)
               (match list
                 ((list* '- (list* 'either _) _)
                  (error "EITHER type not currently supported"))
                 
                 ((list* '- type rest)
                  (setf buffer (nreverse buffer))
                  (dolist (s buffer)
                    (add s type))
                  (setf buffer nil)
                  (rec rest))
                 
                 (nil
                  (setf buffer (nreverse buffer))
                  (dolist (s buffer)
                    (add s 'object))
                  (nreverse db))
                 
                 ((list* now rest)
                  (push now buffer)
                  (rec rest)))))
      (rec list))))

(defun grovel-types (domain)
  (match domain
    ((assoc :types typed-def)
     (let ((parsed (parse-typed-def typed-def)))
       (appendf *types* parsed)
       (iter (for (type . supertype) in parsed)
             (when (not (or (eq supertype 'object)
                            (assoc supertype *types*)))
               (warn "connecting an orphan supertype ~a to OBJECT" supertype)
               (push (cons supertype 'object) *types*)))
       (appendf *predicates*
                (iter (for (current . parent) in *types*)
                      (collecting
                       `(,current ,parent))))))))

(defun flatten-type (type)
  "Returns the list of all parent types (including itself and OBJECT),
 handling the infinite loop.
Signals an error when the type is not connected to the root OBJECT type."
  (let (acc)
    (labels ((rec (type)
               (unless (member type acc)
                 (push type acc)
                 (iter (for (current . parent) in *types*)
                       (with parent-found = nil)
                       (when (eq current type)
                         (setf parent-found t)
                         (rec parent))))))
      (rec type)
      acc)))

(defun flatten-types/argument (arg type)
  "Returns a list of type predicates for each parent type of TYPE,
 with ARG as the argument. The result does not contain the OBJECT type.

Example: (flatten-types/argument '?x 'airport) -> ((airport ?x) (location ?x))
"
  (iter (for parent in (flatten-type type))
        (unless (eq parent 'object)
          (collecting `(,parent ,arg)))))

(defun flatten-types/predicate (predicate &optional include-parent-types)
  "PREDICATE is a predicate form (name args...).
Look up the *predicates* and returns a list that contains itself
and the type predicates implied by its arguments.
By default, the implied type predicates contain only those for the most specific types,
minus the obvious OBJECT type.

Example: (flatten-types/predicate '(next ?x ?y)) -> ((next ?x ?y) (location ?x) (location ?y))

When the optional argument INCLUDE-PARENT-TYPES is true, the list also contains all the type predicates
up in the type hierarchy, minus the OBJECT type."
  (ematch predicate
    ((list* name args)
     (list* predicate
            (if include-parent-types
                (mappend #'flatten-types/argument
                         args
                         (cdr (or (assoc name *predicates*)
                                  (error "Predicate for ~a is missing!" name))))
                (remove 'object
                        (mapcar #'list 
                                (cdr (or (assoc name *predicates*)
                                         (error "Predicate for ~a is missing!" name)))
                                args)
                        :key #'first))))))

(defun flatten-typed-def (typed-def)
  "Takes a typed-def L and returns three values:
1. the untyped version of L
2. a list of literals converted from the types of the parameters, including the parent types
3. alist of (arg . type)

 Example: (?x - table) -> (?x), ((table ?x)), ((?x . table)) "
  (let* ((parsed (parse-typed-def typed-def))
         (w/o-type (mapcar #'car parsed))
         (type-conditions
          (iter (for (arg . type) in parsed)
                (unless (eq type 'object)
                  (collecting `(,type ,arg))))))
    (values w/o-type type-conditions parsed)))

(defun flatten-types/condition (condition)
  (ematch condition
    (nil
     `(and))
    ((list 'exists params condition)
     (multiple-value-bind (w/o-type type-conditions) (flatten-typed-def params)
       `(exists ,w/o-type
               (and ,@type-conditions
                    ,(flatten-types/condition condition)))))
    ((list 'forall params condition)
     (multiple-value-bind (w/o-type type-conditions) (flatten-typed-def params)
       `(forall ,w/o-type
                (imply (and ,@type-conditions)
                       ,(flatten-types/condition condition)))))
    ((list* (and kind (or 'and 'or 'not 'imply))
            conditions)
     `(,kind ,@(mapcar #'flatten-types/condition conditions)))
    (_
     `(and ,@(flatten-types/predicate condition)))))

(defun flatten-types/effect (effect)
  (ematch effect
    (nil
     `(and))
    ((list* (and kind (or 'or 'exists)) _)
     (error "~a should not appear in the effects: ~a" kind effect))
    (`(forall ,params ,effect)
     (multiple-value-bind (w/o-type type-conditions) (flatten-typed-def params)
       `(forall ,w/o-type
                (when (and ,@type-conditions)
                  ,(flatten-types/effect effect)))))
    (`(when ,condition ,body)
      `(when ,(flatten-types/condition condition)
         ,(flatten-types/effect body)))
    (`(and ,@conditions)
      `(and ,@(mapcar #'flatten-types/effect conditions)))
    (`(increase ,@_)
      (log:trace "skipping ~a" effect)
      `(and))
    (_ effect)))

(defun grovel-constants (domain)
  (match domain
    ((assoc :constants typed-def)
     (let ((parsed (parse-typed-def typed-def)))
       (appendf *objects* parsed)
       (dolist (pair parsed)
         (match pair
           ((cons o type)
            (appendf *init* (flatten-types/argument o type)))))))))

(defun grovel-objects (problem)
  ;; almost the same as grovel-constants
  (match problem
    ((assoc :objects typed-def)
     (let ((parsed (parse-typed-def typed-def)))
       (appendf *objects* parsed)
       (dolist (pair parsed)
         (match pair
           ((cons o type)
            (appendf *init* (flatten-types/argument o type)))))))))

(defun grovel-predicates (domain)
  (match domain
    ((assoc :predicates predicates)
     (dolist (predicate predicates)
       (match predicate
         (`(,name ,@typed-def)
           (let ((arguments (parse-typed-def typed-def)))
             (push `(,name ,@(mapcar #'cdr arguments)) *predicates*))))))))

(defun grovel-fluents (domain)
  (match domain
    ((assoc :functions typed-def)
     (dolist (fluent (parse-typed-def typed-def))
       (match fluent
         ((cons `(,name ,@typed-def) value-type)
          (let ((arguments (parse-typed-def typed-def)))
            ;; the last type is the value type.
            ;; this is because (head args...) -> obj is equivalent to (head args... obj) -> t.
            (push `(,name ,@(mapcar #'cdr arguments) ,value-type) *fluents*))))))))

(defun grovel-init (problem)
  (ematch problem
    ((assoc :init predicates)
     (appendf *init*
              (iter (for condition in predicates)
                    (ematch condition
                      ((list* 'not _)
                       (log:trace "skipping ~a -- closed world assumption" condition))
                      (_
                       (appending (flatten-types/predicate condition t))))))
     (setf *init* (remove-duplicates *init* :test 'equal)))))

(defun grovel-goal (problem)
  (ematch problem
    ((assoc :goal (list condition))
     ;; goal may contain forall etc. so it needs flattening
     (setf *goal* (flatten-types/condition condition)))))

(defun grovel-actions (domain)
  (dolist (it domain)
    (match it
      ((list* :action name
              (plist :parameters params
                     :precondition pre :effect eff))
       (multiple-value-bind (w/o-type type-conditions) (flatten-typed-def params)
         (push (unify-duplicates
                w/o-type
                (lambda (newparams unifiers)
                  `(:action ,name
                            :parameters ,newparams
                            :precondition
                            (and ,@type-conditions
                                 ,@unifiers
                                 ,(flatten-types/condition pre))
                            :effect ,(flatten-types/effect eff))))
               *actions*)))
      #+(or)
      ((list* something _)
       (log:info "ignoring (~s ...)" something)))))

(defun grovel-axioms (domain)
  (dolist (it domain)
    (match it
       ((list (or :derived :axiom) (list* predicate params) condition)
        (multiple-value-bind (w/o-type type-conditions) (flatten-typed-def params)
          (push (unify-duplicates
                 w/o-type
                 (lambda (newparams unifiers)
                   `(:derived (,predicate ,@newparams)
                              (and ,@type-conditions
                                   ,@unifiers
                                   ,(flatten-types/condition condition)))))
                *axioms*)))
       #+(or)
       ((list* something _)
        (log:info "ignoring (~s ...)" something)))))

(defun new-variable ()
  "Interns a new symbol in ARRIVAL.PDDL"
  ;; The use of gentemp instead of gensym is intentional; Since the file was already read,
  ;; it is safe to use gentemp
  (gentemp "?" :arrival.pddl))

(defun unify-duplicates (variables fn)
  "If there are any duplicates in VARIABLES,
the second or later appearances are replaced with a new symbol.
FN is called with two arguments; The new, unique variable list
and a list of equality constraints.
"
  (match variables
    (nil
     (funcall fn nil nil))
    
    ((list* v rest)
     (if (find v rest)
         (let ((new (new-variable)))
           (warn "Found a duplicated parameter ~a, translated as equality constraints" v)
           (unify-duplicates
            (substitute new v rest)
            (lambda (newparams unifiers)
              (funcall fn
                       (cons v newparams)
                       (cons `(= ,v ,new) unifiers)))))
         (unify-duplicates
          rest
          (lambda (newparams unifiers)
            (funcall fn
                     (cons v newparams)
                     unifiers)))))))

#+(or)
(unify-duplicates '(?a ?c ?b ?a) (lambda (params unifiers) (print params) (print unifiers)))

;; ->
;; (?A ?C ?B ARRIVAL.PDDL::?12) 
;; ((= ?A ARRIVAL.PDDL::?12)) 
