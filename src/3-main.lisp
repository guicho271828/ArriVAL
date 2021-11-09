
(in-package :arrival)

(defun simulate-main (&rest argv)
  (declare (ignorable argv))
  (setf *terminal-io* *error-output*)
  (log:config :sane)
  (parse-arguments argv))

(defvar *allowed-conditions* nil)

(defun parse-arguments (argv)
  (ematch argv
    ((list* "--verbose" "0" rest)
     (parse-arguments rest))
    
    ((or (list* "-v" rest)
         (list* "--verbose" "1" rest))
     (setf *verbosity* 1)
     (parse-arguments rest))

    ((or (list* "-vv" rest)
         (list* "--verbose" "2" rest))
     (setf *verbosity* 2)
     (parse-arguments rest))

    ((or (list* "-vvv" rest)
         (list* "--verbose" "3" rest))
     (setf *verbosity* 3)
     (parse-arguments rest))

    ((list* (or "--relaxed" "-r") rest)
     (setf *relaxed-planning* t)
     (parse-arguments rest))

    ((list* (or "--no-type") rest)
     (setf *exclude-type-predicates-in-trace* t)
     (parse-arguments rest))

    ((list* (or "-d" "--Eno-domain-name") rest)
     (push 'domain-name-mismatch-error *allowed-conditions*)
     (parse-arguments rest))
    ((list* (or "-g" "--Eno-goal-condition") rest)
     (push 'goal-not-satisfied-error *allowed-conditions*)
     (parse-arguments rest))
    ((list* (or "-p" "--Eno-precondition") rest)
     (push 'precondition-not-satisfied-error *allowed-conditions*)
     (parse-arguments rest))
    
    ((list domain problem plan-output-file)
     (parse-argument2 domain problem plan-output-file *standard-output*))
    
    ((list domain problem plan-output-file trace-output-file)
     (with-open-file (s trace-output-file :direction :output :if-does-not-exist :create :if-exists :supersede)
       (parse-argument2 domain problem plan-output-file s)))
    (_
     (format *error-output* "Usage: [options] arrival domain problem planfile [trace-output]~%")
     (format *error-output* "     --no-type   : The trace output will not contain the type predicates~%")
     (format *error-output* "-v | --verbose N : Specify the verbosity, from 0 to 3                   ~%")
     (format *error-output* "-r | --relaxed   : Perform the relaxed planning instead                 ~%")
     (format *error-output* "-d | --Eno-domain-name    : do not report error with domain-name mismatch           ~%")
     (format *error-output* "-g | --Eno-goal-condition : do not report error when goals are not satisfied        ~%")
     (format *error-output* "-p | --Eno-precondition   : do not report error when preconditions are not satisfied~%")
     (format *error-output* "Got ARGV: ~a~%" argv)
     (format *error-output* "~{~30@a: ~a~%~}"
             (list #+sbcl "dynamic space size" #+sbcl (sb-ext:dynamic-space-size)
                   "lisp implementation type" (lisp-implementation-type)
                   "lisp implementation version" (lisp-implementation-version)
                   "machine instance" (machine-instance)
                   "machine type" (machine-type)
                   "machine version" (machine-version)
                   "software type" (software-type)
                   "software version" (software-version))))))

;; ignore certain errors
(defun parse-argument2 (domain problem plan-output-file trace-output)
  (handler-bind
      ((error (lambda (c)
                (format *error-output* "~a~%" c)
                (if (member (type-of c) *allowed-conditions*)
                    (continue c)))))
    (parse-argument3 domain problem plan-output-file trace-output)))

;; call simulate-plan-from-file
(defun parse-argument3 (domain problem plan-output-file trace-output)
  (simulate-plan-from-file
   domain problem plan-output-file
   (lambda ()
     (pprint-facts (facts) trace-output)
     (fresh-line trace-output)))
  (fresh-line trace-output))
