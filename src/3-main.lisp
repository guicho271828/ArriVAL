
(in-package :arrival)

(defun simulate-main (&rest argv)
  (declare (ignorable argv))
  (setf *terminal-io* *error-output*)
  (log:config :sane)
  (parse-arguments argv))


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
    
    ((list _ _ _)
     (parse-arguments `(,@argv "/dev/stdout")))
    
    ((list domain problem plan-output-file trace-output-file)
     (with-open-file (s trace-output-file :direction :output :if-does-not-exist :create :if-exists :supersede)
       (simulate-plan-from-file
        domain problem plan-output-file
        (lambda ()
          (pprint-facts s)
          (fresh-line s)))
       (fresh-line s)))
    (_
     (format *error-output* "Usage: [--notype] [-v[v[v]] | --verbose N] [-r|--relaxed] arrival domain problem planfile [trace-output]~%")
     (format *error-output* "     --notype    : The trace output will not contain the type predicates~%")
     (format *error-output* "-v | --verbose N : Specify the verbosity, from 0 to 3                   ~%")
     (format *error-output* "-r | --relaxed   : Perform the relaxed planning instead                 ~%")
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
