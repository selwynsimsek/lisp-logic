;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;; High level logic solver for Common Lisp.

(defpackage lisp-logic
  (:use :cl))
(in-package :lisp-logic)

;;; API (aim to interact with the solver only through this)

(defclass logic-solver () ()
  (:documentation "A general superclass for a logic solver e.g. an SMT solver or an iterative SAT solver."))

(defgeneric variable-count (solver)
  (:documentation "Returns the current number of variables stored in the state of the solver.
                   This may include variables created by the solver itself."))

(defgeneric phrase-count (solver)
  (:documentation "Returns the current number of variables stored in the state of the solver.
                   This may include variables created by the solver itself."))

(defgeneric solve (solver)
  (:documentation "Tries to obtain a satisfying solution and returns the state. One of :input, :sat or :unsat."))

(defun check-sat (solver)
  "Returns non-NIL if and only if the problem is satisfied."
  (eq :sat (solve solver)))

(defgeneric reset-solver (solver)
  (:documentation "Resets the solver to having no variables or clauses."))

(defgeneric retrieve-model (solver)
  (:documentation "Returns the model from `solver' - provided that it exists. Usually a bit-vector."))

(defgeneric model-eval (solver expression)
  (:documentation "Evaluates the given expression in the context of the model of `solver' - provided that it exists."))

(defgeneric input-formula (solver formula)
  (:documentation "Adds the given formula to `solver'. Formulae are in an sexp-based language similar to SMT-LIB."))

(defgeneric allocate-boolean (solver)
  (:documentation "Allocates a boolean in solver and returns its name (a positive integer)."))

(defmethod allocate-vector (solver (n integer))
  (coerce (loop repeat n collect (allocate-boolean solver)) 'vector))

(defmethod allocate-matrix (solver (m integer) (n integer))
  (make-array (list m n) :initial-contents
              (loop repeat m collect
                             (loop repeat n collect (allocate-boolean solver)))))
;;; General implementation

(defmethod model-eval (solver (expression list))
  (mapcar (lambda (x) (model-eval solver x)) solver))

(defmethod model-eval (solver (expression array))
  (aops:each (lambda (x) (model-eval solver x)) array))

;;; Z3 implementation

;;; SAT implementation
