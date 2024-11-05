;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;; High level logic solver for Common Lisp.

(defpackage lisp-logic
  (:use :cl)
  (:export *solver*))

(in-package :lisp-logic)

;;; API (aim to interact with the solver only through this)

(defclass solver () ()
  (:documentation "A general superclass for a logic solver e.g. an SMT solver or an iterative SAT solver."))

(defun variable-count (&key (solver *solver*)) (%variable-count solver))
(defgeneric %variable-count (solver)
  (:documentation "Returns the current number of variables stored in the state of the solver.
                   This may include variables created by the solver itself."))

(defun phrase-count (&key (solver *solver*)) (%phrase-count solver))
(defgeneric %phrase-count (solver)
  (:documentation "Returns the current number of variables stored in the state of the solver.
                   This may include variables created by the solver itself."))

(defun solve (&key (solver *solver*)) (%solve solver))
(defgeneric %solve (solver)
  (:documentation "Tries to obtain a satisfying solution and returns the state. One of :input, :sat or :unsat."))

(defun check-sat (&key (solver *solver*))
  "Returns non-NIL if and only if the problem is satisfied."
  (eq :sat (solve solver)))

(defun reset-solver (&key (solver *solver*)) (%reset-solver solver))
(defgeneric %reset-solver (solver)
  (:documentation "Resets the solver to having no variables or clauses."))

(defun retrieve-model (&key (solver *solver*)) (%retrieve-model solver))
(defgeneric %retrieve-model (solver)
  (:documentation "Returns the model from `solver' - provided that it exists. Usually a bit-vector."))

(defun model-eval (expression &key (solver *solver*)) (%model-eval solver expression))
(defgeneric %model-eval (solver expression)
  (:documentation "Evaluates the given expression in the context of the model of `solver' - provided that it exists."))

(defun input-formula (formula &key (solver *solver*)) (%input-formula solver formula))
(defgeneric %input-formula (solver formula)
  (:documentation "Adds the given formula to `solver'. Formulae are in an sexp-based language similar to SMT-LIB."))

(defun allocate-boolean (&key (solver *solver*)) (%allocate-boolean solver))
(defgeneric %allocate-boolean (solver)
  (:documentation "Allocates a boolean in solver and returns its name (a positive integer)."))

(defun allocate-vector (n &key (solver *solver*)) (%allocate-vector solver n))
(defmethod %allocate-vector (solver (n integer))
  (coerce (loop repeat n collect (allocate-boolean solver)) 'vector))

(defun allocate-matrix (m n &key (solver *solver*)) (%allocate-matrix solver m n))
(defmethod %allocate-matrix (solver (m integer) (n integer))
  (make-array (list m n) :initial-contents
              (loop repeat m collect
                             (loop repeat n collect (allocate-boolean solver)))))
;;; General implementation

(defmethod %model-eval (solver (expression list))
  (mapcar (lambda (x) (model-eval solver x)) solver))

(defmethod %model-eval (solver (expression array))
  (aops:each (lambda (x) (model-eval solver x)) array))

;;; Z3 implementation

(defclass z3-solver (solver) ()
  (:documentation "An implementation of lisp-logic that uses Z3."))


(defstruct z3-symbol (name "" :type string)) ; to avoid interning

(defmethod print-object ((symbol z3-symbol) stream)
  (princ (z3-symbol-name symbol) stream))

;; TODO fix this
(defun z3-name (index) (make-z3-symbol :name (format nil "var-~a" index)))

;;; TODO SAT implementation
;;; Use Z3 to translate clauses on demand - no global optimisation
;;; can you add global optimisation later on? probably
;;; keep it simple for now

(defclass sat-solver (solver sat-lisp:incremental-sat-solver)
  ((phrase-count :initarg :phrase-count :accessor phrase-count :initform 0))
  (:documentation "An implementation of lisp-logic that uses an incremental sat solver via sat-lisp."))

(defvar *solver* (make-instance 'sat-solver))

(defmethod initialize-instance :after ((instance sat-solver) &rest initargs)
  (declare (ignore initargs))
  (sat-lisp:init-solver instance))

(defmacro with-sat-solver (&body body)
  `(let ((*solver* (make-instance 'sat-solver)))
     (unwind-protect (progn ,@body)
       (sat-lisp:release-solver *solver*))))

;;; API implementation

(defmethod %variable-count ((solver sat-solver))
  (sat-lisp:variable-count solver))

(defmethod %phrase-count ((solver sat-solver))
  (loop for x across (sat-lisp:added-literals solver) counting (zerop x)))

(defmethod %solve ((solver sat-solver)) (sat-lisp:solve solver))

(defmethod %reset-solver ((solver sat-solver))
  (sat-lisp:release-solver solver)
  (sat-lisp:init-solver solver))

(defmethod %retrieve-model ((solver sat-solver)) (sat-lisp:model solver))

(defmethod %input-formula ((solver sat-solver) formula)
  "Should use Z3 to do the formula translation as a first step."
  (error "implement me"))

(defmethod %allocate-boolean ((solver sat-solver))
  (incf (sat-lisp:variable-count solver)))

(defmethod %model-eval ((solver sat-solver) (expression integer))
  (if (sat-lisp:literal-value solver expression) 1 0))
