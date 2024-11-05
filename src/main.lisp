;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;; High level logic solver for Common Lisp.

(defpackage lisp-logic
  (:use :cl)
  (:shadowing-import-from #:metabang-bind #:bind)
  (:export *solver*
           variable-count
           phrase-count
           solve
           transpose
           solver
           check-sat
           reset-solver
           retrieve-model
           model-eval
           input-formula
           allocate-boolean
           allocate-vector
           allocate-matrix
           z3-solver
           sat-solver
           with-sat-solver))

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

(defmethod %allocate-boolean ((solver sat-solver))
  (incf (sat-lisp:variable-count solver)))

(defmethod %input-formula ((solver sat-solver) formula)
  "Should use Z3 to do the formula translation as a first step."
  (bind ((smt-formulae (lisp-logic->smt formula))
         (symbols (collect-symbols smt-formulae))
         (cl-smt-lib:*smt-debug* *debug-io*))
    ;; reset the solver
    (cl-smt-lib:write-to-smt *smt* '((|reset|)))
    ;; declare the variables
    (loop for symbol in symbols
          do (cl-smt-lib:write-to-smt *smt* `((|declare-fun| ,symbol () |Bool|))))
    ;; write the formulae
    (cl-smt-lib:write-to-smt *smt*)
    ;; read out the results
    ;; convert the results to cnf form and write them to the solver
    (smt->cnf solver)))

(defmethod lisp-logic->smt ((formula integer)) (z3-name formula))

(defmethod lisp-logic->smt ((formula vector))
  (lisp-logic->smt (aops:reshape formula '(t 1))))

(defmethod lisp-logic->smt (formula) formula)

(defmethod lisp-logic->smt ((cons cons))
  (lisp-logic-cons->smt (car cons) (cdr cons)))

(defmethod lisp-logic-cons->smt ((car (eql 'xor)) rest)
  `(|xor| ,@(mapcar #'lisp-logic->smt rest)))

(defmethod lisp-logic-cons->smt ((car (eql 'and)) rest)
  `(|and| ,@(mapcar #'lisp-logic->smt rest)))

(defmethod lisp-logic-cons->smt ((car (eql 'or)) rest)
  `(|or| ,@(mapcar #'lisp-logic->smt rest)))

(defmethod lisp-logic-cons->smt ((car (eql 'not)) rest)
  `(|not| ,(lisp-logic->smt rest)))

(defmethod lisp-logic-cons->smt ((car (eql 'transpose)) rest)
  (lisp-logic->smt (aops:permute '(1 0) (lisp-logic->smt (first rest)))))

(defmethod lisp-logic-cons->smt ((car (eql '=>)) rest)
  `(|or| (|not| ,(lisp-logic->smt (first rest)))
          ,(lisp-logic->smt (second rest))))

(defmethod lisp-logic-cons->smt ((car (eql '=)) rest)
  (when (zerop (length rest))
    (error "need at least one thing to be equal"))
  (etypecase (first rest)
    ((or integer cons) `(|=| ,@(mapcar #'lisp-logic->smt rest)))
    (array `(|and| ,@(coerce
                      (aops:flatten
                       (apply #'aops:each
                              (lambda (&rest elements)
                                `(|=| ,@(mapcar #'lisp-logic->smt elements)))
                              rest))
                      'list)))))

(defmethod lisp-logic-cons->smt ((car (eql '*)) rest)
  (reduce #'lisp-logic-multiply->smt
          (mapcar #'lisp-logic->smt rest)))

(defmethod lisp-logic-cons->smt ((car (eql '+)) rest)
  (when (zerop (length rest))
    (error "need at least one thing to be equal"))
  (etypecase (first rest)
    ((or integer cons) `(|xor| ,@(mapcar #'lisp-logic->smt rest)))
    (array (apply #'aops:each (lambda (&rest elements)
                                (lisp-logic->smt `(+ ,@elements)))
                  rest))))

(defmethod lisp-logic-multiply->smt ((a array) (b vector))
  "Assumes that b is a column vector."
  (lisp-logic-multiply->smt a (aops:reshape b '(t 1))))

(defmethod lisp-logic-multiply->smt ((a array) (b array))
  (bind (((m k1) (array-dimensions a))
         ((k n) (array-dimensions b))
         (result (make-array (list m n))))
    (assert (= k1 k))                   ; dimensions need to match up
    (loop for i from 0 below m do
      (loop for j from 0 below n do
        (setf (aref result i j)
              `(|xor| ,@(loop for s from 0 below k collect `(|and| ,(aref a i s) ,(aref b s j)))))))
    result))

(defmethod lisp-logic-multiply->smt (a b)
  ;assumes a and b are bits
  `(|and| ,(lisp-logic->smt a) ,(lisp-logic->smt b)))

(defmethod lisp-logic-cons->smt ((car (eql 'at-most)) rest)
  `((_ |at-most| ,(first rest)) ,@(rest rest)))

(defmethod lisp-logic-cons->smt ((car (eql 'at-least)) rest)
  `((_ |at-least| ,(first rest)) ,@(rest rest)))

(defmethod lisp-logic-cons->smt ((car (eql 'exactly)) rest)
  `(|and| ,(lisp-logic-cons->smt (cons 'at-most rest))
          ,(lisp-logic-cons->smt (cons 'at-least rest))))


(defmethod %model-eval ((solver sat-solver) (expression integer))
  (if (sat-lisp:literal-value solver expression) 1 0))

(defvar *smt-args* '("-v:10" "model_validate=true" "parallel.enable=true" "parallel.threads.max=100") "Additional arguments for Z3")

(defun make-smt (&optional (type :z3))
  "Returns a handle to an SMT solver. Z3 is the default as it exposes useful extensions."
  (let ((smt
          (ecase type
            (:z3 (apply #'cl-smt-lib:make-smt "z3" "-in" *smt-args*))
            ;; removing cvc5 as we use so many Z3 specific extensions now
            ;; (:cvc5 (smt:make-smt "cvc5" "--lang=smtlib2.6"))
            )))
                                        ;(smt:write-to-smt smt *smt-init-sexp*)
    smt))

(defvar *smt* (make-smt))
(defun smt->cnf (solver)
  "Serialises the current state of the SMT solver for use with a SAT solver."
  (cl-smt-lib:write-to-smt *smt* `((|apply|
                                    (|then| ; TODO look into these? are they all necessary?
                                     |simplify| ; is this the best combination?
                                     |solve-eqs|
                                     |card2bv|
                                     |pb2bv|
                                     |solve-eqs|
                                     |simplify|
                                     |tseitin-cnf|)))) ; use tactics to convert to CNF
  (bind (((_ (_ &rest content)) (cl-smt-lib:read-from-smt *smt*))
         (depth (nth (- (length content) 1) content))
         (precision (nth (- (length content) 3) content))
         (clauses (subseq content 0 (- (length content) 4))) ; 20 for testing purposes
         (variable-hash-table (make-hash-table :test 'eq))
         (number-of-variables 0))
    (loop for clause in clauses do
      (let ((symbol-bag (remove 'not (remove 'or (alexandria:flatten clause)))))
        (loop for symbol in symbol-bag do
          (unless (gethash symbol variable-hash-table)
                                        ; symbol not stored yet
            (incf number-of-variables)
            (setf (gethash symbol variable-hash-table)
                  number-of-variables))))) ;; TODO fix this, it will mess up the number of variables.
    (print clauses) ;; TODO Actually write the variables to the sat solver
    ;; (loop for clause in clauses do
    ;;   (cond
    ;;     ((symbolp clause)
    ;;      (sat-lisp:add-literal (gethash clause variable-hash-table))
    ;;      (sat-lisp:add-literal 0)
    ;;                                     ;(format stream "~a 0~%" (gethash clause variable-hash-table))
    ;;      )                              ; a unit assertion
    ;;     ((eq (car clause) 'not)
    ;;      (sat-lisp:add-literal (- (gethash (second clause) variable-hash-table)))
    ;;      (sat-lisp:add-literal 0))
    ;;                                     ; a unit negation
    ;;     ((eq (car clause) 'or)
    ;;      (map nil #'sat-lisp:add-literal
    ;;           (loop for subclause in (rest clause)
    ;;                 collect
    ;;                 (cond ((symbolp subclause)
    ;;                        (gethash subclause variable-hash-table))
    ;;                       ((eq 'not (car subclause))
    ;;                        (- (gethash (second subclause) variable-hash-table)))
    ;;                       (t (error "shouldnt be here")))))
    ;;      (sat-lisp:add-literal 0))
    ;;     (t (error "not understood"))))
    pathname))
