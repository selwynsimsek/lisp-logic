;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;; High level logic solver for Common Lisp.

(defpackage com.selwynsimsek.lisp-logic
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
           with-reset-solver
           z3-solver
           sat-solver
           with-sat-solver))

(in-package :com.selwynsimsek.lisp-logic)

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
  (eq :sat (solve :solver solver)))

(defun reset-solver (&key (solver *solver*)) (%reset-solver solver))
(defgeneric %reset-solver (solver)
  (:documentation "Resets the solver to having no variables or clauses."))

(defun model (&key (solver *solver*)) (%model solver))

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
  (coerce (loop repeat n collect (allocate-boolean :solver solver)) 'vector))

(defun allocate-matrix (m n &key (solver *solver*)) (%allocate-matrix solver m n))
(defmethod %allocate-matrix (solver (m integer) (n integer))
  (make-array (list m n) :initial-contents
              (loop repeat m collect
                             (loop repeat n collect (allocate-boolean :solver solver)))))
;;; General implementation

(defmethod %model-eval (solver (expression array))
  (aops:each (lambda (x) (model-eval x :solver solver)) expression))

;;; Z3 implementation

(defclass z3-solver (solver) ()
  (:documentation "An implementation of lisp-logic that uses Z3."))


(defstruct z3-symbol (name "" :type string) (index 0 :type integer)) ; to avoid interning

(defmethod print-object ((symbol z3-symbol) stream)
  (princ (z3-symbol-name symbol) stream))

;; TODO fix this
(defun z3-name (index) (make-z3-symbol :name (format nil "var-~a" index) :index index))

(defun z3-symbol-equal-p (z1 z2) (string= (z3-symbol-name z1) (z3-symbol-name z2)))

;;; TODO SAT implementation
;;; Use Z3 to translate clauses on demand - no global optimisation
;;; can you add global optimisation later on? probably
;;; keep it simple for now

(defclass cached-formula-solver ()
  ((cached-formulae :initarg :cached-formulae :accessor cached-formulae :initform nil))
  (:documentation "A solver that caches its formulae."))

(defclass sat-solver (solver sat-lisp:incremental-sat-solver cached-formula-solver)
  ()
  (:documentation "An implementation of lisp-logic that uses an incremental sat solver via sat-lisp."))


(defvar *solver* (make-instance 'sat-solver))

(defmethod initialize-instance :after ((solver sat-solver) &rest initargs)
  (declare (ignore initargs))
  (init-solver solver))

(defmethod %solve :around (solver)
  (format *debug-io* "Calling solver ~a with ~a variables and ~a phrases...~%"
          (sat-lisp:ipasir-signature)
          (variable-count :solver solver)
          (phrase-count :solver solver))
  (time (call-next-method)))

(defmethod init-solver ((solver sat-solver))
  (sat-lisp:init-solver solver)
  ;; Reserve the literal '1' to be true
  (sat-lisp:add-literal (allocate-boolean :solver solver) :solver solver)
  (sat-lisp:add-literal 0 :solver solver))

(defmacro with-sat-solver (&body body)
  `(let ((*solver* (make-instance 'sat-solver)))
     (unwind-protect (progn ,@body)
       (sat-lisp:release-solver *solver*))))

;;; API implementation

(defmethod %variable-count ((solver sat-solver))
  (sat-lisp:variable-count solver))

(defmethod %phrase-count ((solver cached-formula-solver))
 ; (loop for x across (sat-lisp:added-literals solver) counting (zerop x))
  (length (cached-formulae solver)))

(defmethod %solve :before ((solver sat-solver))
  (add-formulae solver))

(defmethod %solve ((solver sat-solver))
  (sat-lisp:solve solver))

(defmethod %reset-solver ((solver sat-solver))
  (sat-lisp:release-solver solver)
  (init-solver solver))

(defmethod %reset-solver :after ((solver cached-formula-solver))
  (setf (cached-formulae solver) nil))

(defmethod %model ((solver sat-solver)) (sat-lisp:model solver))

(defmethod %allocate-boolean ((solver sat-solver))
  (incf (sat-lisp:variable-count solver)))

(defmethod %input-formula ((solver cached-formula-solver) formula)
  (push formula (cached-formulae solver)))

(defmethod add-formulae ((solver sat-solver))
  "Should use Z3 to do the formula translation as a first step."
 ; (format t "~a~%" (cached-formulae solver))
  (bind ((cl-smt-lib:*smt-debug* nil)
         (symbols (remove-duplicates
                   (remove-if-not (lambda (s) (z3-symbol-p s))
                                  (alexandria:flatten
                                   (mapcar #'lisp-logic->smt
                                           (cached-formulae solver))))
                   :test #'z3-symbol-equal-p)))
    ;; declare the variables
    (loop for symbol in symbols
          do (cl-smt-lib:write-to-smt *smt* `((|declare-fun| ,symbol () |Bool|))))
    (loop for formula in (cached-formulae solver) do
      (bind ((smt-formulae (lisp-logic->smt formula))
             )
        ;; reset the solver
                                        ; (cl-smt-lib:write-to-smt *smt* '((|reset|)))
        ;; write the formulae
        (cl-smt-lib:write-to-smt *smt* `((|assert| ,smt-formulae))))))
  (smt->cnf solver))
    ;; read out the results
    ;; convert the results to cnf form and write them to the solver))

(defmacro with-reset-solver (&rest body)
  `(unwind-protect (progn ,@body)
     (reset-smt-process)
     (reset-solver)))

(defmethod lisp-logic->smt ((formula integer))
  (alexandria:switch (formula :test #'=)
    (0 '|false|)
    (1 '|true|)
    (t (z3-name formula))))

(defmethod lisp-logic->smt ((formula vector))
  (lisp-logic->smt (aops:reshape formula '(t 1))))

(defmethod lisp-logic->smt (formula) formula)

(defmethod lisp-logic->smt ((cons cons))
  (lisp-logic-cons->smt (car cons) (cdr cons)))

(defmethod lisp-logic-cons->smt ((car (eql '|xor|)) rest)
  "expression is already parsed"
  (cons car rest))
(defmethod lisp-logic-cons->smt ((car (eql '|and|)) rest)
  "expression is already parsed"
  (cons car rest))
(defmethod lisp-logic-cons->smt ((car (eql '|or|)) rest)
  "expression is already parsed"
  (cons car rest))
(defmethod lisp-logic-cons->smt ((car (eql '|not|)) rest)
  "expression is already parsed"
  (cons car rest))

(defmethod lisp-logic-cons->smt ((car (eql 'xor)) rest)
  `(|xor| ,@(mapcar #'lisp-logic->smt rest)))

(defmethod lisp-logic-cons->smt ((car (eql 'and)) rest)
  `(|and| ,@(mapcar #'lisp-logic->smt rest)))

(defmethod lisp-logic-cons->smt ((car (eql 'or)) rest)
  `(|or| ,@(mapcar #'lisp-logic->smt rest)))

(defmethod lisp-logic-cons->smt ((car (eql 'not)) rest)
  `(|not| ,@(mapcar #'lisp-logic->smt rest)))

(defmethod lisp-logic-cons->smt ((car (eql 'transpose)) rest)
  (lisp-logic->smt (aops:permute '(1 0) (lisp-logic->smt (first rest)))))

(defmethod lisp-logic-cons->smt ((car (eql '=>)) rest)
  `(|or| (|not| ,(lisp-logic->smt (first rest)))
          ,(lisp-logic->smt (second rest))))

(defmethod lisp-logic-cons->smt ((car (eql '=)) rest)
  (when (zerop (length rest))
    (error "need at least one thing to be equal"))
  (etypecase (first rest)
    ((or integer cons) (lisp-logic->smt `(|=| ,@(mapcar #'lisp-logic->smt rest))))
    ((or symbol z3-symbol) `(|=| ,@(mapcar #'lisp-logic->smt rest)))
    (array `(|and| ,@(coerce
                      (aops:flatten
                       (apply #'aops:each
                              (lambda (&rest elements)
                                `(|=| ,@(mapcar #'lisp-logic->smt elements)))
                              (mapcar #'lisp-logic->smt rest)))
                      'list)))))

(defmethod lisp-logic-cons->smt ((car (eql '*)) rest)
  (reduce #'lisp-logic-multiply->smt (mapcar #'lisp-logic->smt rest)))

(defmethod lisp-logic-cons->smt ((car (eql '+)) rest)
  (when (zerop (length rest))
    (error "need at least one thing to be equal"))
  (etypecase (first rest)
    ((or integer cons) `(|xor| ,@(mapcar #'lisp-logic->smt rest)))
    (array (apply #'aops:each (lambda (&rest elements)
                                (lisp-logic->smt `(+ ,@elements)))
                  (mapcar #'lisp-logic->smt rest)))))

;(trace lisp-logic->smt lisp-logic-cons->smt lisp-logic-multiply->smt)

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
              `(|xor| ,@(loop for s from 0 below k collect
                              `(|and| ,(lisp-logic->smt (aref a i s))
                                      ,(lisp-logic->smt (aref b s j))))))))
    result))

(defmethod lisp-logic-multiply->smt (a b)
  ;assumes a and b are bits
  `(|and| ,(lisp-logic->smt a) ,(lisp-logic->smt b)))

(defmethod lisp-logic-cons->smt ((car (eql 'at-most)) rest)
  `((_ |at-most| ,(first rest)) ,@(mapcar #'lisp-logic->smt (rest rest))))

(defmethod lisp-logic-cons->smt ((car (eql 'at-least)) rest)
  `((_ |at-least| ,(first rest)) ,@(mapcar #'lisp-logic->smt (rest rest))))

(defmethod lisp-logic-cons->smt ((car (eql 'exactly)) rest)
  `(|and| ,(lisp-logic->smt (cons 'at-most rest))
          ,(lisp-logic->smt (cons 'at-least rest))))


(defmethod %model-eval ((solver sat-solver) (expression integer))
  (if (sat-lisp:literal-value solver expression) 1 0))

(setf *smt-args* '("model_validate=true" "parallel.enable=true" "parallel.threads.max=100"))

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
                                    (|then|
                                     |simplify|
                                     |card2bv|
                                     |tseitin-cnf|)))) ; use tactics to convert to CNF
  (bind (((_ (_ &rest content)) (cl-smt-lib:read-from-smt *smt*))
         (depth (nth (- (length content) 1) content))
         (precision (nth (- (length content) 3) content))
         (sat-lisp:*sat-solver* solver)
         (clauses (subseq content 0 (- (length content) 4))) ; 20 for testing purposes
         (variable-hash-table (make-hash-table :test 'eq)))
    (loop for clause in clauses do
      (let ((symbol-bag (remove 'not (remove 'or (alexandria:flatten clause)))))
        (loop for symbol in symbol-bag do
          (unless (gethash symbol variable-hash-table)
                                        ; symbol not stored yet
            (setf (gethash symbol variable-hash-table)
                  (if (str:starts-with? "VAR-" (symbol-name symbol))
                      (parse-integer (subseq (symbol-name symbol) 4))
                      (allocate-boolean :solver solver)))))))
    ;(print clauses) ;; TODO Actually write the variables to the sat solver
    ;(print (alexandria:hash-table-alist variable-hash-table))
    (loop for clause in clauses do
      (cond
        ((symbolp clause)
         (sat-lisp:add-literal (gethash clause variable-hash-table))
         (sat-lisp:add-literal 0)
                                        ;(format stream "~a 0~%" (gethash clause variable-hash-table))
         )                              ; a unit assertion
        ((eq (car clause) 'not)
         (sat-lisp:add-literal (- (gethash (second clause) variable-hash-table)))
         (sat-lisp:add-literal 0))
                                        ; a unit negation
        ((eq (car clause) 'or)
         (map nil #'sat-lisp:add-literal
              (loop for subclause in (rest clause)
                    collect
                    (cond ((symbolp subclause)
                           (gethash subclause variable-hash-table))
                          ((eq 'not (car subclause))
                           (- (gethash (second subclause) variable-hash-table)))
                          (t (error "shouldnt be here")))))
         (sat-lisp:add-literal 0))
        (t (error "not understood"))))
   ; pathname
    ))


(defun close-smt (smt)
  ;; Close the input and output streams first
  (close (cl-smt-lib::input smt))
  (close (cl-smt-lib::output smt))
                                        ; (bt:destroy-thread (cl-smt-lib/process-two-way-stream::thread smt))
  (uiop:terminate-process (cl-smt-lib::process smt))
  ;; Make sure it's dead
                                        ; (uiop:run-program (format nil "kill ~a" (smt-pid smt)) :ignore-error-status t)
  ;;  If the process is still alive, user needs to be alerted
  (sleep 1)
  (when (uiop:process-alive-p (cl-smt-lib::process smt))
    (error "SMT process still alive somehow")))
(defun reset-smt-process ()
  "Resets the SMT process. This should not normally be called, unless, say, the Z3 process has been
   killed manually."
                                        ; (ignore-errors (close-smt *smt*))
  (close-smt *smt*)
  (setf *smt* (make-smt)))
