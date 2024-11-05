(defsystem "lisp-logic"
  :version "0.0.1"
  :author "Selwyn Simsek"
  :mailto "selwyn.simsek@cantab.net"
  :license "MIT"
  :depends-on ("sat-lisp"
               "bordeaux-threads"
               "cl-smt-lib"
               "array-operations")
  :components ((:module "src"
                :components
                ((:file "main"))))
  :description ""
  :in-order-to ((test-op (test-op "lisp-logic/tests"))))

(defsystem "lisp-logic/tests"
  :author "Selwyn Simsek"
  :license "MIT"
  :depends-on ("lisp-logic"
               "rove")
  :components ((:module "tests"
                :components
                ((:file "main"))))
  :description "Test system for lisp-logic"
  :perform (test-op (op c) (symbol-call :rove :run c)))
