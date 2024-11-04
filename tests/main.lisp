(defpackage lisp-logic/tests/main
  (:use :cl
        :lisp-logic
        :rove))
(in-package :lisp-logic/tests/main)

;; NOTE: To run this test file, execute `(asdf:test-system :lisp-logic)' in your Lisp.

(deftest test-target-1
  (testing "should (= 1 1) to be true"
    (ok (= 1 1))))
