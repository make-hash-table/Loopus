(in-package #:loopus.ir)

(defun ir-isl-optimize (ir)
  "Returns a copy of IR where it's reordered by isl"
  (let ((*set-domain* (isl:union-set-empty *space-domain*))
        (*map-read* (isl:union-map-empty *space-map-domain-range*))
        (*map-write* (isl:union-map-empty *space-map-domain-range*))
        (*map-schedule* (isl:union-map-empty *space-map-schedule*)))
    ;; Special parameters - inputs
    (setf *construct-to-identifier* (make-hash-table))
    (setf position-next-free-variable (- *size-domain* 2))
    ;;-1 because 1 slot is for the global counter
    ;;-1 because we use the value returned by inc
    (setf *counter-range* 0)
    (setf *all-irnodes* (make-hash-table))
    (setf *loop-variables* '())
    (setf *loop-bounds* '())
    (setf *counter-domain* 0)
    (setf *id-to-expression* (make-hash-table))
    (setf *depth-node* (make-hash-table))
    (setf *current-depth* 0)
    ;; End of setf special parameters
    (map-block-inner-nodes #'update-node ir)
    (print "Domain, read, write, and schedule:")
    (print *set-domain*)
    (print *map-read*)
    (print *map-write*)
    (print *map-schedule*)
    ;; Special parameters - outputs
    (setf node nil)
    (setf *ir-value-copies* (make-hash-table))
    (setf *values* '())
    (setf *depth-loop-variables* '())
    (setf *current-depth* 0)
    (setf *position-to-loopusvariable* (make-hash-table))
    (maphash (lambda (key value) (setf (gethash (- value (1- *size-domain*)) *position-to-loopusvariable*) key)) *construct-to-identifier*)
    ;; End of setf special parameters
    (let ((node (isl::get-new-result *set-domain* *map-read* *map-write* *map-schedule*)))
      (isl:pretty-print-node node)
      (print "ok")
      (let ((r (my-main node nil)))
        (print (ir-expand r))
        r))))

(defun ir-isl-optimize (ir)
  ir)
