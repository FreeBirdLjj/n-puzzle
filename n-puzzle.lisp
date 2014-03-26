(declaim (optimize (speed 3)
                   (compilation-speed 0)
                   (safety 0)
                   (debug 0)))

(defun heap-val (heap i key)
  (funcall key (aref heap i)))

(defun heap-parent (i)
  (floor (1- i) 2))

(defun heap-left (i)
  (+ 1 i i))

(defun heap-right (i)
  (+ 2 i i))

(defun heap-leafp (heap i)
  (> i (1- (floor (fill-pointer heap) 2))))

(defun heapify (heap i key)
  (unless (heap-leafp heap i)
    (let* ((left-index (heap-left i))
           (right-index (heap-right i))
           (smaller-index
            (if (and (< right-index (fill-pointer heap))
                     (< (heap-val heap right-index key)
                        (heap-val heap left-index key)))
                right-index
              left-index)))
      (when (> (heap-val heap i key)
               (heap-val heap smaller-index key))
        (rotatef (aref heap i)
                 (aref heap smaller-index))
        (heapify heap smaller-index key)))))

(defun heap-pop (heap key)
  (let ((minimum (aref heap 0)))
    (setf (aref heap 0) (aref heap (1- (fill-pointer heap))))
    (decf (fill-pointer heap))
    (heapify heap 0 key)
    minimum))

(defun heap-find-pos (heap i val key)
  (if (or (zerop i)
          (< (heap-val heap (heap-parent i) key) val))
      i
    (progn
      (setf (aref heap i) (aref heap (heap-parent i)))
      (heap-find-pos heap (heap-parent i) val key))))

(defun heap-insert (heap item key)
  (vector-push-extend nil heap)
  (setf (aref heap (heap-find-pos heap
                                  (1- (fill-pointer heap))
                                  (funcall key item)
                                  key))
	item))

(defun heap-find (heap val key)
  (labels ((heap-find-iter (i)
             (let ((i-val (heap-val heap i key)))
               (cond
                ((= i-val val)
                 (aref heap i))
                ((or (> i-val val)
                     (heap-leafp heap i))
                 nil)
                (t
                 (let ((find-left (heap-find-iter (heap-left i))))
                   (if (null find-left)
                       (let ((find-right (heap-find-iter (heap-right i))))
                         (if (null find-right)
                             nil
                           find-right))
                     find-left)))))))
    (heap-find-iter 0)))

(defun make-heap (&optional (size 1024))
  (make-array size
              :fill-pointer 0
              :adjustable t))

(defstruct fringe
  (key #'identity)
  (elements (make-heap)))

(defun fringe-remove (f)
  (heap-pop (fringe-elements f) (fringe-key f)))

(defun fringe-insert (f items)
  (mapc (lambda (item)
          (heap-insert (fringe-elements f) item (fringe-key f)))
        items)
  f)

(defun fringe-find (f key-val)
  (heap-find (fringe-elements f) key-val (fringe-key f)))

(defstruct node
  state
  (parent nil)
  (direction nil)
  (path-cost 0)
  (depth 0))

(defun direction-sequence (node)
  (labels ((direction-sequence-iter (node directions)
             (if (null (node-parent node))
                 directions
               (direction-sequence-iter (node-parent node) (cons (node-direction node) directions)))))
    (direction-sequence-iter node nil)))

(defun A*-search (action heuristic goalp initial-state)
  (labels ((expand (node fringe)
             (mapcar (lambda (direction-state-cost)
                       (let ((direction (aref direction-state-cost 0))
                             (state (aref direction-state-cost 1))
                             (cost (aref direction-state-cost 2))
                             (depth (node-depth node)))
                         (make-node :state state
                                    :parent node
                                    :direction direction
                                    :path-cost (+ depth cost)
                                    :depth (1+ depth))))
                     (remove-if (lambda (temp-triple)
                                  (let ((heap-pos (fringe-find fringe (aref temp-triple 2))))
                                    (and heap-pos
                                         (equal (node-state heap-pos) (aref temp-triple 2)))))
                                (mapcar (lambda (state-direction)
                                          (let ((state (car state-direction))
                                                (direction (cdr state-direction)))
                                            (vector direction state (funcall heuristic state))))
                                        (funcall action (node-state node) (node-direction node))))))
           (search-iter (fringe)
             (let ((node (fringe-remove fringe)))
               (if (funcall goalp (node-state node))
                   (list (direction-sequence node) (node-depth node))
                 (search-iter (fringe-insert fringe (expand node fringe)))))))
    (search-iter (fringe-insert (make-fringe :key #'node-path-cost)
                                (list (make-node :state initial-state))))))

(defun IDA*-search (action heuristic goalp initial-state)
  (let ((max-cost-limit 105)
        (initial-node (make-node :state initial-state)))
    (labels ((expand (node)
               (mapcar (lambda (state-direction)
                         (let ((state (car state-direction))
                               (direction (cdr state-direction))
                               (depth (node-depth node)))
                           (make-node :state state
                                      :parent node
                                      :direction direction
                                      :depth (1+ depth))))
                       (funcall action (node-state node) (node-direction node))))
             (search-iter (fringe cost-limit next-cost-limit)
               (if (null fringe)
                   (search-iter (list initial-node) next-cost-limit max-cost-limit)
                 (let* ((node (car fringe))
                        (rst (cdr fringe))
                        (car-cost (+ (funcall heuristic (node-state node)) (node-depth node))))
                   (cond ((> car-cost cost-limit)
                          (search-iter rst cost-limit (min next-cost-limit car-cost)))
                         ((funcall goalp (node-state node))
                          (list (direction-sequence node) (node-depth node)))
                         (t
                          (search-iter (nconc (expand node) rst) cost-limit next-cost-limit)))))))
      (search-iter (list initial-node) (funcall heuristic initial-state) max-cost-limit))))

(defun manhattan (state)
  (declare (special *target*
                    *width*))
  (loop for square from 0 to (reduce #'max state) summing
        (multiple-value-bind (square-x square-y) (floor (position square state) *width*)
          (multiple-value-bind (*target*-x *target*-y) (floor (position square *target*) *width*)
            (+ (abs (- *target*-x square-x)) (abs (- *target*-y square-y)))))))

(defun misplaced (state)
  (declare (special *target*))
  (loop for i from 0 to (1- (length state)) counting
        (not (=
              (aref state i)
              (aref *target* i)))))

(defun swap (state i j)
  ;; move 0 at i to pos j with side-effect.
  (unless (= (aref state j) -1)
    (let ((temp-state (copy-seq state)))
      (rotatef (aref temp-state i) (aref temp-state j))
      temp-state)))

(defun move-blank (state direction)
  (declare (special *width*))
  (cons (case direction
          (UP
           (let ((i (position 0 state))
                 (j (- (position 0 state) *width*)))
             (when (>= j 0)
               (swap state i j))))
          (DOWN
           (let ((i (position 0 state))
                 (j (+ (position 0 state) *width*)))
             (when (< j (length state))
               (swap state i j))))
          (LEFT
           (let ((i (position 0 state))
                 (j (1- (position 0 state))))
             (unless (zerop (mod i *width*))
               (swap state i j))))
          (RIGHT
           (let ((i (position 0 state))
                 (j (1+ (position 0 state))))
             (unless (zerop (mod (1+ i) *width*))
               (swap state i j)))))
        direction))

(defparameter *width* 3)

(defparameter *target* (vector 0 1 2
                               3 4 5
                               6 7 8))

(defparameter *start* (vector 5 1 8
                              7 2 3
                              0 6 4))

(defun goalp (node)
  (equalp node *target*))

(defun action (old-state old-direction)
  ;; return a dotted list (state . direction)
  (remove nil
          (mapcar (lambda (direction)
                    (move-blank old-state direction))
                  (remove (case old-direction
                            (UP 'DOWN)
                            (DOWN 'UP)
                            (RIGHT 'LEFT)
                            (LEFT 'RIGHT))
                          '(UP DOWN RIGHT LEFT)))
          :key #'car))

(defun n-puzzle (search heuristic initial-state)
  (funcall search #'action heuristic #'goalp initial-state))

(format t "IDA*-search~%")
(time (format t "~A~%" (n-puzzle #'IDA*-search
                                 #'manhattan
                                 *start*)))

(format t "A*-search~%")
(time (format t "~A~%" (n-puzzle #'A*-search
                                 #'manhattan
                                 *start*)))
