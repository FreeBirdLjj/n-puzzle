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

(defun make-heap (&optional (size 1024))
  (make-array size
              :fill-pointer 0
              :adjustable t))

(defstruct fringe
  (key #'identity)
  (elements (make-heap))) ; Heap

(defun fringe-remove (q)
  (heap-pop (fringe-elements q) (fringe-key q)))

(defun fringe-insert (q items)
  (mapc (lambda (item)
          (heap-insert (fringe-elements q) item (fringe-key q)))
        items)
  q)

(defstruct node
  state
  (parent nil)
  (direction nil)
  (path-cost 0)
  (depth 0))

(defun expand (heuristic successor node fringe)
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
                       (find (aref temp-triple 1) (fringe-elements fringe) :key #'node-state :test #'equal))
                     (funcall successor heuristic (node-state node) (node-direction node)))))

(defun direction-sequence (node)
  (labels ((direction-sequence-iter (node directions)
             (if (null (node-parent node))
                 directions
               (direction-sequence-iter (node-parent node) (cons (node-direction node) directions)))))
    (direction-sequence-iter node nil)))

(defun A*-search (heuristic fringe successor goalp)
  (let ((node (fringe-remove fringe)))
    (if (funcall goalp (node-state node))
        (list (direction-sequence node) (node-depth node))
      (A*-search heuristic
                 (fringe-insert fringe (expand heuristic successor node fringe))
                 successor
                 goalp))))

(defun tree-search (search successor heuristic goalp initial-state)
  (funcall search
           heuristic
           (fringe-insert (make-fringe :key #'node-path-cost) (list (make-node :state initial-state)))
           successor
           goalp))

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

(defparameter *target* (vector 0  1  2
                               3  -1 4
                               5  6  7
                               8  -1 9
                               10 11 12))

(defparameter *width* 3)

(defun goalp (node)
  (equalp node *target*))

(defun successor (heuristic old-state old-direction)
  (mapcar (lambda (state-direction)
            (let ((state (car state-direction))
                  (direction (cdr state-direction)))
              (vector direction state (funcall heuristic state))))
          (remove nil
                  (mapcar (lambda (direction)
                            (move-blank old-state direction))
                          (remove (case old-direction
                                    (UP 'DOWN)
                                    (DOWN 'UP)
                                    (RIGHT 'LEFT)
                                    (LEFT 'RIGHT))
                                  '(UP DOWN RIGHT LEFT)))
                  :key #'car)))

(defun n-puzzle (search heuristic initial-state)
  (tree-search search #'successor heuristic #'goalp initial-state))

(time (format t "~A~%" (n-puzzle #'A*-search
                                 #'manhattan
                                 (vector 3  1  2
                                         8  -1 4
                                         0  10 5
                                         11 -1 7
                                         12 9  6))))
