(let ((a!1 (exists ((b1_ Real) (b2_ Real) (b3_ Real) (b4_ Real) (b5_ Real))
             (let ((a!1 (forall ((b1__ Real)
                                 (b2__ Real)
                                 (b3__ Real)
                                 (b4__ Real)
                                 (b5__ Real))
                          (let ((a!1 (or (<= b2__ (/ 2.0 5.0))
                                         (<= b5__ (/ 2.0 5.0))
                                         (<= b3__ (/ 2.0 5.0))
                                         (<= (- (/ 4.0 5.0))
                                             (+ (* (- 1.0) b4__)
                                                (* (- 1.0) b2__)))
                                         (<= (- (/ 4.0 5.0))
                                             (+ (* (- 1.0) b1__)
                                                (* (- 1.0) b4__)))
                                         (<= (- (/ 4.0 5.0))
                                             (+ (* (- 1.0) b1__)
                                                (* (- 1.0) b3__)))))
                                (a!2 (<= (- (/ 6.0 5.0))
                                         (+ (* (- 1.0) b5__)
                                            (* (- 1.0) b1__)
                                            (* (- 1.0) b4__))))
                                (a!4 (or (<= b2__ (/ 2.0 5.0))
                                         (<= b5__ (/ 2.0 5.0))
                                         (<= b3__ (/ 2.0 5.0))
                                         (<= (- (/ 4.0 5.0))
                                             (+ (* (- 1.0) b1__)
                                                (* (- 1.0) b4__)))
                                         (<= (- (/ 4.0 5.0))
                                             (+ (* (- 1.0) b4__)
                                                (* (- 1.0) b3__)))
                                         (<= (- (/ 4.0 5.0))
                                             (+ (* (- 1.0) b1__)
                                                (* (- 1.0) b2__)))))
                                (a!6 (or (<= b2__ (/ 2.0 5.0))
                                         (<= b5__ (/ 2.0 5.0))
                                         (<= b4__ (/ 2.0 5.0))
                                         (<= (- (/ 4.0 5.0))
                                             (+ (* (- 1.0) b5__)
                                                (* (- 1.0) b1__)))
                                         (<= (- (/ 4.0 5.0))
                                             (+ (* (- 1.0) b4__)
                                                (* (- 1.0) b3__)))
                                         (<= (- (/ 4.0 5.0))
                                             (+ (* (- 1.0) b1__)
                                                (* (- 1.0) b3__)))))
                                (a!7 (or (<= b2__ (/ 2.0 5.0))
                                         (<= b5__ (/ 2.0 5.0))
                                         (<= b1__ (/ 2.0 5.0))
                                         (<= (- (/ 4.0 5.0))
                                             (+ (* (- 1.0) b3__)
                                                (* (- 1.0) b2__)))
                                         (<= (- (/ 4.0 5.0))
                                             (+ (* (- 1.0) b5__)
                                                (* (- 1.0) b4__)))
                                         (<= (- (/ 4.0 5.0))
                                             (+ (* (- 1.0) b4__)
                                                (* (- 1.0) b3__)))))
                                (a!8 (or (<= b2__ (/ 2.0 5.0))
                                         (<= b1__ (/ 2.0 5.0))
                                         (<= b4__ (/ 2.0 5.0))
                                         (<= (- (/ 4.0 5.0))
                                             (+ (* (- 1.0) b3__)
                                                (* (- 1.0) b2__)))
                                         (<= (- (/ 4.0 5.0))
                                             (+ (* (- 1.0) b5__)
                                                (* (- 1.0) b3__)))
                                         (<= (- (/ 4.0 5.0))
                                             (+ (* (- 1.0) b5__)
                                                (* (- 1.0) b1__)))))
                                (a!9 (or (<= b1__ (/ 2.0 5.0))
                                         (<= b2__ (/ 4.0 5.0))
                                         (<= (- (/ 4.0 5.0))
                                             (+ (* (- 1.0) b5__)
                                                (* (- 1.0) b3__)))
                                         (<= (- (/ 4.0 5.0))
                                             (+ (* (- 1.0) b5__)
                                                (* (- 1.0) b4__)))))
                                (a!10 (or (<= b2__ (/ 4.0 5.0))
                                          (<= (- (/ 4.0 5.0))
                                              (+ (* (- 1.0) b5__)
                                                 (* (- 1.0) b3__)))
                                          (<= (- (/ 4.0 5.0))
                                              (+ (* (- 1.0) b1__)
                                                 (* (- 1.0) b4__)))))
                                (a!11 (or (<= (- (/ 4.0 5.0))
                                              (+ (* (- 1.0) b4__)
                                                 (* (- 1.0) b2__)))
                                          (<= b1__ (/ 4.0 5.0))
                                          (<= b5__ (/ 4.0 5.0))))
                                (a!12 (or (<= b2__ (/ 2.0 5.0))
                                          (<= (- (/ 4.0 5.0))
                                              (+ (* (- 1.0) b4__)
                                                 (* (- 1.0) b2__)))
                                          (<= (- (/ 4.0 5.0))
                                              (+ (* (- 1.0) b5__)
                                                 (* (- 1.0) b3__)))
                                          (<= (- (/ 4.0 5.0))
                                              (+ (* (- 1.0) b5__)
                                                 (* (- 1.0) b1__)))
                                          (<= (- (/ 4.0 5.0))
                                              (+ (* (- 1.0) b1__)
                                                 (* (- 1.0) b4__)))
                                          (<= (- (/ 4.0 5.0))
                                              (+ (* (- 1.0) b1__)
                                                 (* (- 1.0) b3__)))))
                                (a!13 (or (<= b2__ (/ 2.0 5.0))
                                          (<= b1__ (/ 2.0 5.0))
                                          (<= (- (/ 4.0 5.0))
                                              (+ (* (- 1.0) b4__)
                                                 (* (- 1.0) b2__)))
                                          (<= (- (/ 4.0 5.0))
                                              (+ (* (- 1.0) b3__)
                                                 (* (- 1.0) b2__)))
                                          (<= (- (/ 4.0 5.0))
                                              (+ (* (- 1.0) b5__)
                                                 (* (- 1.0) b3__)))
                                          (<= (- (/ 4.0 5.0))
                                              (+ (* (- 1.0) b5__)
                                                 (* (- 1.0) b4__)))
                                          (<= (- (/ 4.0 5.0))
                                              (+ (* (- 1.0) b5__)
                                                 (* (- 1.0) b1__)))))
                                (a!14 (or (<= b1__ (/ 4.0 5.0))
                                          (<= b2__ (/ 4.0 5.0))
                                          (<= (- (/ 4.0 5.0))
                                              (+ (* (- 1.0) b5__)
                                                 (* (- 1.0) b3__)))))
                                (a!15 (or (<= b4__ (/ 2.0 5.0))
                                          (<= b2__ (/ 4.0 5.0))
                                          (<= (- (/ 4.0 5.0))
                                              (+ (* (- 1.0) b5__)
                                                 (* (- 1.0) b3__)))
                                          (<= (- (/ 4.0 5.0))
                                              (+ (* (- 1.0) b5__)
                                                 (* (- 1.0) b1__)))))
                                (a!16 (or (<= b5__ (/ 2.0 5.0))
                                          (<= b2__ (/ 4.0 5.0))
                                          (<= (- (/ 4.0 5.0))
                                              (+ (* (- 1.0) b1__)
                                                 (* (- 1.0) b4__)))
                                          (<= (- (/ 4.0 5.0))
                                              (+ (* (- 1.0) b4__)
                                                 (* (- 1.0) b3__)))))
                                (a!18 (<= (- (/ 6.0 5.0))
                                          (+ (* (- 1.0) b1__)
                                             (* (- 1.0) b3__)
                                             (* (- 1.0) b2__))))
                                (a!21 (or (<= b2__ (/ 4.0 5.0))
                                          (<= b3__ (/ 4.0 5.0))
                                          (<= (- (/ 4.0 5.0))
                                              (+ (* (- 1.0) b1__)
                                                 (* (- 1.0) b4__)))))
                                (a!22 (or (<= (- (/ 4.0 5.0))
                                              (+ (* (- 1.0) b4__)
                                                 (* (- 1.0) b2__)))
                                          (<= b5__ (/ 4.0 5.0))
                                          (<= (- (/ 4.0 5.0))
                                              (+ (* (- 1.0) b1__)
                                                 (* (- 1.0) b3__)))))
                                (a!23 (or (<= b4__ (/ 4.0 5.0))
                                          (<= b5__ (/ 4.0 5.0))
                                          (<= (- (/ 4.0 5.0))
                                              (+ (* (- 1.0) b1__)
                                                 (* (- 1.0) b3__)))))
                                (a!24 (or (<= b5__ (/ 2.0 5.0))
                                          (<= b4__ (/ 2.0 5.0))
                                          (<= (- (/ 4.0 5.0))
                                              (+ (* (- 1.0) b4__)
                                                 (* (- 1.0) b2__)))
                                          (<= (- (/ 4.0 5.0))
                                              (+ (* (- 1.0) b5__)
                                                 (* (- 1.0) b1__)))
                                          (<= (- (/ 4.0 5.0))
                                              (+ (* (- 1.0) b4__)
                                                 (* (- 1.0) b3__)))
                                          (<= (- (/ 4.0 5.0))
                                              (+ (* (- 1.0) b1__)
                                                 (* (- 1.0) b2__)))
                                          (<= (- (/ 4.0 5.0))
                                              (+ (* (- 1.0) b1__)
                                                 (* (- 1.0) b3__)))))
                                (a!25 (or (<= b4__ (/ 2.0 5.0))
                                          (<= (- (/ 4.0 5.0))
                                              (+ (* (- 1.0) b4__)
                                                 (* (- 1.0) b2__)))
                                          (<= (- (/ 4.0 5.0))
                                              (+ (* (- 1.0) b5__)
                                                 (* (- 1.0) b3__)))
                                          (<= (- (/ 4.0 5.0))
                                              (+ (* (- 1.0) b5__)
                                                 (* (- 1.0) b1__)))
                                          (<= (- (/ 4.0 5.0))
                                              (+ (* (- 1.0) b1__)
                                                 (* (- 1.0) b3__)))
                                          (<= (- (/ 4.0 5.0))
                                              (+ (* (- 1.0) b5__)
                                                 (* (- 1.0) b2__)))))
                                (a!26 (or (<= b4__ (/ 4.0 5.0))
                                          (<= (- (/ 4.0 5.0))
                                              (+ (* (- 1.0) b1__)
                                                 (* (- 1.0) b3__)))
                                          (<= (- (/ 4.0 5.0))
                                              (+ (* (- 1.0) b5__)
                                                 (* (- 1.0) b2__)))))
                                (a!27 (or (<= b4__ (/ 4.0 5.0))
                                          (<= b3__ (/ 4.0 5.0))
                                          (<= (- (/ 4.0 5.0))
                                              (+ (* (- 1.0) b5__)
                                                 (* (- 1.0) b2__)))))
                                (a!28 (not (<= (- (/ 4.0 5.0))
                                               (+ (* (- 1.0) b5__)
                                                  (* (- 1.0) b1__)))))
                                (a!31 (or (<= b2__ (/ 2.0 5.0))
                                          (<= b1__ (/ 2.0 5.0))
                                          (<= (- (/ 4.0 5.0))
                                              (+ (* (- 1.0) b3__)
                                                 (* (- 1.0) b2__)))
                                          (<= (- (/ 4.0 5.0))
                                              (+ (* (- 1.0) b5__)
                                                 (* (- 1.0) b3__)))
                                          (<= (- (/ 4.0 5.0))
                                              (+ (* (- 1.0) b5__)
                                                 (* (- 1.0) b1__)))
                                          (<= (- (/ 4.0 5.0))
                                              (+ (* (- 1.0) b1__)
                                                 (* (- 1.0) b4__)))
                                          (<= (- (/ 4.0 5.0))
                                              (+ (* (- 1.0) b4__)
                                                 (* (- 1.0) b3__)))))
                                (a!32 (or (<= b2__ (/ 2.0 5.0))
                                          (<= b4__ (/ 4.0 5.0))
                                          (<= (- (/ 4.0 5.0))
                                              (+ (* (- 1.0) b5__)
                                                 (* (- 1.0) b1__)))
                                          (<= (- (/ 4.0 5.0))
                                              (+ (* (- 1.0) b1__)
                                                 (* (- 1.0) b3__)))))
                                (a!33 (or (<= b1__ (/ 2.0 5.0))
                                          (<= (- (/ 4.0 5.0))
                                              (+ (* (- 1.0) b3__)
                                                 (* (- 1.0) b2__)))
                                          (<= b4__ (/ 4.0 5.0))
                                          (<= (- (/ 4.0 5.0))
                                              (+ (* (- 1.0) b5__)
                                                 (* (- 1.0) b2__)))))
                                (a!34 (<= (- (/ 6.0 5.0))
                                          (+ (* (- 1.0) b5__)
                                             (* (- 1.0) b4__)
                                             (* (- 1.0) b3__))))
                                (a!36 (<= (- (/ 6.0 5.0))
                                          (+ (* (- 1.0) b5__)
                                             (* (- 1.0) b1__)
                                             (* (- 1.0) b2__))))
                                (a!37 (<= (- (/ 6.0 5.0))
                                          (+ (* (- 1.0) b4__)
                                             (* (- 1.0) b3__)
                                             (* (- 1.0) b2__)))))
                          (let ((a!3 (or (not (<= b1__ (/ 2.0 5.0)))
                                         (<= b2__ (/ 2.0 5.0))
                                         (<= (- (/ 4.0 5.0))
                                             (+ (* (- 1.0) b5__)
                                                (* (- 1.0) b1__)))
                                         a!2
                                         (<= (- (/ 4.0 5.0))
                                             (+ (* (- 1.0) b4__)
                                                (* (- 1.0) b3__)))
                                         (<= (- (/ 4.0 5.0))
                                             (+ (* (- 1.0) b1__)
                                                (* (- 1.0) b3__)))))
                                (a!5 (or (<= b2__ (/ 2.0 5.0))
                                         (<= b3__ (/ 2.0 5.0))
                                         (<= (- (/ 4.0 5.0))
                                             (+ (* (- 1.0) b5__)
                                                (* (- 1.0) b4__)))
                                         (<= (- (/ 4.0 5.0))
                                             (+ (* (- 1.0) b5__)
                                                (* (- 1.0) b1__)))
                                         a!2
                                         (<= (- (/ 4.0 5.0))
                                             (+ (* (- 1.0) b4__)
                                                (* (- 1.0) b3__)))
                                         (<= (- (/ 4.0 5.0))
                                             (+ (* (- 1.0) b1__)
                                                (* (- 1.0) b2__)))))
                                (a!17 (or (not (<= b4__ (/ 2.0 5.0)))
                                          (<= b2__ (/ 4.0 5.0))
                                          (<= (- (/ 4.0 5.0))
                                              (+ (* (- 1.0) b5__)
                                                 (* (- 1.0) b3__)))
                                          (<= (- (/ 4.0 5.0))
                                              (+ (* (- 1.0) b5__)
                                                 (* (- 1.0) b4__)))
                                          a!2))
                                (a!19 (or (<= b5__ (/ 2.0 5.0))
                                          (<= b4__ (/ 2.0 5.0))
                                          (<= (- (/ 4.0 5.0))
                                              (+ (* (- 1.0) b3__)
                                                 (* (- 1.0) b2__)))
                                          (<= (- (/ 4.0 5.0))
                                              (+ (* (- 1.0) b1__)
                                                 (* (- 1.0) b4__)))
                                          (<= (- (/ 4.0 5.0))
                                              (+ (* (- 1.0) b4__)
                                                 (* (- 1.0) b3__)))
                                          a!18
                                          (<= (- (/ 4.0 5.0))
                                              (+ (* (- 1.0) b1__)
                                                 (* (- 1.0) b2__)))))
                                (a!20 (or (<= b5__ (/ 2.0 5.0))
                                          (<= (- (/ 4.0 5.0))
                                              (+ (* (- 1.0) b4__)
                                                 (* (- 1.0) b2__)))
                                          (<= (- (/ 4.0 5.0))
                                              (+ (* (- 1.0) b3__)
                                                 (* (- 1.0) b2__)))
                                          (<= (- (/ 4.0 5.0))
                                              (+ (* (- 1.0) b5__)
                                                 (* (- 1.0) b3__)))
                                          (<= (- (/ 4.0 5.0))
                                              (+ (* (- 1.0) b5__)
                                                 (* (- 1.0) b4__)))
                                          (<= (- (/ 4.0 5.0))
                                              (+ (* (- 1.0) b5__)
                                                 (* (- 1.0) b1__)))
                                          a!2
                                          a!18
                                          (<= (- (/ 4.0 5.0))
                                              (+ (* (- 1.0) b1__)
                                                 (* (- 1.0) b2__)))))
                                (a!29 (or (not (<= b2__ (/ 4.0 5.0)))
                                          (<= (- (/ 4.0 5.0))
                                              (+ (* (- 1.0) b1__)
                                                 (* (- 1.0) b4__)))
                                          a!28
                                          (<= (- (/ 4.0 5.0))
                                              (+ (* (- 1.0) b1__)
                                                 (* (- 1.0) b3__)))
                                          (<= (- (/ 4.0 5.0))
                                              (+ (* (- 1.0) b5__)
                                                 (* (- 1.0) b2__)))))
                                (a!30 (or (not (<= b1__ (/ 2.0 5.0)))
                                          (<= (- (/ 4.0 5.0))
                                              (+ (* (- 1.0) b5__)
                                                 (* (- 1.0) b1__)))
                                          (not (<= b5__ (/ 4.0 5.0)))
                                          a!2
                                          (<= (- (/ 4.0 5.0))
                                              (+ (* (- 1.0) b1__)
                                                 (* (- 1.0) b3__)))
                                          (<= (- (/ 4.0 5.0))
                                              (+ (* (- 1.0) b5__)
                                                 (* (- 1.0) b2__)))))
                                (a!35 (or (<= b1__ (/ 2.0 5.0))
                                          (<= b4__ (/ 2.0 5.0))
                                          (<= (- (/ 4.0 5.0))
                                              (+ (* (- 1.0) b3__)
                                                 (* (- 1.0) b2__)))
                                          (<= (- (/ 4.0 5.0))
                                              (+ (* (- 1.0) b5__)
                                                 (* (- 1.0) b4__)))
                                          (<= (- (/ 4.0 5.0))
                                              (+ (* (- 1.0) b4__)
                                                 (* (- 1.0) b3__)))
                                          a!34
                                          (<= (- (/ 4.0 5.0))
                                              (+ (* (- 1.0) b5__)
                                                 (* (- 1.0) b2__)))))
                                (a!38 (or (not (<= b5__ (/ 2.0 5.0)))
                                          a!36
                                          (<= (- (/ 4.0 5.0))
                                              (+ (* (- 1.0) b3__)
                                                 (* (- 1.0) b2__)))
                                          (<= (- (/ 4.0 5.0))
                                              (+ (* (- 1.0) b5__)
                                                 (* (- 1.0) b3__)))
                                          (<= (- (/ 4.0 5.0))
                                              (+ (* (- 1.0) b5__)
                                                 (* (- 1.0) b1__)))
                                          (<= (- (/ 4.0 5.0))
                                              (+ (* (- 1.0) b1__)
                                                 (* (- 1.0) b4__)))
                                          (<= (- (/ 4.0 5.0))
                                              (+ (* (- 1.0) b4__)
                                                 (* (- 1.0) b3__)))
                                          a!37))
                                (a!39 (or (not (<= b5__ (/ 2.0 5.0)))
                                          a!36
                                          (<= b4__ (/ 4.0 5.0))
                                          (<= (- (/ 4.0 5.0))
                                              (+ (* (- 1.0) b5__)
                                                 (* (- 1.0) b1__)))
                                          (<= (- (/ 4.0 5.0))
                                              (+ (* (- 1.0) b1__)
                                                 (* (- 1.0) b3__)))))
                                (a!40 (or (<= b1__ (/ 2.0 5.0))
                                          (<= (- (/ 4.0 5.0))
                                              (+ (* (- 1.0) b3__)
                                                 (* (- 1.0) b2__)))
                                          (<= (- (/ 4.0 5.0))
                                              (+ (* (- 1.0) b5__)
                                                 (* (- 1.0) b3__)))
                                          (<= (- (/ 4.0 5.0))
                                              (+ (* (- 1.0) b5__)
                                                 (* (- 1.0) b4__)))
                                          (<= (- (/ 4.0 5.0))
                                              (+ (* (- 1.0) b4__)
                                                 (* (- 1.0) b3__)))
                                          a!37
                                          (<= (- (/ 4.0 5.0))
                                              (+ (* (- 1.0) b5__)
                                                 (* (- 1.0) b2__)))))
                                (a!41 (or (<= b5__ (/ 2.0 5.0))
                                          (<= (- (/ 4.0 5.0))
                                              (+ (* (- 1.0) b3__)
                                                 (* (- 1.0) b2__)))
                                          (<= (- (/ 4.0 5.0))
                                              (+ (* (- 1.0) b1__)
                                                 (* (- 1.0) b4__)))
                                          (<= (- (/ 4.0 5.0))
                                              (+ (* (- 1.0) b4__)
                                                 (* (- 1.0) b3__)))
                                          (<= (- (/ 4.0 5.0))
                                              (+ (* (- 1.0) b1__)
                                                 (* (- 1.0) b2__)))
                                          (<= (- (/ 4.0 5.0))
                                              (+ (* (- 1.0) b1__)
                                                 (* (- 1.0) b3__)))
                                          a!37))
                                (a!42 (or (<= (- (/ 4.0 5.0))
                                              (+ (* (- 1.0) b4__)
                                                 (* (- 1.0) b2__)))
                                          (<= b1__ (/ 4.0 5.0))
                                          (<= (- (/ 4.0 5.0))
                                              (+ (* (- 1.0) b5__)
                                                 (* (- 1.0) b4__)))
                                          (<= (- (/ 4.0 5.0))
                                              (+ (* (- 1.0) b4__)
                                                 (* (- 1.0) b3__)))
                                          a!34))
                                (a!43 (or (<= (- (/ 4.0 5.0))
                                              (+ (* (- 1.0) b3__)
                                                 (* (- 1.0) b2__)))
                                          (<= b4__ (/ 4.0 5.0))
                                          a!18
                                          (<= (- (/ 4.0 5.0))
                                              (+ (* (- 1.0) b1__)
                                                 (* (- 1.0) b2__)))
                                          (<= (- (/ 4.0 5.0))
                                              (+ (* (- 1.0) b5__)
                                                 (* (- 1.0) b2__)))))
                                (a!44 (or (<= (- (/ 4.0 5.0))
                                              (+ (* (- 1.0) b3__)
                                                 (* (- 1.0) b2__)))
                                          (<= b5__ (/ 4.0 5.0))
                                          (<= (- (/ 4.0 5.0))
                                              (+ (* (- 1.0) b4__)
                                                 (* (- 1.0) b3__)))
                                          (<= (- (/ 4.0 5.0))
                                              (+ (* (- 1.0) b1__)
                                                 (* (- 1.0) b3__)))
                                          a!37))
                                (a!45 (or (<= b2__ (/ 4.0 5.0))
                                          (<= (- (/ 4.0 5.0))
                                              (+ (* (- 1.0) b5__)
                                                 (* (- 1.0) b4__)))
                                          (<= (- (/ 4.0 5.0))
                                              (+ (* (- 1.0) b1__)
                                                 (* (- 1.0) b4__)))
                                          (<= (- (/ 4.0 5.0))
                                              (+ (* (- 1.0) b4__)
                                                 (* (- 1.0) b3__)))
                                          a!34)))
                          (let ((a!46 (or (and (<= b1__ (/ 7.0 5.0))
                                               (<= b2__ (/ 7.0 5.0))
                                               (<= b3__ (/ 7.0 5.0))
                                               (<= b4__ (/ 7.0 5.0))
                                               (<= b5__ (/ 7.0 5.0)))
                                          (and a!1
                                               a!3
                                               (or (<= b2__ (/ 2.0 5.0))
                                                   (<= b5__ (/ 2.0 5.0))
                                                   (<= b4__ (/ 4.0 5.0))
                                                   (<= b3__ (/ 4.0 5.0)))
                                               (or (<= b3__ (/ 4.0 5.0))
                                                   (<= b5__ (/ 4.0 5.0)))
                                               (or (<= b2__ (/ 4.0 5.0))
                                                   (<= b5__ (/ 4.0 5.0)))
                                               a!4
                                               a!5
                                               (or (<= b4__ (/ 4.0 5.0))
                                                   (<= b2__ (/ 4.0 5.0)))
                                               a!6
                                               a!7
                                               a!8
                                               a!9
                                               a!10
                                               a!11
                                               a!12
                                               a!13
                                               a!14
                                               a!15
                                               a!16
                                               a!17
                                               a!19
                                               a!20
                                               a!21
                                               a!22
                                               a!23
                                               a!24
                                               a!25
                                               a!26
                                               a!27
                                               a!29
                                               a!30
                                               a!31
                                               a!32
                                               a!33
                                               a!35
                                               (or (<= b1__ (/ 4.0 5.0))
                                                   (<= b3__ (/ 4.0 5.0)))
                                               a!38
                                               (or (<= b1__ (/ 4.0 5.0))
                                                   (<= b4__ (/ 4.0 5.0)))
                                               a!39
                                               a!40
                                               a!41
                                               a!42
                                               a!43
                                               a!44
                                               a!45))))
                            (=> (and (= (+ b1__ b2__ b3__ b4__ b5__)
                                        (+ b1_ b2_ b3_ b4_ b5_ 1.0))
                                     (>= b1__ b1_)
                                     (>= b2__ b2_)
                                     (>= b3__ b3_)
                                     (>= b4__ b4_)
                                     (>= b5__ b5_))
                                a!46)))))))
               (and (or (and (= b1_ 0.0)
                             (= b2_ 0.0)
                             (= b3_ b3)
                             (= b4_ b4)
                             (= b5_ b5))
                        (and (= b2_ 0.0)
                             (= b3_ 0.0)
                             (= b4_ b4)
                             (= b5_ b5)
                             (= b1_ b1))
                        (and (= b3_ 0.0)
                             (= b4_ 0.0)
                             (= b5_ b5)
                             (= b1_ b1)
                             (= b2_ b2))
                        (and (= b4_ 0.0)
                             (= b5_ 0.0)
                             (= b1_ b1)
                             (= b2_ b2)
                             (= b3_ b3))
                        (and (= b5_ 0.0)
                             (= b1_ 0.0)
                             (= b2_ b2)
                             (= b3_ b3)
                             (= b4_ b4)))
                    a!1)))))
  (and true
       (or (and (<= b1 (/ 7.0 5.0))
                (<= b2 (/ 7.0 5.0))
                (<= b3 (/ 7.0 5.0))
                (<= b4 (/ 7.0 5.0))
                (<= b5 (/ 7.0 5.0))
                true)
           a!1)))