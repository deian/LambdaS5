#lang racket

(require redex)
(require "s5.rkt")

(define simple-application
  (term ([] [] [] ((λ (x) x) 5))))
(define after-lambda
  (term ([] [] [] (([] : (λ (x) x)) 5))))
(define after-applying
  (term ([] [(loc 5)] [(x loc)] x)))
(define after-lookup
  (term ([] [(loc 5)] [(x loc)] 5)))

(test--> →s5 simple-application after-lambda)
(test--> →s5 after-lambda after-applying)
(test--> →s5 after-applying after-lookup)

(test-->> →s5 (term ([] [] [] ((λ (x) (if (canFlowTo x ⊤) 3 4)) ⊤)))
             (term ([] [(loc ⊤)] [(x loc)] 3)))

(define double-apply
  (term ([] [] [] ((λ (x y) y) 5 "foo"))))
(define d-after-lambda
  (term ([] [] [] (([] : (λ (x y) y)) 5 "foo"))))
(define d-after-applying
  (term ([] [(loc 5) (loc1 "foo")] [(x loc) (y loc1)] y)))
(define d-after-lookup
  (term ([] [(loc 5) (loc1 "foo")] [(x loc) (y loc1)]  "foo")))

(test--> →s5 double-apply d-after-lambda)
(test--> →s5 d-after-lambda d-after-applying)
(test--> →s5 d-after-applying d-after-lookup)


(define closure
  (term ([] [] [] (((λ (x) (λ (y) x)) 5) null))))
(define c-after-lambda1
  (term ([] [] [] ((([] : (λ (x) (λ (y) x))) 5) null))))
(define c-after-apply1
  (term ([] [(loc 5)] [(x loc)] ((λ (y) x) null))))
(define c-after-lambda2
  (term ([] [(loc 5)] [(x loc)] (([(x loc)] : (λ (y) x)) null))))
(define c-after-apply2
  (term ([] [(loc 5) (loc1 null)] [(y loc1) (x loc)] x)))
(define c-after-lookup
  (term ([] [(loc 5) (loc1 null)] [(y loc1) (x loc)] 5)))
(test--> →s5 closure c-after-lambda1)
(test--> →s5 c-after-lambda1 c-after-apply1)
(test--> →s5 c-after-apply1 c-after-lambda2)
(test--> →s5 c-after-lambda2 c-after-apply2)
(test--> →s5 c-after-apply2 c-after-lookup)

(define double-x
  (term ([] [] [] (λ (x x) x))))

(define rec
  (term ([] [] [] (rec [f (λ (x) (f x))] (f 3)))))
(define after-rec
  (term ([] [(loc ([(f loc)] : (λ (x) (f x))))] [(f loc)] (f 3))))
(test--> →s5 rec after-rec)

(define shadow
  (term ([] [] [] (((λ (x) (λ (x) x)) 5) 22))))
(define shadow-after-lambda
  (term ([] [] [] ((([] : (λ (x) (λ (x) x))) 5) 22))))
(define shadow-after-apply
  (term ([] [(loc 5)] [(x loc)] ((λ (x) x) 22))))
(define shadow-after-apply2
  (term ([] [(loc 5)] [(x loc)] (([(x loc)] : (λ (x) x)) 22))))
(define shadow-after-apply3
  (term ([] [(loc 5) (loc1 22)] [(x loc1) (x loc)] x)))
(define shadow-after-apply4
  (term ([] [(loc 5) (loc1 22)] [(x loc1) (x loc)] 22)))

(test--> →s5 shadow shadow-after-lambda)
(test--> →s5 shadow-after-lambda shadow-after-apply)
(test--> →s5 shadow-after-apply shadow-after-apply2)
(test--> →s5 shadow-after-apply2 shadow-after-apply3)
(test--> →s5 shadow-after-apply3 shadow-after-apply4)


(define obj-get
  (term ([] [] [] (get-field (object []
                                     [("x" [(@v 5) (@w #f) (@c #f) (@e #f)])])
                   "x" null))))

(define obj-get-after-obj
  (term ([(ref_new ([]
                    [("x" [(@v 5) (@w #f) (@c #f) (@e #f)])]))]
        [] []
        (get-field ref_new "x" null))))

(define obj-get-after-g2
  (term ([(ref_new ([]
                    [("x" [(@v 5) (@w #f) (@c #f) (@e #f)])]))]
        [] []
        (get-field2 ref_new ref_new "x" null))))

(define obj-get-after-get
  (term ([(ref_new ([]
                    [("x" [(@v 5) (@w #f) (@c #f) (@e #f)])]))]
        [] []
        5)))

(test--> →s5 obj-get obj-get-after-obj)
(test--> →s5 obj-get-after-obj obj-get-after-g2)
(test--> →s5 obj-get-after-g2 obj-get-after-get)


(define obj-with-proto
  (term ([] [] [] (get-field
    (object [(proto
              (object []
                      [("x" [(@v 22) (@w #f) (@c #f) (@e #f)])]))]
            []) "x" null))))

(define obj-with-proto-after-obj
  (term ([(ref_new ([] [("x" [(@v 22) (@w #f) (@c #f) (@e #f)])]))] [] []
         (get-field (object [(proto ref_new)] []) "x" null))))

(define obj-with-proto-after-obj-again
  (term ([(ref_new1 ([(proto ref_new)] []))
          (ref_new ([] [("x" [(@v 22) (@w #f) (@c #f) (@e #f)])]))] [] []
         (get-field ref_new1 "x" null))))

(define obj-with-proto-after-g2
  (term ([(ref_new1 ([(proto ref_new)] []))
          (ref_new ([] [("x" [(@v 22) (@w #f) (@c #f) (@e #f)])]))] [] []
         (get-field2 ref_new1 ref_new1 "x" null))))
  

(test--> →s5 obj-with-proto obj-with-proto-after-obj)
(test--> →s5 obj-with-proto-after-obj obj-with-proto-after-obj-again)
(test--> →s5 obj-with-proto-after-obj-again obj-with-proto-after-g2)

(define obj-getter
  (term ([] [] [] (get-field (object [(proto
    (object [] [("getter" [(@g (λ (this args) 27))
                           (@s null) (@c #f) (@e #f)])]))] [])
    "getter" null))))

(test-->> →s5 obj-getter 
  (term ([(ref_new1 (((proto ref_new)) ()))
          (ref_new (() [("getter" [(@g (() : (λ (this args) 27)))
                        (@s null) (@c #f) (@e #f)])]))]
         [(loc ref_new1) (loc1 null)]
         [(this loc) (args loc1)]
         27)))

(define obj-missed-lookup
  (term ([] [] [] (get-field (object [(proto null)] []) "foo" null))))

(test-->> →s5 obj-missed-lookup (term ([(ref_new ([(proto null)] []))] [] [] undefined)))

(define obj-set-field
  (term ([(ref_new ([] [("x" [(@v 24) (@w #t) (@c #f) (@e #f)])]))]
         [] []
         (set-field2 ref_new ref_new "x" "foozle" null))))
(define obj-set-field-after
  (term ([(ref_new ([] [("x" [(@v "foozle") (@w #t) (@c #f) (@e #f)])]))]
         [] []
         "foozle")))

(test-->> →s5 obj-set-field obj-set-field-after)

(define obj-add-field
  (term ([(ref_new ([(extensible #t)] []))] [] []
         (set-field ref_new "foo" 22 null))))


(define obj-add-field-after-add
  (term ([(ref_new ([(extensible #t)]
         [("foo" [(@v 22) (@w #t) (@c #t) (@e #t)])]))]
        [] []
        22)))

(test-->> →s5 obj-add-field obj-add-field-after-add)

(define obj-setter
  (term ([(ref_new ([(extensible #t)]
                    [("x" 
                      [(@g null)
                       (@s ([] : (λ (this args) (set-field this "y" args null))))
                       (@c #t)
                       (@e #f)])]))]
         [] []
         (set-field2 ref_new ref_new "x" "the-answer" "the-args"))))

(define obj-setter-after-set
  (term ([(ref_new ([(extensible #t)]
                    [("y" [(@v "the-args") (@w #t) (@c #t) (@e #t)])
                     ("x" 
                      [(@g null)
                       (@s ([] : (λ (this args) (set-field this "y" args null))))
                       (@c #t) (@e #f)])
                     ]))]
         [(loc ref_new) (loc1 "the-args")]
         [(this loc) (args loc1)]
         "the-answer")))

(test-->> →s5 obj-setter obj-setter-after-set)

(define eseq
  (term ([] [] [] (seq 5 6))))
(test--> →s5 eseq (term ([] [] [] 6)))

(define eseq2
  (term ([] [] [] (seq (seq 3 4) "end"))))
(test-->> →s5 eseq2 (term ([] [] [] "end")))

(define eif
  (term ([] [] [] (if #t "expected" "not-expected"))))
(test--> →s5 eif (term ([] [] [] "expected")))
