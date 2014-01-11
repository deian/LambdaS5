#lang racket
(require redex)
(provide s5 →s5)

;; This should be easy to match up with es5_eval and es5_syntax.ml
(define-language s5
  (P (σ Σ Γ e))
  ;; variable store
  (loc (variable-prefix loc))
  (Σ ((loc_!_ val) ...))
  ;; object store
  (ref (variable-prefix ref))
  (σ ((ref_!_ obj) ...))
  ;; explicit closure environments
  (Γ ((x loc) ...))
  (bool #t #f)

  (accessor ((@g val) (@s val) (@c bool) (@e bool)))
  (data ((@v val) (@w bool) (@c bool) (@e bool)))

  (accessor-e ((@g e) (@s e) (@c e) (@e e)))
  (data-e ((@v e) (@w bool) (@c e) (@e e)))

  (attr @g @s @v @w @c @e)
  (obj-attr code primval proto extensible klass)

  (property accessor data)
  (property-e accessor-e data-e)

  (obj-attrs [(obj-attr_!_ val) ...])
  (obj-attrs-e [(obj-attr_!_ e) ...])

  (s string)

  (obj (obj-attrs [(s property) ...]))

  (prim number s #t #f undefined null)
  
  ;; two point lattice
  (l ⊥ ⊤)

  (val prim
       (Γ : (λ (x_!_ ...) e))
       ref
       loc
       l)

  (op1 typeof surface-typeof primitive? prim->str prim->num
       prim->num prim->bool is-callable is-extensible
       prevent-extensions print get-proto get-primval get-class
       get-code property-names own-property-names object-to-string
       strlen is-array to-int32 fail? ! void floor ceil abs log
       ascii-ntoc ascii-cton to-lower to-upper ~ sin)
  (op2 + - / * % & binary-or ^ << >> >>> < <= > >= stx= abs= hasProperty
       hasOwnProperty string+ string< base char-at local-compare
       pow to-fixed isAccessor)

  (lbl x)

  (e prim
     l
     x
     (λ (x_!_ ...) e)
     (object obj-attrs-e
             [(string property-e) ...])
     (get-attr attr e e)
     (set-attr attr e e e)

     (get-field e e e)
     (get-field2 val val val val)
     (set-field e e e e)
     (set-field2 val val val val val)
     (delete-field e e e)

     (set! x e)

     (e e ...)
     (op op1 e)
     (op op2 e e)

     (if e e e)
     (seq e e)

     (let ([x e]) e)
     (rec ([x e]) e)

     (label lbl e)
     (break lbl e)

     (catch e e)
     (finally e e)
     (throw e)

     (join e e)
     (meet e e)
     (canFlowTo e e))

   ((f g x y z) variable-not-otherwise-mentioned)


   ;; Top-level contexts
   (E-property
      (string ((@v E) (@w bool) (@c bool) (@e bool)))
      (string ((@g E) (@s e) (@c bool) (@e bool)))
      (string ((@g val) (@s E) (@c bool) (@e bool))))

   (E-attrs
      [(obj-attr val) ... (obj-attr E) (obj-attr e) ...])

   (E hole
      (object E-attrs [(string property-e) ...])
      (object obj-attrs [(string property) ...
                         E-property
                         (string property-e) ...])

      (get-attr attr E e)
      (get-attr attr val E)

      (set-attr attr E e e)
      (set-attr attr val E e)
      (set-attr attr val val E)

      (get-field E e e)
      (get-field val E e)
      (get-field val val E)

      (set-field E e e e)
      (set-field val E e e)
      (set-field val val E e)
      (set-field val val val E)

      (delete-field E e e)
      (delete-field val E e)
      (delete-field val val E)

      (set! x E)

      (val ... E e ...)
      (op1 op E)
      (op2 op E e)
      (op2 op val E)

      (if E e e)

      (seq E e)
      (seq val E)

      (let ([x E]) e)

      (label lbl E)
      (break lbl E)

      (throw E)
      (catch E e)
      (finally E e)
      
      (join E e)
      (join val E)
      (meet E e)
      (meet val E)
      (canFlowTo E e)
      (canFlowTo val E)
      ))

;; full terms are of the form
;; (σ, Σ, Γ, e)
(define →s5
  (reduction-relation
   s5

   ;; Binding, variables, and assignment
   ;; ----------------------------------
   (--> (σ ((loc_1 val_1) ...) ((x_1 loc_2) ...)
         (in-hole E (let [x val] e)))
        (σ ((loc_1 val_1) ... (loc_new val)) ((x loc_new) (x_1 loc_2) ...)
         (in-hole E e))
        "E-Let"
        (fresh loc_new))

   (--> (σ [(loc_1 val_1) ...] [(x_1 loc_2) ...]
         (in-hole E (rec [f (λ (x ...) e_1)] e)))
        (σ [(loc_1 val_1) ... (loc ([(f loc) (x_1 loc_2) ...] : (λ (x ...) e_1)))]
          [(f loc) (x_1 loc_2) ...]
          (in-hole E e))
        "E-Rec")

   (--> (σ [(loc_1 val_1) ...] Γ
         (in-hole E (([(y loc_3) ...] : (λ (x ...) e)) val_2 ...)))
        (σ [(loc_1 val_1) ... (loc val_2) ...]
           [(x loc) ... (y loc_3) ...]
         (in-hole E e))
        "E-Beta"
        (fresh ((loc ...) (val_2 ...)))
        (side-condition (= (length (term (val_2 ...)))
                           (length (term (x ...))))))

   (--> (σ Σ Γ (in-hole E (λ (x ...) e)))
        (σ Σ Γ (in-hole E (Γ : (λ (x ...) e))))
        "E-Γλ")

   (--> (σ
         [(loc_1 val_1) ... (loc val) (loc_2 val_2) ...]
         [(y loc_y) ... (x loc) (z loc_z) ...]
         (in-hole E (set! x val_new)))
        (σ
         [(loc_1 val_1) ... (loc val_new) (loc_2 val_2) ...]
         [(y loc_y) ... (x loc) (z loc_z) ...]
         (in-hole E val_new))
        "E-Set!")

   (--> (σ
         [(loc_1 val_1) ... (loc val) (loc_2 val_2) ...]
         [(y loc_y) ... (x loc) (z val_z) ...]
         (in-hole E x))
        (σ
         [(loc_1 val_1) ... (loc val) (loc_2 val_2) ...]
         [(y loc_y) ... (x loc) (z val_z) ...]
         (in-hole E val))
        (side-condition (not (member (term x) (term (y ...)))))
        "E-Ident")

   ;; Objects
   ;; -------
   (--> ([(ref obj) ...] Σ Γ (in-hole E (object obj-attrs [(string property) ...])))
        ([(ref_new (obj-attrs [(string property) ...])) (ref obj) ...] Σ Γ
         (in-hole E ref_new))
        (fresh ref_new))


   ;; Field Access
   (==> (get-field ref string val_args)
        (get-field2 ref ref string val_args)
        "E-GetField2")

   (--> ([(ref_first obj_first) ... 
          (ref (obj-attrs [(string_first property_first) ...
                (string [(@v val) (@w bool) (@c bool) (@e bool)])
                (string_rest property_rest) ...]))
          (ref_rest obj_rest) ...]
         Σ Γ
         (in-hole E (get-field2 ref ref_this string val_args)))
        ([(ref_first obj_first) ... 
          (ref (obj-attrs [(string_first property_first) ...
                (string [(@v val) (@w bool) (@c bool) (@e bool)])
                (string_rest property_rest) ...]))
          (ref_rest obj_rest) ...]
         Σ Γ
         (in-hole E val))
        "E-GetField-Found")

   (--> ([(ref_first obj_first) ... 
          (ref ([(obj-attr_1 val_1) ...
                 (proto ref_proto)
                 (obj-attr_2 val_2) ...]
                [(string_first property_first) ...]))
          (ref_rest obj_rest) ...]
        Σ Γ
        (in-hole E (get-field2 ref ref_this string val_args)))
;; -->
        ([(ref_first obj_first) ... 
          (ref ([(obj-attr_1 val_1) ...
                 (proto ref_proto)
                 (obj-attr_2 val_2) ...]
                [(string_first property_first) ...]))
          (ref_rest obj_rest) ...]
        Σ Γ
        (in-hole E (get-field2 ref_proto ref_this string val_args)))
       "E-GetField-Proto"
       (side-condition (not (member (term string) (term (string_first ...))))))

   (--> ([(ref_1 obj_1) ...
          (ref (obj-attrs
                [(string_1 property_1) ...
                 (string [(@g val_getter) (@s val_setter) (@c bool_1) (@e bool_2)])
                 (string_n property_n) ...]))
          (ref_n obj_n) ...]
         Σ Γ
         (in-hole E (get-field2 ref ref_this string val_args)))
;; -->
        ([(ref_1 obj_1) ...
          (ref (obj-attrs
                [(string_1 property_1) ...
                 (string [(@g val_getter) (@s val_setter) (@c bool_1) (@e bool_2)])
                 (string_n property_n) ...]))
          (ref_n obj_n) ...]
         Σ Γ
         (in-hole E (val_getter ref_this val_args)))
         "E-GetField-Getter")

   (--> ([(ref_1 obj_1) ...
          (ref ([(obj-attr_1 val_1) ...
                 (proto null)
                 (obj-attr_n val_n) ...]
                [(string property) ...]))
          (ref_n obj_n) ...]
         Σ Γ
         (in-hole E (get-field2 ref ref_this string_lookup val_args)))
;; -->
        ([(ref_1 obj_1) ...
          (ref ([(obj-attr_1 val_1) ...
                 (proto null)
                 (obj-attr_n val_n) ...]
                [(string property) ...]))
          (ref_n obj_n) ...]
         Σ Γ
         (in-hole E undefined))
         "E-GetField-Not-Found"
         (side-condition (not (member (term string_lookup) (term (string ...))))))


    ;; Field Update/Addition
    (==> (set-field ref string val_new val_args)
         (set-field2 ref ref string val_new val_args))

    (--> ([(ref_1 obj_1) ...
           (ref (obj-attrs
                 [(string_1 property_1) ...
                  (string [(@v val) (@w #t) (@c bool_1) (@e bool_1)])
                  (string_n property_n) ...]))
           (ref_n obj_n) ...]
          Σ Γ
          (in-hole E (set-field2 ref ref_this string val_new val_args)))
;; -->
         ([(ref_1 obj_1) ...
           (ref (obj-attrs
                 [(string_1 property_1) ...
                  (string [(@v val_new) (@w #t) (@c bool_1) (@e bool_1)])
                  (string_n property_n) ...]))
           (ref_n obj_n) ...]
          Σ Γ
          (in-hole E val_new))
          "E-SetField")

    (--> ([(ref_1 obj_1) ...
           (ref ([(obj-attr_1 val_1) ...
                  (extensible #t)
                  (obj-attr_n val_n) ...]
                 [(string property) ...]))
           (ref_n obj_n) ...]
          Σ Γ
          (in-hole E (set-field2 ref ref_this string_lookup val_new val_args)))
;; -->
         ([(ref_1 obj_1) ...
           (ref ([(obj-attr_1 val_1) ... (extensible #t) (obj-attr_n val_n) ...]
                 [(string_lookup [(@v val_new) (@w #t) (@c #t) (@e #t)])
                  (string property) ...]))
           (ref_n obj_n) ...]
          Σ Γ
          (in-hole E val_new))
         "E-SetField-Add"
         (side-condition (not (member (term string_lookup) (term (string ...))))))

    (--> ([(ref_1 obj_1) ...
           (ref ([(obj-attr val) ...]
                 [(string_1 property_1) ...
                  (string_x [(@g val_g) (@s val_s) (@c bool_c) (@e bool_e)])
                  (string_n property_n) ...]))
           (ref_n obj_n) ...]
          Σ Γ
          (in-hole E (set-field2 ref ref_this string_x val_new val_args)))
;; -->
         ([(ref_1 obj_1) ...
           (ref ([(obj-attr val) ...]
                 [(string_1 property_1) ...
                  (string_x [(@g val_g) (@s val_s) (@c bool_c) (@e bool_e)])
                  (string_n property_n) ...]))
           (ref_n obj_n) ...]
          Σ Γ
          (in-hole E (seq (val_s ref_this val_args)
                          val_new)))
        "E-SetField-Setter")

    ;; boring, standard stuff
    (==> (seq val_1 val_2) val_2 "E-Seq-Result")

    (==> (if #t e_1 e_2)
         e_1
         "E-If-True")

    (==> (if #f e_1 e_2)
         e_2
         "E-If-False")

    ;; labels
    
    ; join 
    (==> (join l_1 l_2) ⊤ "E-join-⊤" (side-condition (or (equal? (term l_1) (term ⊤))
                                                         (equal? (term l_2) (term ⊤)))))
    (==> (join l ⊥) l "E-join-⊥-1")
    (==> (join ⊥ l) l "E-join-⊥-2")
    ; meet
    (==> (meet l_1 l_2) any "E-meet-⊥" (side-condition (or (equal? (term l_1) (term ⊥))
                                                           (equal? (term l_2) (term ⊥)))))
    (==> (meet l ⊤) l "E-meet-⊤-1")
    (==> (meet ⊤ l) l "E-meet-⊤-2")
    ; canFlowTo
    (==> (canFlowTo l ⊤) #t "E-canFlowTo-x⊤")
    (==> (canFlowTo ⊥ l) #t "E-canFlowTo-⊥x")
    (==> (canFlowTo ⊤ ⊥) #f "E-canFlowTo-⊤⊥")

    with
    [(--> (σ Σ Γ (in-hole E e_1)) (σ Σ Γ (in-hole E e_2)))
     (==> e_1 e_2)]
))