signature mergesortTheory =
sig
  type thm = Thm.thm

  (*  Definitions  *)
    val merge_curried_def : thm
    val merge_tail_curried_def : thm
    val merge_tail_tupled_primitive_def : thm
    val merge_tupled_primitive_def : thm
    val mergesortN_curried_def : thm
    val mergesortN_tail_curried_def : thm
    val mergesortN_tail_tupled_primitive_def : thm
    val mergesortN_tupled_primitive_def : thm
    val mergesort_def : thm
    val mergesort_tail_def : thm
    val sort2_def : thm
    val sort2_tail_def : thm
    val sort3_def : thm
    val sort3_tail_def : thm
    val stable_def : thm

  (*  Theorems  *)
    val filter_merge : thm
    val merge_def : thm
    val merge_empty : thm
    val merge_ind : thm
    val merge_perm : thm
    val merge_sorted : thm
    val merge_stable : thm
    val merge_tail_correct1 : thm
    val merge_tail_correct2 : thm
    val merge_tail_def : thm
    val merge_tail_ind : thm
    val mergesortN_correct : thm
    val mergesortN_def : thm
    val mergesortN_ind : thm
    val mergesortN_perm : thm
    val mergesortN_sorted : thm
    val mergesortN_stable : thm
    val mergesortN_tail_def : thm
    val mergesortN_tail_ind : thm
    val mergesort_STABLE_SORT : thm
    val mergesort_mem : thm
    val mergesort_perm : thm
    val mergesort_sorted : thm
    val mergesort_stable : thm
    val mergesort_tail_correct : thm
    val sort2_perm : thm
    val sort2_sorted : thm
    val sort2_stable : thm
    val sort2_tail_correct : thm
    val sort3_perm : thm
    val sort3_sorted : thm
    val sort3_stable : thm
    val sort3_tail_correct : thm
    val stable_cong : thm
    val stable_trans : thm

  val mergesort_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [quantHeuristics] Parent theory of "mergesort"

   [sorting] Parent theory of "mergesort"

   [merge_curried_def]  Definition

      |- ∀x x1 x2. merge x x1 x2 = merge_tupled (x,x1,x2)

   [merge_tail_curried_def]  Definition

      |- ∀x x1 x2 x3 x4.
           merge_tail x x1 x2 x3 x4 = merge_tail_tupled (x,x1,x2,x3,x4)

   [merge_tail_tupled_primitive_def]  Definition

      |- merge_tail_tupled =
         WFREC
           (@R'.
              WF R' ∧
              (∀acc l2 l1 negate y x R.
                 ¬(R x y ⇎ negate) ⇒
                 R' (negate,R,x::l1,l2,y::acc)
                   (negate,R,x::l1,y::l2,acc)) ∧
              ∀acc l2 l1 negate y x R.
                (R x y ⇎ negate) ⇒
                R' (negate,R,l1,y::l2,x::acc) (negate,R,x::l1,y::l2,acc))
           (λmerge_tail_tupled a.
              case a of
                (negate,R,[],[],acc) => I acc
              | (negate,R,v14::v15,[],acc) => I (REV (v14::v15) acc)
              | (negate,R,[],y::l2,acc) => I (REV (y::l2) acc)
              | (negate,R,x::l1,y::l2,acc) =>
                  I
                    (if R x y ⇎ negate then
                       merge_tail_tupled (negate,R,l1,y::l2,x::acc)
                     else merge_tail_tupled (negate,R,x::l1,l2,y::acc)))

   [merge_tupled_primitive_def]  Definition

      |- merge_tupled =
         WFREC
           (@R'.
              WF R' ∧
              (∀l2 l1 y x R. ¬R x y ⇒ R' (R,x::l1,l2) (R,x::l1,y::l2)) ∧
              ∀l2 l1 y x R. R x y ⇒ R' (R,l1,y::l2) (R,x::l1,y::l2))
           (λmerge_tupled a.
              case a of
                (R,[],[]) => I []
              | (R,v10::v11,[]) => I (v10::v11)
              | (R,[],y::l2) => I (y::l2)
              | (R,x::l1,y::l2) =>
                  I
                    (if R x y then x::merge_tupled (R,l1,y::l2)
                     else y::merge_tupled (R,x::l1,l2)))

   [mergesortN_curried_def]  Definition

      |- ∀x x1 x2. mergesortN x x1 x2 = mergesortN_tupled (x,x1,x2)

   [mergesortN_tail_curried_def]  Definition

      |- ∀x x1 x2 x3.
           mergesortN_tail x x1 x2 x3 = mergesortN_tail_tupled (x,x1,x2,x3)

   [mergesortN_tail_tupled_primitive_def]  Definition

      |- mergesortN_tail_tupled =
         WFREC
           (@R'.
              WF R' ∧
              (∀l R negate v6 len1 neg.
                 v6 ≠ 0 ∧ v6 ≠ 1 ∧ v6 ≠ 2 ∧ v6 ≠ 3 ∧ len1 = DIV2 v6 ∧
                 (neg ⇔ ¬negate) ⇒
                 R' (neg,R,DIV2 v6,l) (negate,R,v6,l)) ∧
              ∀l R negate v6 len1 neg.
                v6 ≠ 0 ∧ v6 ≠ 1 ∧ v6 ≠ 2 ∧ v6 ≠ 3 ∧ len1 = DIV2 v6 ∧
                (neg ⇔ ¬negate) ⇒
                R' (neg,R,v6 − len1,DROP len1 l) (negate,R,v6,l))
           (λmergesortN_tail_tupled a.
              case a of
                (negate,R,0,l) => I []
              | (negate,R,1,[]) => I []
              | (negate,R,1,x::l') => I [x]
              | (negate,R,2,[]) => I []
              | (negate,R,2,[x']) => I [x']
              | (negate,R,2,x'::y::l'') => I (sort2_tail negate R x' y)
              | (negate,R,3,[]) => I []
              | (negate,R,3,[x'']) => I [x'']
              | (negate,R,3,[x''; y']) => I (sort2_tail negate R x'' y')
              | (negate,R,3,x''::y'::z::l''') =>
                  I (sort3_tail negate R x'' y' z)
              | (negate,R,n,l) =>
                  I
                    (let len1 = DIV2 n in
                     let neg = ¬negate
                     in
                       merge_tail neg R
                         (mergesortN_tail_tupled (neg,R,DIV2 n,l))
                         (mergesortN_tail_tupled
                            (neg,R,n − len1,DROP len1 l)) []))

   [mergesortN_tupled_primitive_def]  Definition

      |- mergesortN_tupled =
         WFREC
           (@R'.
              WF R' ∧
              (∀l R v4 len1.
                 v4 ≠ 0 ∧ v4 ≠ 1 ∧ v4 ≠ 2 ∧ v4 ≠ 3 ∧ len1 = DIV2 v4 ⇒
                 R' (R,DIV2 v4,l) (R,v4,l)) ∧
              ∀l R v4 len1.
                v4 ≠ 0 ∧ v4 ≠ 1 ∧ v4 ≠ 2 ∧ v4 ≠ 3 ∧ len1 = DIV2 v4 ⇒
                R' (R,v4 − len1,DROP len1 l) (R,v4,l))
           (λmergesortN_tupled a.
              case a of
                (R,0,l) => I []
              | (R,1,[]) => I []
              | (R,1,x::l') => I [x]
              | (R,2,[]) => I []
              | (R,2,[x']) => I [x']
              | (R,2,x'::y::l'') => I (sort2 R x' y)
              | (R,3,[]) => I []
              | (R,3,[x'']) => I [x'']
              | (R,3,[x''; y']) => I (sort2 R x'' y')
              | (R,3,x''::y'::z::l''') => I (sort3 R x'' y' z)
              | (R,n,l) =>
                  I
                    (let len1 = DIV2 n
                     in
                       merge R (mergesortN_tupled (R,DIV2 n,l))
                         (mergesortN_tupled (R,n − len1,DROP len1 l))))

   [mergesort_def]  Definition

      |- ∀R l. mergesort R l = mergesortN R (LENGTH l) l

   [mergesort_tail_def]  Definition

      |- ∀R l. mergesort_tail R l = mergesortN_tail F R (LENGTH l) l

   [sort2_def]  Definition

      |- ∀R x y. sort2 R x y = if R x y then [x; y] else [y; x]

   [sort2_tail_def]  Definition

      |- ∀neg R x y.
           sort2_tail neg R x y = if R x y ⇎ neg then [x; y] else [y; x]

   [sort3_def]  Definition

      |- ∀R x y z.
           sort3 R x y z =
           if R x y then
             if R y z then [x; y; z]
             else if R x z then [x; z; y]
             else [z; x; y]
           else if R y z then if R x z then [y; x; z] else [y; z; x]
           else [z; y; x]

   [sort3_tail_def]  Definition

      |- ∀neg R x y z.
           sort3_tail neg R x y z =
           if R x y ⇎ neg then
             if R y z ⇎ neg then [x; y; z]
             else if R x z ⇎ neg then [x; z; y]
             else [z; x; y]
           else if R y z ⇎ neg then
             if R x z ⇎ neg then [y; x; z] else [y; z; x]
           else [z; y; x]

   [stable_def]  Definition

      |- ∀R l1 l2.
           stable R l1 l2 ⇔
           ∀p. (∀x y. p x ∧ p y ⇒ R x y) ⇒ FILTER p l1 = FILTER p l2

   [filter_merge]  Theorem

      |- ∀P R l1 l2.
           transitive R ∧ (∀x y. P x ∧ P y ⇒ R x y) ∧ SORTED R l1 ⇒
           FILTER P (merge R l1 l2) = FILTER P (l1 ++ l2)

   [merge_def]  Theorem

      |- (∀R. merge R [] [] = []) ∧
         (∀v9 v8 R. merge R (v8::v9) [] = v8::v9) ∧
         (∀v5 v4 R. merge R [] (v4::v5) = v4::v5) ∧
         ∀y x l2 l1 R.
           merge R (x::l1) (y::l2) =
           if R x y then x::merge R l1 (y::l2) else y::merge R (x::l1) l2

   [merge_empty]  Theorem

      |- ∀R l acc. merge R l [] = l ∧ merge R [] l = l

   [merge_ind]  Theorem

      |- ∀P.
           (∀R. P R [] []) ∧ (∀R v8 v9. P R (v8::v9) []) ∧
           (∀R v4 v5. P R [] (v4::v5)) ∧
           (∀R x l1 y l2.
              (¬R x y ⇒ P R (x::l1) l2) ∧ (R x y ⇒ P R l1 (y::l2)) ⇒
              P R (x::l1) (y::l2)) ⇒
           ∀v v1 v2. P v v1 v2

   [merge_perm]  Theorem

      |- ∀R l1 l2. PERM (l1 ++ l2) (merge R l1 l2)

   [merge_sorted]  Theorem

      |- ∀R l1 l2.
           transitive R ∧ total R ∧ SORTED R l1 ∧ SORTED R l2 ⇒
           SORTED R (merge R l1 l2)

   [merge_stable]  Theorem

      |- ∀R l1 l2.
           transitive R ∧ SORTED R l1 ⇒ stable R (l1 ++ l2) (merge R l1 l2)

   [merge_tail_correct1]  Theorem

      |- ∀neg R l1 l2 acc.
           (neg ⇔ F) ⇒
           merge_tail neg R l1 l2 acc = REVERSE (merge R l1 l2) ++ acc

   [merge_tail_correct2]  Theorem

      |- ∀neg R l1 l2 acc.
           (neg ⇔ T) ∧ transitive R ∧ SORTED R (REVERSE l1) ∧
           SORTED R (REVERSE l2) ⇒
           merge_tail neg R l1 l2 acc =
           merge R (REVERSE l1) (REVERSE l2) ++ acc

   [merge_tail_def]  Theorem

      |- (∀negate acc R. merge_tail negate R [] [] acc = acc) ∧
         (∀v13 v12 negate acc R.
            merge_tail negate R (v12::v13) [] acc = REV (v12::v13) acc) ∧
         (∀v9 v8 negate acc R.
            merge_tail negate R [] (v8::v9) acc = REV (v8::v9) acc) ∧
         ∀y x negate l2 l1 acc R.
           merge_tail negate R (x::l1) (y::l2) acc =
           if R x y ⇎ negate then merge_tail negate R l1 (y::l2) (x::acc)
           else merge_tail negate R (x::l1) l2 (y::acc)

   [merge_tail_ind]  Theorem

      |- ∀P.
           (∀negate R acc. P negate R [] [] acc) ∧
           (∀negate R v12 v13 acc. P negate R (v12::v13) [] acc) ∧
           (∀negate R v8 v9 acc. P negate R [] (v8::v9) acc) ∧
           (∀negate R x l1 y l2 acc.
              (¬(R x y ⇎ negate) ⇒ P negate R (x::l1) l2 (y::acc)) ∧
              ((R x y ⇎ negate) ⇒ P negate R l1 (y::l2) (x::acc)) ⇒
              P negate R (x::l1) (y::l2) acc) ⇒
           ∀v v1 v2 v3 v4. P v v1 v2 v3 v4

   [mergesortN_correct]  Theorem

      |- ∀negate R n l.
           total R ∧ transitive R ⇒
           mergesortN_tail negate R n l =
           if negate then REVERSE (mergesortN R n l) else mergesortN R n l

   [mergesortN_def]  Theorem

      |- (∀l R. mergesortN R 0 l = []) ∧
         (∀x l R. mergesortN R 1 (x::l) = [x]) ∧
         (∀R. mergesortN R 1 [] = []) ∧
         (∀y x l R. mergesortN R 2 (x::y::l) = sort2 R x y) ∧
         (∀x R. mergesortN R 2 [x] = [x]) ∧ (∀R. mergesortN R 2 [] = []) ∧
         (∀z y x l R. mergesortN R 3 (x::y::z::l) = sort3 R x y z) ∧
         (∀y x R. mergesortN R 3 [x; y] = sort2 R x y) ∧
         (∀x R. mergesortN R 3 [x] = [x]) ∧ (∀R. mergesortN R 3 [] = []) ∧
         ∀v4 l R.
           mergesortN R v4 l =
           if v4 = 0 then []
           else if v4 = 1 then case l of [] => [] | x::l' => [x]
           else if v4 = 2 then
             case l of [] => [] | [x'] => [x'] | x'::y::l'' => sort2 R x' y
           else if v4 = 3 then
             case l of
               [] => []
             | [x''] => [x'']
             | [x''; y'] => sort2 R x'' y'
             | x''::y'::z::l''' => sort3 R x'' y' z
           else
             (let len1 = DIV2 v4
              in
                merge R (mergesortN R (DIV2 v4) l)
                  (mergesortN R (v4 − len1) (DROP len1 l)))

   [mergesortN_ind]  Theorem

      |- ∀P.
           (∀R l. P R 0 l) ∧ (∀R x l. P R 1 (x::l)) ∧ (∀R. P R 1 []) ∧
           (∀R x y l. P R 2 (x::y::l)) ∧ (∀R x. P R 2 [x]) ∧
           (∀R. P R 2 []) ∧ (∀R x y z l. P R 3 (x::y::z::l)) ∧
           (∀R x y. P R 3 [x; y]) ∧ (∀R x. P R 3 [x]) ∧ (∀R. P R 3 []) ∧
           (∀R v4 l.
              (∀len1.
                 v4 ≠ 0 ∧ v4 ≠ 1 ∧ v4 ≠ 2 ∧ v4 ≠ 3 ∧ len1 = DIV2 v4 ⇒
                 P R (DIV2 v4) l) ∧
              (∀len1.
                 v4 ≠ 0 ∧ v4 ≠ 1 ∧ v4 ≠ 2 ∧ v4 ≠ 3 ∧ len1 = DIV2 v4 ⇒
                 P R (v4 − len1) (DROP len1 l)) ⇒
              P R v4 l) ⇒
           ∀v v1 v2. P v v1 v2

   [mergesortN_perm]  Theorem

      |- ∀R n l. PERM (TAKE n l) (mergesortN R n l)

   [mergesortN_sorted]  Theorem

      |- ∀R n l. total R ∧ transitive R ⇒ SORTED R (mergesortN R n l)

   [mergesortN_stable]  Theorem

      |- ∀R n l.
           total R ∧ transitive R ⇒ stable R (TAKE n l) (mergesortN R n l)

   [mergesortN_tail_def]  Theorem

      |- (∀negate l R. mergesortN_tail negate R 0 l = []) ∧
         (∀x negate l R. mergesortN_tail negate R 1 (x::l) = [x]) ∧
         (∀negate R. mergesortN_tail negate R 1 [] = []) ∧
         (∀y x negate l R.
            mergesortN_tail negate R 2 (x::y::l) =
            sort2_tail negate R x y) ∧
         (∀x negate R. mergesortN_tail negate R 2 [x] = [x]) ∧
         (∀negate R. mergesortN_tail negate R 2 [] = []) ∧
         (∀z y x negate l R.
            mergesortN_tail negate R 3 (x::y::z::l) =
            sort3_tail negate R x y z) ∧
         (∀y x negate R.
            mergesortN_tail negate R 3 [x; y] = sort2_tail negate R x y) ∧
         (∀x negate R. mergesortN_tail negate R 3 [x] = [x]) ∧
         (∀negate R. mergesortN_tail negate R 3 [] = []) ∧
         ∀v6 negate l R.
           mergesortN_tail negate R v6 l =
           if v6 = 0 then []
           else if v6 = 1 then case l of [] => [] | x::l' => [x]
           else if v6 = 2 then
             case l of
               [] => []
             | [x'] => [x']
             | x'::y::l'' => sort2_tail negate R x' y
           else if v6 = 3 then
             case l of
               [] => []
             | [x''] => [x'']
             | [x''; y'] => sort2_tail negate R x'' y'
             | x''::y'::z::l''' => sort3_tail negate R x'' y' z
           else
             (let len1 = DIV2 v6 in
              let neg = ¬negate
              in
                merge_tail neg R (mergesortN_tail neg R (DIV2 v6) l)
                  (mergesortN_tail neg R (v6 − len1) (DROP len1 l)) [])

   [mergesortN_tail_ind]  Theorem

      |- ∀P.
           (∀negate R l. P negate R 0 l) ∧
           (∀negate R x l. P negate R 1 (x::l)) ∧
           (∀negate R. P negate R 1 []) ∧
           (∀negate R x y l. P negate R 2 (x::y::l)) ∧
           (∀negate R x. P negate R 2 [x]) ∧ (∀negate R. P negate R 2 []) ∧
           (∀negate R x y z l. P negate R 3 (x::y::z::l)) ∧
           (∀negate R x y. P negate R 3 [x; y]) ∧
           (∀negate R x. P negate R 3 [x]) ∧ (∀negate R. P negate R 3 []) ∧
           (∀negate R v6 l.
              (∀len1 neg.
                 v6 ≠ 0 ∧ v6 ≠ 1 ∧ v6 ≠ 2 ∧ v6 ≠ 3 ∧ len1 = DIV2 v6 ∧
                 (neg ⇔ ¬negate) ⇒
                 P neg R (DIV2 v6) l) ∧
              (∀len1 neg.
                 v6 ≠ 0 ∧ v6 ≠ 1 ∧ v6 ≠ 2 ∧ v6 ≠ 3 ∧ len1 = DIV2 v6 ∧
                 (neg ⇔ ¬negate) ⇒
                 P neg R (v6 − len1) (DROP len1 l)) ⇒
              P negate R v6 l) ⇒
           ∀v v1 v2 v3. P v v1 v2 v3

   [mergesort_STABLE_SORT]  Theorem

      |- ∀R. transitive R ∧ total R ⇒ STABLE mergesort R

   [mergesort_mem]  Theorem

      |- ∀R L x. MEM x (mergesort R L) ⇔ MEM x L

   [mergesort_perm]  Theorem

      |- ∀R l. PERM l (mergesort R l)

   [mergesort_sorted]  Theorem

      |- ∀R l. transitive R ∧ total R ⇒ SORTED R (mergesort R l)

   [mergesort_stable]  Theorem

      |- ∀R l. transitive R ∧ total R ⇒ stable R l (mergesort R l)

   [mergesort_tail_correct]  Theorem

      |- ∀R l. total R ∧ transitive R ⇒ mergesort_tail R l = mergesort R l

   [sort2_perm]  Theorem

      |- ∀R x y. PERM [x; y] (sort2 R x y)

   [sort2_sorted]  Theorem

      |- ∀R x y. total R ⇒ SORTED R (sort2 R x y)

   [sort2_stable]  Theorem

      |- ∀R x y. stable R [x; y] (sort2 R x y)

   [sort2_tail_correct]  Theorem

      |- ∀neg R x y.
           sort2_tail neg R x y =
           if neg then REVERSE (sort2 R x y) else sort2 R x y

   [sort3_perm]  Theorem

      |- ∀R x y z. PERM [x; y; z] (sort3 R x y z)

   [sort3_sorted]  Theorem

      |- ∀R x y z. total R ⇒ SORTED R (sort3 R x y z)

   [sort3_stable]  Theorem

      |- ∀R x y z.
           total R ∧ transitive R ⇒ stable R [x; y; z] (sort3 R x y z)

   [sort3_tail_correct]  Theorem

      |- ∀neg R x y z.
           sort3_tail neg R x y z =
           if neg then REVERSE (sort3 R x y z) else sort3 R x y z

   [stable_cong]  Theorem

      |- ∀R l1 l2 l3 l4.
           stable R l1 l2 ∧ stable R l3 l4 ⇒ stable R (l1 ++ l3) (l2 ++ l4)

   [stable_trans]  Theorem

      |- ∀R l1 l2 l3. stable R l1 l2 ∧ stable R l2 l3 ⇒ stable R l1 l3


*)
end
