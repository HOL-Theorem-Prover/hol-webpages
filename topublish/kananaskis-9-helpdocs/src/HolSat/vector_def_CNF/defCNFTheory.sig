signature defCNFTheory =
sig
  type thm = Thm.thm

  (*  Definitions  *)
    val DEF_def : thm
    val OKDEF_def : thm
    val OK_curried_def : thm
    val OK_tupled_primitive_def : thm
    val UNIQUE_curried_def : thm
    val UNIQUE_tupled_primitive_def : thm

  (*  Theorems  *)
    val BIGSTEP : thm
    val CONSISTENCY : thm
    val DEF_SNOC : thm
    val FINAL_DEF : thm
    val OKDEF_SNOC : thm
    val OK_def : thm
    val OK_ind : thm
    val UNIQUE_def : thm
    val UNIQUE_ind : thm

  val defCNF_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [rich_list] Parent theory of "defCNF"

   [DEF_def]  Definition

      |- (∀v n. defCNF$DEF v n [] ⇔ T) ∧
         ∀v n x xs.
           defCNF$DEF v n (x::xs) ⇔
           defCNF$UNIQUE v n x ∧ defCNF$DEF v (SUC n) xs

   [OKDEF_def]  Definition

      |- (∀n. defCNF$OKDEF n [] ⇔ T) ∧
         ∀n x xs.
           defCNF$OKDEF n (x::xs) ⇔ defCNF$OK n x ∧ defCNF$OKDEF (SUC n) xs

   [OK_curried_def]  Definition

      |- ∀x x1. defCNF$OK x x1 ⇔ OK_tupled (x,x1)

   [OK_tupled_primitive_def]  Definition

      |- OK_tupled =
         WFREC (@R. WF R)
           (λOK_tupled a'.
              case a' of
                (n,conn,INL i,INL j) => I (i < n ∧ j < n)
              | (n,conn,INL i,INR b) => I (i < n)
              | (n,conn,INR a,INL j') => I (j' < n)
              | (n,conn,INR a,INR b') => I T)

   [UNIQUE_curried_def]  Definition

      |- ∀x x1 x2. defCNF$UNIQUE x x1 x2 ⇔ UNIQUE_tupled (x,x1,x2)

   [UNIQUE_tupled_primitive_def]  Definition

      |- UNIQUE_tupled =
         WFREC (@R. WF R)
           (λUNIQUE_tupled a'.
              case a' of
                (v,n,conn,INL i,INL j) => I (v n ⇔ conn (v i) (v j))
              | (v,n,conn,INL i,INR b) => I (v n ⇔ conn (v i) b)
              | (v,n,conn,INR a,INL j') => I (v n ⇔ conn a (v j'))
              | (v,n,conn,INR a,INR b') => I (v n ⇔ conn a b'))

   [BIGSTEP]  Theorem

      |- ∀P Q R. (∀v. P v ⇒ (Q ⇔ R v)) ⇒ ((∃v. P v) ∧ Q ⇔ ∃v. P v ∧ R v)

   [CONSISTENCY]  Theorem

      |- ∀n l. defCNF$OKDEF n l ⇒ ∃v. defCNF$DEF v n l

   [DEF_SNOC]  Theorem

      |- ∀n x l v.
           defCNF$DEF v n (SNOC x l) ⇔
           defCNF$DEF v n l ∧ defCNF$UNIQUE v (n + LENGTH l) x

   [FINAL_DEF]  Theorem

      |- ∀v n x. (v n ⇔ x) ⇔ (v n ⇔ x) ∧ defCNF$DEF v (SUC n) []

   [OKDEF_SNOC]  Theorem

      |- ∀n x l.
           defCNF$OKDEF n (SNOC x l) ⇔
           defCNF$OKDEF n l ∧ defCNF$OK (n + LENGTH l) x

   [OK_def]  Theorem

      |- (defCNF$OK n (conn,INL i,INL j) ⇔ i < n ∧ j < n) ∧
         (defCNF$OK n (conn,INL i,INR b) ⇔ i < n) ∧
         (defCNF$OK n (conn,INR a,INL j) ⇔ j < n) ∧
         (defCNF$OK n (conn,INR a,INR b) ⇔ T)

   [OK_ind]  Theorem

      |- ∀P.
           (∀n conn i j. P n (conn,INL i,INL j)) ∧
           (∀n conn i b. P n (conn,INL i,INR b)) ∧
           (∀n conn a j. P n (conn,INR a,INL j)) ∧
           (∀n conn a b. P n (conn,INR a,INR b)) ⇒
           ∀v v1 v2 v3. P v (v1,v2,v3)

   [UNIQUE_def]  Theorem

      |- (defCNF$UNIQUE v n (conn,INL i,INL j) ⇔
          (v n ⇔ conn (v i) (v j))) ∧
         (defCNF$UNIQUE v n (conn,INL i,INR b) ⇔ (v n ⇔ conn (v i) b)) ∧
         (defCNF$UNIQUE v n (conn,INR a,INL j) ⇔ (v n ⇔ conn a (v j))) ∧
         (defCNF$UNIQUE v n (conn,INR a,INR b) ⇔ (v n ⇔ conn a b))

   [UNIQUE_ind]  Theorem

      |- ∀P.
           (∀v n conn i j. P v n (conn,INL i,INL j)) ∧
           (∀v n conn i b. P v n (conn,INL i,INR b)) ∧
           (∀v n conn a j. P v n (conn,INR a,INL j)) ∧
           (∀v n conn a b. P v n (conn,INR a,INR b)) ⇒
           ∀v v1 v2 v3 v4. P v v1 (v2,v3,v4)


*)
end
