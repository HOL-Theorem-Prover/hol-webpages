signature numposrepTheory =
sig
  type thm = Thm.thm

  (*  Definitions  *)
    val l2n_def : thm
    val n2l_curried_def : thm
    val n2l_tupled_primitive_def : thm
    val num_from_bin_list_def : thm
    val num_from_dec_list_def : thm
    val num_from_hex_list_def : thm
    val num_from_oct_list_def : thm
    val num_to_bin_list_def : thm
    val num_to_dec_list_def : thm
    val num_to_hex_list_def : thm
    val num_to_oct_list_def : thm

  (*  Theorems  *)
    val DIV_0_IMP_LT : thm
    val EL_TAKE : thm
    val EL_n2l : thm
    val LENGTH_l2n : thm
    val LENGTH_n2l : thm
    val l2n_DIGIT : thm
    val l2n_lt : thm
    val l2n_n2l : thm
    val n2l_BOUND : thm
    val n2l_def : thm
    val n2l_ind : thm
    val n2l_l2n : thm

  val numposrep_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [logroot] Parent theory of "numposrep"

   [rich_list] Parent theory of "numposrep"

   [l2n_def]  Definition

      |- (∀b. l2n b [] = 0) ∧ ∀b h t. l2n b (h::t) = h MOD b + b * l2n b t

   [n2l_curried_def]  Definition

      |- ∀x x1. n2l x x1 = n2l_tupled (x,x1)

   [n2l_tupled_primitive_def]  Definition

      |- n2l_tupled =
         WFREC (@R. WF R ∧ ∀b n. ¬(n < b ∨ b < 2) ⇒ R (b,n DIV b) (b,n))
           (λn2l_tupled a.
              case a of
                (b,n) =>
                  I
                    (if n < b ∨ b < 2 then
                       [n MOD b]
                     else
                       n MOD b::n2l_tupled (b,n DIV b)))

   [num_from_bin_list_def]  Definition

      |- num_from_bin_list = l2n 2

   [num_from_dec_list_def]  Definition

      |- num_from_dec_list = l2n 10

   [num_from_hex_list_def]  Definition

      |- num_from_hex_list = l2n 16

   [num_from_oct_list_def]  Definition

      |- num_from_oct_list = l2n 8

   [num_to_bin_list_def]  Definition

      |- num_to_bin_list = n2l 2

   [num_to_dec_list_def]  Definition

      |- num_to_dec_list = n2l 10

   [num_to_hex_list_def]  Definition

      |- num_to_hex_list = n2l 16

   [num_to_oct_list_def]  Definition

      |- num_to_oct_list = n2l 8

   [DIV_0_IMP_LT]  Theorem

      |- ∀b n. 1 < b ∧ (n DIV b = 0) ⇒ n < b

   [EL_TAKE]  Theorem

      |- ∀x n l. x < n ∧ n ≤ LENGTH l ⇒ (EL x (TAKE n l) = EL x l)

   [EL_n2l]  Theorem

      |- ∀b x n.
           1 < b ∧ x < LENGTH (n2l b n) ⇒
           (EL x (n2l b n) = (n DIV b ** x) MOD b)

   [LENGTH_l2n]  Theorem

      |- ∀b l.
           1 < b ∧ EVERY ($> b) l ∧ l2n b l ≠ 0 ⇒
           SUC (LOG b (l2n b l)) ≤ LENGTH l

   [LENGTH_n2l]  Theorem

      |- ∀b n.
           1 < b ⇒ (LENGTH (n2l b n) = if n = 0 then 1 else SUC (LOG b n))

   [l2n_DIGIT]  Theorem

      |- ∀b l x.
           1 < b ∧ EVERY ($> b) l ∧ x < LENGTH l ⇒
           ((l2n b l DIV b ** x) MOD b = EL x l)

   [l2n_lt]  Theorem

      |- ∀l b. 0 < b ⇒ l2n b l < b ** LENGTH l

   [l2n_n2l]  Theorem

      |- ∀b n. 1 < b ⇒ (l2n b (n2l b n) = n)

   [n2l_BOUND]  Theorem

      |- ∀b n. 0 < b ⇒ EVERY ($> b) (n2l b n)

   [n2l_def]  Theorem

      |- ∀n b.
           n2l b n =
           if n < b ∨ b < 2 then [n MOD b] else n MOD b::n2l b (n DIV b)

   [n2l_ind]  Theorem

      |- ∀P.
           (∀b n. (¬(n < b ∨ b < 2) ⇒ P b (n DIV b)) ⇒ P b n) ⇒
           ∀v v1. P v v1

   [n2l_l2n]  Theorem

      |- ∀b l.
           1 < b ∧ EVERY ($> b) l ⇒
           (n2l b (l2n b l) =
            if l2n b l = 0 then [0] else TAKE (SUC (LOG b (l2n b l))) l)


*)
end
