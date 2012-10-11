signature basis_emitTheory =
sig
  type thm = Thm.thm

  (*  Axioms  *)
    val EXPi : thm
    val MULi : thm
    val SUMi : thm
    val dimindexi : thm

  (*  Definitions  *)
    val FCPi_primitive_def : thm
    val IS_EMPTY_def : thm
    val fromNum_primitive_def : thm
    val i2w_itself_primitive_def : thm
    val mk_fcp_def : thm
    val neg_int_of_num_def : thm
    val sw2sw_itself_def : thm
    val w2w_itself_def : thm
    val word_concat_itself_def : thm
    val word_eq_def : thm
    val word_extract_itself_def : thm
    val word_index_def : thm

  (*  Theorems  *)
    val FCPi_def : thm
    val FCPi_ind : thm
    val IS_EMPTY_REWRITE : thm
    val fromNum_def : thm
    val fromNum_ind : thm
    val i2w_itself_def : thm
    val i2w_itself_ind : thm

  val basis_emit_grammars : type_grammar.grammar * term_grammar.grammar

  val WORDS_EMIT_RULE : thm -> thm

(*
   [finite_map] Parent theory of "basis_emit"

   [integer_word] Parent theory of "basis_emit"

   [sorting] Parent theory of "basis_emit"

   [EXPi]  Axiom

      [oracles: ] [axioms: EXPi] []
      |- EXPi (ITSELF a,ITSELF b) = ITSELF (a ** b)

   [MULi]  Axiom

      [oracles: ] [axioms: MULi] []
      |- MULi (ITSELF a,ITSELF b) = ITSELF (a * b)

   [SUMi]  Axiom

      [oracles: ] [axioms: SUMi] []
      |- SUMi (ITSELF a,ITSELF b) = ITSELF (a + b)

   [dimindexi]  Axiom

      [oracles: ] [axioms: dimindexi] [] |- dimindex (ITSELF a) = a

   [FCPi_primitive_def]  Definition

      |- FCPi =
         WFREC (@R. WF R) (λFCPi a. case a of (f,(:β)) => I ($FCP f))

   [IS_EMPTY_def]  Definition

      |- ∀s. IS_EMPTY s ⇔ if s = ∅ then T else F

   [fromNum_primitive_def]  Definition

      |- fromNum =
         WFREC (@R. WF R)
           (λfromNum a.
              case a of
                (n,(:α)) => I (n2w_itself (n MOD dimword (:α),(:α))))

   [i2w_itself_primitive_def]  Definition

      |- i2w_itself =
         WFREC (@R. WF R) (λi2w_itself a. case a of (i,(:α)) => I (i2w i))

   [mk_fcp_def]  Definition

      |- mk_fcp = FCPi

   [neg_int_of_num_def]  Definition

      |- ∀n. neg_int_of_num n = -int_of_num (n + 1)

   [sw2sw_itself_def]  Definition

      |- ∀w. sw2sw_itself (:α) w = sw2sw w

   [w2w_itself_def]  Definition

      |- ∀w. w2w_itself (:α) w = w2w w

   [word_concat_itself_def]  Definition

      |- ∀v w. word_concat_itself (:α) v w = v @@ w

   [word_eq_def]  Definition

      |- ∀v w. word_eq v w ⇔ (v = w)

   [word_extract_itself_def]  Definition

      |- ∀h l w. word_extract_itself (:α) h l w = (h >< l) w

   [word_index_def]  Definition

      |- ∀w n. word_index w n ⇔ w ' n

   [FCPi_def]  Theorem

      |- FCPi (f,(:β)) = $FCP f

   [FCPi_ind]  Theorem

      |- ∀P. (∀f. P (f,(:β))) ⇒ ∀v v1. P (v,v1)

   [IS_EMPTY_REWRITE]  Theorem

      |- ((s = ∅) ⇔ IS_EMPTY s) ∧ ((∅ = s) ⇔ IS_EMPTY s)

   [fromNum_def]  Theorem

      |- fromNum (n,(:α)) = n2w_itself (n MOD dimword (:α),(:α))

   [fromNum_ind]  Theorem

      |- ∀P. (∀n. P (n,(:α))) ⇒ ∀v v1. P (v,v1)

   [i2w_itself_def]  Theorem

      |- i2w_itself (i,(:α)) = i2w i

   [i2w_itself_ind]  Theorem

      |- ∀P. (∀i. P (i,(:α))) ⇒ ∀v v1. P (v,v1)


*)
end
