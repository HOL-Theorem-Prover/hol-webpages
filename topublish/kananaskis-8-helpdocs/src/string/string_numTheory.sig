signature string_numTheory =
sig
  type thm = Thm.thm

  (*  Definitions  *)
    val n2s_primitive_def : thm
    val s2n_def : thm

  (*  Theorems  *)
    val n2s_11 : thm
    val n2s_def : thm
    val n2s_ind : thm
    val n2s_onto : thm
    val n2s_s2n : thm
    val s2n_11 : thm
    val s2n_n2s : thm
    val s2n_onto : thm

  val string_num_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [string] Parent theory of "string_num"

   [n2s_primitive_def]  Definition

      |- n2s =
         WFREC
           (@R.
              WF R ∧
              ∀n r0 r.
                n ≠ 0 ∧ (r0 = n MOD 256) ∧
                (r = if r0 = 0 then 256 else r0) ⇒
                R ((n − r) DIV 256) n)
           (λn2s n.
              I
                (if n = 0 then
                   ""
                 else
                   (let r0 = n MOD 256 in
                    let r = if r0 = 0 then 256 else r0 in
                    let s0 = n2s ((n − r) DIV 256)
                    in
                      STRING (CHR (r − 1)) s0)))

   [s2n_def]  Definition

      |- (s2n "" = 0) ∧ ∀c s. s2n (STRING c s) = s2n s * 256 + ORD c + 1

   [n2s_11]  Theorem

      |- (n2s x = n2s y) ⇔ (x = y)

   [n2s_def]  Theorem

      |- ∀n.
           n2s n =
           if n = 0 then
             ""
           else
             (let r0 = n MOD 256 in
              let r = if r0 = 0 then 256 else r0 in
              let s0 = n2s ((n − r) DIV 256)
              in
                STRING (CHR (r − 1)) s0)

   [n2s_ind]  Theorem

      |- ∀P.
           (∀n.
              (∀r0 r.
                 n ≠ 0 ∧ (r0 = n MOD 256) ∧
                 (r = if r0 = 0 then 256 else r0) ⇒
                 P ((n − r) DIV 256)) ⇒
              P n) ⇒
           ∀v. P v

   [n2s_onto]  Theorem

      |- ∀s. ∃n. s = n2s n

   [n2s_s2n]  Theorem

      |- n2s (s2n s) = s

   [s2n_11]  Theorem

      |- (s2n x = s2n y) ⇔ (x = y)

   [s2n_n2s]  Theorem

      |- ∀n. s2n (n2s n) = n

   [s2n_onto]  Theorem

      |- ∀n. ∃s. n = s2n s


*)
end
