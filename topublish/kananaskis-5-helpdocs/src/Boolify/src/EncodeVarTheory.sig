signature EncodeVarTheory =
sig
  type thm = Thm.thm
  
  (*  Definitions  *)
    val fixed_width_def : thm
    val of_length_def : thm
  
  (*  Theorems  *)
    val fixed_width_bnum : thm
    val fixed_width_bool : thm
    val fixed_width_exists : thm
    val fixed_width_prod : thm
    val fixed_width_sum : thm
    val fixed_width_unit : thm
    val fixed_width_univ : thm
    val of_length_exists_suc : thm
    val of_length_exists_zero : thm
    val of_length_univ_suc : thm
    val of_length_univ_zero : thm
  
  val EncodeVar_grammars : type_grammar.grammar * term_grammar.grammar
  
  
(*
   [Coder] Parent theory of "EncodeVar"
   
   [fixed_width_def]  Definition
      
      |- !n c.
           fixed_width n c <=>
           !x. domain c x ==> (LENGTH (encoder c x) = n)
   
   [of_length_def]  Definition
      
      |- !l n. l IN of_length n <=> (LENGTH l = n)
   
   [fixed_width_bnum]  Theorem
      
      |- !m p. fixed_width m (bnum_coder m p)
   
   [fixed_width_bool]  Theorem
      
      |- !p. fixed_width 1 (bool_coder p)
   
   [fixed_width_exists]  Theorem
      
      |- !phi c n.
           wf_coder c /\ fixed_width n c ==>
           ((?x. domain c x /\ phi x) <=>
            ?w::of_length n. phi (decoder c w))
   
   [fixed_width_prod]  Theorem
      
      |- !c1 c2 n1 n2.
           fixed_width n1 c1 /\ fixed_width n2 c2 ==>
           fixed_width (n1 + n2) (prod_coder c1 c2)
   
   [fixed_width_sum]  Theorem
      
      |- !c1 c2 n.
           fixed_width n c1 /\ fixed_width n c2 ==>
           fixed_width (SUC n) (sum_coder c1 c2)
   
   [fixed_width_unit]  Theorem
      
      |- !p. fixed_width 0 (unit_coder p)
   
   [fixed_width_univ]  Theorem
      
      |- !phi c n.
           wf_coder c /\ fixed_width n c ==>
           ((!x. domain c x ==> phi x) <=>
            !w::of_length n. phi (decoder c w))
   
   [of_length_exists_suc]  Theorem
      
      |- !phi n.
           (?w::of_length (SUC n). phi w) <=>
           ?x (w::of_length n). phi (x::w)
   
   [of_length_exists_zero]  Theorem
      
      |- !phi. (?w::of_length 0. phi w) <=> phi []
   
   [of_length_univ_suc]  Theorem
      
      |- !phi n.
           (!w::of_length (SUC n). phi w) <=>
           !x (w::of_length n). phi (x::w)
   
   [of_length_univ_zero]  Theorem
      
      |- !phi. (!w::of_length 0. phi w) <=> phi []
   
   
*)
end
