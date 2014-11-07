signature CoderTheory =
sig
  type thm = Thm.thm

  (*  Definitions  *)
    val blist_coder_def : thm
    val bnum_coder_def : thm
    val bool_coder_def : thm
    val decode_def : thm
    val decoder_def : thm
    val domain_def : thm
    val encoder_def : thm
    val list_coder_def : thm
    val num_coder_def : thm
    val option_coder_def : thm
    val prod_coder_def : thm
    val sum_coder_def : thm
    val tree_coder_def : thm
    val unit_coder_def : thm
    val wf_coder_def : thm

  (*  Theorems  *)
    val decode_encode : thm
    val wf_coder : thm
    val wf_coder_blist : thm
    val wf_coder_bnum : thm
    val wf_coder_bool : thm
    val wf_coder_closed : thm
    val wf_coder_list : thm
    val wf_coder_num : thm
    val wf_coder_op : thm
    val wf_coder_option : thm
    val wf_coder_prod : thm
    val wf_coder_sum : thm
    val wf_coder_tree : thm
    val wf_coder_unit : thm

  val Coder_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [Decode] Parent theory of "Coder"

   [blist_coder_def]  Definition

      |- ∀m p e d.
           blist_coder m (p,e,d) =
           (lift_blist m p,encode_blist m e,
            decode_blist (lift_blist m p) m d)

   [bnum_coder_def]  Definition

      |- ∀m p. bnum_coder m p = (p,encode_bnum m,decode_bnum m p)

   [bool_coder_def]  Definition

      |- ∀p. bool_coder p = (p,encode_bool,decode_bool p)

   [decode_def]  Definition

      |- ∀p d l.
           decode p d l = case d l of NONE => @x. p x | SOME (x,v2) => x

   [decoder_def]  Definition

      |- ∀p e d. decoder (p,e,d) = decode p d

   [domain_def]  Definition

      |- ∀p e d. domain (p,e,d) = p

   [encoder_def]  Definition

      |- ∀p e d. encoder (p,e,d) = e

   [list_coder_def]  Definition

      |- ∀p e d.
           list_coder (p,e,d) =
           (EVERY p,encode_list e,decode_list (EVERY p) d)

   [num_coder_def]  Definition

      |- ∀p. num_coder p = (p,encode_num,decode_num p)

   [option_coder_def]  Definition

      |- ∀p e d.
           option_coder (p,e,d) =
           (lift_option p,encode_option e,decode_option (lift_option p) d)

   [prod_coder_def]  Definition

      |- ∀p1 e1 d1 p2 e2 d2.
           prod_coder (p1,e1,d1) (p2,e2,d2) =
           (lift_prod p1 p2,encode_prod e1 e2,
            decode_prod (lift_prod p1 p2) d1 d2)

   [sum_coder_def]  Definition

      |- ∀p1 e1 d1 p2 e2 d2.
           sum_coder (p1,e1,d1) (p2,e2,d2) =
           (lift_sum p1 p2,encode_sum e1 e2,
            decode_sum (lift_sum p1 p2) d1 d2)

   [tree_coder_def]  Definition

      |- ∀p e d.
           tree_coder (p,e,d) =
           (lift_tree p,encode_tree e,decode_tree (lift_tree p) d)

   [unit_coder_def]  Definition

      |- ∀p. unit_coder p = (p,encode_unit,decode_unit p)

   [wf_coder_def]  Definition

      |- ∀p e d.
           wf_coder (p,e,d) ⇔
           wf_pred p ∧ wf_encoder p e ∧ (d = enc2dec p e)

   [decode_encode]  Theorem

      |- ∀p e x. wf_encoder p e ∧ p x ⇒ (decode p (enc2dec p e) (e x) = x)

   [wf_coder]  Theorem

      |- ∀c. wf_coder c ⇒ ∀x. domain c x ⇒ (decoder c (encoder c x) = x)

   [wf_coder_blist]  Theorem

      |- ∀m c. wf_coder c ⇒ wf_coder (blist_coder m c)

   [wf_coder_bnum]  Theorem

      |- ∀m p. wf_pred_bnum m p ⇒ wf_coder (bnum_coder m p)

   [wf_coder_bool]  Theorem

      |- ∀p. wf_pred p ⇒ wf_coder (bool_coder p)

   [wf_coder_closed]  Theorem

      |- ∀c. wf_coder c ⇒ ∀l. domain c (decoder c l)

   [wf_coder_list]  Theorem

      |- ∀c. wf_coder c ⇒ wf_coder (list_coder c)

   [wf_coder_num]  Theorem

      |- ∀p. wf_pred p ⇒ wf_coder (num_coder p)

   [wf_coder_op]  Theorem

      |- ∀p e f.
           (∃x. p x) ∧ wf_encoder p e ∧ (∀x. p x ⇒ (e x = f x)) ⇒
           wf_coder (p,e,enc2dec p f)

   [wf_coder_option]  Theorem

      |- ∀c. wf_coder c ⇒ wf_coder (option_coder c)

   [wf_coder_prod]  Theorem

      |- ∀c1 c2. wf_coder c1 ∧ wf_coder c2 ⇒ wf_coder (prod_coder c1 c2)

   [wf_coder_sum]  Theorem

      |- ∀c1 c2. wf_coder c1 ∧ wf_coder c2 ⇒ wf_coder (sum_coder c1 c2)

   [wf_coder_tree]  Theorem

      |- ∀c. wf_coder c ⇒ wf_coder (tree_coder c)

   [wf_coder_unit]  Theorem

      |- ∀p. wf_pred p ⇒ wf_coder (unit_coder p)


*)
end
