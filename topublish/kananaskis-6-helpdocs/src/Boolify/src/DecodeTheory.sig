signature DecodeTheory =
sig
  type thm = Thm.thm
  
  (*  Definitions  *)
    val dec2enc_def : thm
    val dec_bnum_def : thm
    val decode_blist_def : thm
    val decode_bnum_def : thm
    val decode_bool_def : thm
    val decode_list_def : thm
    val decode_num_def : thm
    val decode_option_def : thm
    val decode_prod_def : thm
    val decode_sum_def : thm
    val decode_tree_def : thm
    val decode_unit_def : thm
    val enc2dec_def : thm
    val wf_decoder_def : thm
  
  (*  Theorems  *)
    val dec2enc_decode_blist : thm
    val dec2enc_decode_bnum : thm
    val dec2enc_decode_bool : thm
    val dec2enc_decode_list : thm
    val dec2enc_decode_num : thm
    val dec2enc_decode_option : thm
    val dec2enc_decode_prod : thm
    val dec2enc_decode_sum : thm
    val dec2enc_decode_unit : thm
    val dec2enc_enc2dec : thm
    val dec2enc_some : thm
    val dec_bnum_inj : thm
    val dec_bnum_lt : thm
    val decode_blist : thm
    val decode_bnum : thm
    val decode_bool : thm
    val decode_dec2enc : thm
    val decode_dec2enc_append : thm
    val decode_list : thm
    val decode_num : thm
    val decode_num_total : thm
    val decode_option : thm
    val decode_prod : thm
    val decode_sum : thm
    val decode_tree : thm
    val decode_unit : thm
    val enc2dec_dec2enc : thm
    val enc2dec_none : thm
    val enc2dec_some : thm
    val enc2dec_some_alt : thm
    val encode_then_decode_blist : thm
    val encode_then_decode_list : thm
    val encode_then_decode_option : thm
    val encode_then_decode_prod : thm
    val encode_then_decode_sum : thm
    val wf_dec2enc : thm
    val wf_decode_blist : thm
    val wf_decode_bnum : thm
    val wf_decode_bool : thm
    val wf_decode_list : thm
    val wf_decode_num : thm
    val wf_decode_option : thm
    val wf_decode_prod : thm
    val wf_decode_sum : thm
    val wf_decode_tree : thm
    val wf_decode_unit : thm
    val wf_enc2dec : thm
  
  val Decode_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [Encode] Parent theory of "Decode"
   
   [dec2enc_def]  Definition
      
      |- ∀d x. dec2enc d x = @l. d l = SOME (x,[])
   
   [dec_bnum_def]  Definition
      
      |- (∀l. dec_bnum 0 l = SOME (0,l)) ∧
         ∀m l.
           dec_bnum (SUC m) l =
           case l of
              [] -> NONE
           || h::t ->
                case dec_bnum m t of
                   NONE -> NONE
                || SOME (n,t') -> SOME (2 * n + if h then 1 else 0,t')
   
   [decode_blist_def]  Definition
      
      |- ∀p m d. decode_blist p m d = enc2dec p (encode_blist m (dec2enc d))
   
   [decode_bnum_def]  Definition
      
      |- ∀m p. decode_bnum m p = enc2dec p (encode_bnum m)
   
   [decode_bool_def]  Definition
      
      |- ∀p. decode_bool p = enc2dec p encode_bool
   
   [decode_list_def]  Definition
      
      |- ∀p d. decode_list p d = enc2dec p (encode_list (dec2enc d))
   
   [decode_num_def]  Definition
      
      |- ∀p. decode_num p = enc2dec p encode_num
   
   [decode_option_def]  Definition
      
      |- ∀p d. decode_option p d = enc2dec p (encode_option (dec2enc d))
   
   [decode_prod_def]  Definition
      
      |- ∀p d1 d2.
           decode_prod p d1 d2 = enc2dec p (encode_prod (dec2enc d1) (dec2enc d2))
   
   [decode_sum_def]  Definition
      
      |- ∀p d1 d2.
           decode_sum p d1 d2 = enc2dec p (encode_sum (dec2enc d1) (dec2enc d2))
   
   [decode_tree_def]  Definition
      
      |- ∀p d. decode_tree p d = enc2dec p (encode_tree (dec2enc d))
   
   [decode_unit_def]  Definition
      
      |- ∀p. decode_unit p = enc2dec p encode_unit
   
   [enc2dec_def]  Definition
      
      |- ∀p e l.
           enc2dec p e l =
           if ∃x t. p x ∧ (l = e x ++ t) then
             SOME (@(x,t). p x ∧ (l = e x ++ t))
           else
             NONE
   
   [wf_decoder_def]  Definition
      
      |- ∀p d.
           wf_decoder p d ⇔
           ∀x.
             if p x then
               ∃a. ∀b c. (d b = SOME (x,c)) ⇔ (b = a ++ c)
             else
               ∀a b. d a ≠ SOME (x,b)
   
   [dec2enc_decode_blist]  Theorem
      
      |- ∀m p d l.
           wf_decoder p d ∧ lift_blist m p l ⇒
           (dec2enc (decode_blist (lift_blist m p) m d) l =
            encode_blist m (dec2enc d) l)
   
   [dec2enc_decode_bnum]  Theorem
      
      |- ∀m p x.
           wf_pred_bnum m p ∧ p x ⇒ (dec2enc (decode_bnum m p) x = encode_bnum m x)
   
   [dec2enc_decode_bool]  Theorem
      
      |- ∀p x. p x ⇒ (dec2enc (decode_bool p) x = encode_bool x)
   
   [dec2enc_decode_list]  Theorem
      
      |- ∀p d x.
           wf_decoder p d ∧ EVERY p x ⇒
           (dec2enc (decode_list (EVERY p) d) x = encode_list (dec2enc d) x)
   
   [dec2enc_decode_num]  Theorem
      
      |- ∀p x. p x ⇒ (dec2enc (decode_num p) x = encode_num x)
   
   [dec2enc_decode_option]  Theorem
      
      |- ∀p d x.
           wf_decoder p d ∧ lift_option p x ⇒
           (dec2enc (decode_option (lift_option p) d) x =
            encode_option (dec2enc d) x)
   
   [dec2enc_decode_prod]  Theorem
      
      |- ∀p1 p2 d1 d2 x.
           wf_decoder p1 d1 ∧ wf_decoder p2 d2 ∧ lift_prod p1 p2 x ⇒
           (dec2enc (decode_prod (lift_prod p1 p2) d1 d2) x =
            encode_prod (dec2enc d1) (dec2enc d2) x)
   
   [dec2enc_decode_sum]  Theorem
      
      |- ∀p1 p2 d1 d2 x.
           wf_decoder p1 d1 ∧ wf_decoder p2 d2 ∧ lift_sum p1 p2 x ⇒
           (dec2enc (decode_sum (lift_sum p1 p2) d1 d2) x =
            encode_sum (dec2enc d1) (dec2enc d2) x)
   
   [dec2enc_decode_unit]  Theorem
      
      |- ∀p x. p x ⇒ (dec2enc (decode_unit p) x = encode_unit x)
   
   [dec2enc_enc2dec]  Theorem
      
      |- ∀p e x. wf_encoder p e ∧ p x ⇒ (dec2enc (enc2dec p e) x = e x)
   
   [dec2enc_some]  Theorem
      
      |- ∀p d x l. wf_decoder p d ⇒ ((dec2enc d x = l) ∧ p x ⇔ (d l = SOME (x,[])))
   
   [dec_bnum_inj]  Theorem
      
      |- ∀m l n t. (dec_bnum m l = SOME (n,t)) ⇒ (l = encode_bnum m n ++ t)
   
   [dec_bnum_lt]  Theorem
      
      |- ∀m l n t. (dec_bnum m l = SOME (n,t)) ⇒ n < 2 ** m
   
   [decode_blist]  Theorem
      
      |- wf_decoder p d ⇒
         (decode_blist (lift_blist m p) m d l =
          case m of
             0 -> SOME ([],l)
          || SUC n ->
               case d l of
                  NONE -> NONE
               || SOME (x,t) ->
                    case decode_blist (lift_blist n p) n d t of
                       NONE -> NONE
                    || SOME (xs,t') -> SOME (x::xs,t'))
   
   [decode_bnum]  Theorem
      
      |- wf_pred_bnum m p ⇒
         (decode_bnum m p l =
          case dec_bnum m l of
             NONE -> NONE
          || SOME (n,t) -> if p n then SOME (n,t) else NONE)
   
   [decode_bool]  Theorem
      
      |- decode_bool p l =
         case l of [] -> NONE || h::t -> if p h then SOME (h,t) else NONE
   
   [decode_dec2enc]  Theorem
      
      |- ∀p d x. wf_decoder p d ∧ p x ⇒ (d (dec2enc d x) = SOME (x,[]))
   
   [decode_dec2enc_append]  Theorem
      
      |- ∀p d x t. wf_decoder p d ∧ p x ⇒ (d (dec2enc d x ++ t) = SOME (x,t))
   
   [decode_list]  Theorem
      
      |- wf_decoder p d ⇒
         (decode_list (EVERY p) d l =
          case l of
             [] -> NONE
          || T::t ->
               (case d t of
                   NONE -> NONE
                || SOME (x,t') ->
                     case decode_list (EVERY p) d t' of
                        NONE -> NONE
                     || SOME (xs,t'') -> SOME (x::xs,t''))
          || F::t -> SOME ([],t))
   
   [decode_num]  Theorem
      
      |- decode_num p l =
         case l of
            [] -> NONE
         || [T] -> NONE
         || T::T::t -> if p 0 then SOME (0,t) else NONE
         || T::F::t ->
              (case decode_num (K T) t of
                  NONE -> NONE
               || SOME (v,t') -> if p (2 * v + 1) then SOME (2 * v + 1,t') else NONE)
         || F::t' ->
              case decode_num (K T) t' of
                 NONE -> NONE
              || SOME (v,t') -> if p (2 * v + 2) then SOME (2 * v + 2,t') else NONE
   
   [decode_num_total]  Theorem
      
      |- decode_num (K T) l =
         case l of
            [] -> NONE
         || [T] -> NONE
         || T::T::t -> SOME (0,t)
         || T::F::t ->
              (case decode_num (K T) t of
                  NONE -> NONE
               || SOME (v,t') -> SOME (2 * v + 1,t'))
         || F::t' ->
              case decode_num (K T) t' of
                 NONE -> NONE
              || SOME (v,t') -> SOME (2 * v + 2,t')
   
   [decode_option]  Theorem
      
      |- wf_decoder p d ⇒
         (decode_option (lift_option p) d l =
          case l of
             [] -> NONE
          || T::t -> (case d t of NONE -> NONE || SOME (x,t') -> SOME (SOME x,t'))
          || F::t -> SOME (NONE,t))
   
   [decode_prod]  Theorem
      
      |- wf_decoder p1 d1 ∧ wf_decoder p2 d2 ⇒
         (decode_prod (lift_prod p1 p2) d1 d2 l =
          case d1 l of
             NONE -> NONE
          || SOME (x,t) ->
               case d2 t of NONE -> NONE || SOME (y,t') -> SOME ((x,y),t'))
   
   [decode_sum]  Theorem
      
      |- wf_decoder p1 d1 ∧ wf_decoder p2 d2 ⇒
         (decode_sum (lift_sum p1 p2) d1 d2 l =
          case l of
             [] -> NONE
          || T::t -> (case d1 t of NONE -> NONE || SOME (x,t') -> SOME (INL x,t'))
          || F::t -> case d2 t of NONE -> NONE || SOME (x,t') -> SOME (INR x,t'))
   
   [decode_tree]  Theorem
      
      |- wf_decoder p d ⇒
         (decode_tree (lift_tree p) d l =
          case d l of
             NONE -> NONE
          || SOME (a,t) ->
               case
                 decode_list (EVERY (lift_tree p)) (decode_tree (lift_tree p) d) t
                 of
                  NONE -> NONE
               || SOME (ts,t') -> SOME (Node a ts,t'))
   
   [decode_unit]  Theorem
      
      |- decode_unit p l = if p () then SOME ((),l) else NONE
   
   [enc2dec_dec2enc]  Theorem
      
      |- ∀p d. wf_decoder p d ⇒ (enc2dec p (dec2enc d) = d)
   
   [enc2dec_none]  Theorem
      
      |- ∀p e l. (enc2dec p e l = NONE) ⇔ ∀x t. p x ⇒ l ≠ e x ++ t
   
   [enc2dec_some]  Theorem
      
      |- ∀p e l x t.
           wf_encoder p e ⇒ ((enc2dec p e l = SOME (x,t)) ⇔ p x ∧ (l = e x ++ t))
   
   [enc2dec_some_alt]  Theorem
      
      |- ∀p e l x.
           wf_encoder p e ⇒
           ((enc2dec p e l = SOME x) ⇔ p (FST x) ∧ (l = e (FST x) ++ SND x))
   
   [encode_then_decode_blist]  Theorem
      
      |- ∀m p e l t.
           wf_encoder p e ∧ lift_blist m p l ⇒
           (decode_blist (lift_blist m p) m (enc2dec p e) (encode_blist m e l ++ t) =
            SOME (l,t))
   
   [encode_then_decode_list]  Theorem
      
      |- ∀p e l t.
           wf_encoder p e ∧ EVERY p l ⇒
           (decode_list (EVERY p) (enc2dec p e) (encode_list e l ++ t) = SOME (l,t))
   
   [encode_then_decode_option]  Theorem
      
      |- ∀p e l t.
           wf_encoder p e ∧ lift_option p l ⇒
           (decode_option (lift_option p) (enc2dec p e) (encode_option e l ++ t) =
            SOME (l,t))
   
   [encode_then_decode_prod]  Theorem
      
      |- ∀p1 p2 e1 e2 l t.
           wf_encoder p1 e1 ∧ wf_encoder p2 e2 ∧ lift_prod p1 p2 l ⇒
           (decode_prod (lift_prod p1 p2) (enc2dec p1 e1) (enc2dec p2 e2)
              (encode_prod e1 e2 l ++ t) =
            SOME (l,t))
   
   [encode_then_decode_sum]  Theorem
      
      |- ∀p1 p2 e1 e2 l t.
           wf_encoder p1 e1 ∧ wf_encoder p2 e2 ∧ lift_sum p1 p2 l ⇒
           (decode_sum (lift_sum p1 p2) (enc2dec p1 e1) (enc2dec p2 e2)
              (encode_sum e1 e2 l ++ t) =
            SOME (l,t))
   
   [wf_dec2enc]  Theorem
      
      |- ∀p d. wf_decoder p d ⇒ wf_encoder p (dec2enc d)
   
   [wf_decode_blist]  Theorem
      
      |- ∀m p d.
           wf_decoder p d ⇒
           wf_decoder (lift_blist m p) (decode_blist (lift_blist m p) m d)
   
   [wf_decode_bnum]  Theorem
      
      |- ∀m p. wf_pred_bnum m p ⇒ wf_decoder p (decode_bnum m p)
   
   [wf_decode_bool]  Theorem
      
      |- ∀p. wf_decoder p (decode_bool p)
   
   [wf_decode_list]  Theorem
      
      |- ∀p d. wf_decoder p d ⇒ wf_decoder (EVERY p) (decode_list (EVERY p) d)
   
   [wf_decode_num]  Theorem
      
      |- ∀p. wf_decoder p (decode_num p)
   
   [wf_decode_option]  Theorem
      
      |- ∀p d.
           wf_decoder p d ⇒
           wf_decoder (lift_option p) (decode_option (lift_option p) d)
   
   [wf_decode_prod]  Theorem
      
      |- ∀p1 p2 d1 d2.
           wf_decoder p1 d1 ∧ wf_decoder p2 d2 ⇒
           wf_decoder (lift_prod p1 p2) (decode_prod (lift_prod p1 p2) d1 d2)
   
   [wf_decode_sum]  Theorem
      
      |- ∀p1 p2 d1 d2.
           wf_decoder p1 d1 ∧ wf_decoder p2 d2 ⇒
           wf_decoder (lift_sum p1 p2) (decode_sum (lift_sum p1 p2) d1 d2)
   
   [wf_decode_tree]  Theorem
      
      |- ∀p d.
           wf_decoder p d ⇒ wf_decoder (lift_tree p) (decode_tree (lift_tree p) d)
   
   [wf_decode_unit]  Theorem
      
      |- wf_decoder p (decode_unit p)
   
   [wf_enc2dec]  Theorem
      
      |- ∀p e. wf_encoder p e ⇒ wf_decoder p (enc2dec p e)
   
   
*)
end
