signature prelimTheory =
sig
  type thm = Thm.thm
  
  (*  Definitions  *)
    val EQUAL_def : thm
    val GREATER_def : thm
    val LESS_def : thm
    val compare_def : thm
    val list_compare_curried_def : thm
    val list_compare_tupled_primitive_def : thm
    val list_merge_curried_def : thm
    val list_merge_tupled_primitive_def : thm
    val ordering_BIJ : thm
    val ordering_TY_DEF : thm
    val ordering_case : thm
    val ordering_size_def : thm
  
  (*  Theorems  *)
    val compare_equal : thm
    val datatype_ordering : thm
    val list_compare_def : thm
    val list_compare_ind : thm
    val list_merge_def : thm
    val list_merge_ind : thm
    val num2ordering_11 : thm
    val num2ordering_ONTO : thm
    val num2ordering_ordering2num : thm
    val num2ordering_thm : thm
    val ordering2num_11 : thm
    val ordering2num_ONTO : thm
    val ordering2num_num2ordering : thm
    val ordering2num_thm : thm
    val ordering_Axiom : thm
    val ordering_EQ_ordering : thm
    val ordering_case_cong : thm
    val ordering_case_def : thm
    val ordering_distinct : thm
    val ordering_eq_dec : thm
    val ordering_induction : thm
    val ordering_nchotomy : thm
  
  val prelim_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [list] Parent theory of "prelim"
   
   [EQUAL_def]  Definition
      
      |- EQUAL = num2ordering 1
   
   [GREATER_def]  Definition
      
      |- GREATER = num2ordering 2
   
   [LESS_def]  Definition
      
      |- LESS = num2ordering 0
   
   [compare_def]  Definition
      
      |- (∀lt eq gt. compare LESS lt eq gt = lt) ∧
         (∀lt eq gt. compare EQUAL lt eq gt = eq) ∧
         ∀lt eq gt. compare GREATER lt eq gt = gt
   
   [list_compare_curried_def]  Definition
      
      |- ∀x x1 x2. list_compare x x1 x2 = list_compare_tupled (x,x1,x2)
   
   [list_compare_tupled_primitive_def]  Definition
      
      |- list_compare_tupled =
         WFREC (@R. WF R ∧ ∀y x l2 l1 cmp. R (cmp,l1,l2) (cmp,x::l1,y::l2))
           (λlist_compare_tupled a.
              case a of
                 (cmp,[],[]) -> I EQUAL
              || (cmp,[],v10::v11) -> I LESS
              || (cmp,x::l1,[]) -> I GREATER
              || (cmp,x::l1,y::l2) ->
                   I
                     (compare (cmp x y) LESS (list_compare_tupled (cmp,l1,l2))
                        GREATER))
   
   [list_merge_curried_def]  Definition
      
      |- ∀x x1 x2. list_merge x x1 x2 = list_merge_tupled (x,x1,x2)
   
   [list_merge_tupled_primitive_def]  Definition
      
      |- list_merge_tupled =
         WFREC
           (@R.
              WF R ∧
              (∀l2 l1 y x a_lt. ¬a_lt x y ⇒ R (a_lt,x::l1,l2) (a_lt,x::l1,y::l2)) ∧
              ∀l2 l1 y x a_lt. a_lt x y ⇒ R (a_lt,l1,y::l2) (a_lt,x::l1,y::l2))
           (λlist_merge_tupled a.
              case a of
                 (a_lt,[],[]) -> I []
              || (a_lt,[],v10::v11) -> I (v10::v11)
              || (a_lt,x::l1,[]) -> I (x::l1)
              || (a_lt,x::l1,y::l2) ->
                   I
                     (if a_lt x y then
                        x::list_merge_tupled (a_lt,l1,y::l2)
                      else
                        y::list_merge_tupled (a_lt,x::l1,l2)))
   
   [ordering_BIJ]  Definition
      
      |- (∀a. num2ordering (ordering2num a) = a) ∧
         ∀r. (λn. n < 3) r ⇔ (ordering2num (num2ordering r) = r)
   
   [ordering_TY_DEF]  Definition
      
      |- ∃rep. TYPE_DEFINITION (λn. n < 3) rep
   
   [ordering_case]  Definition
      
      |- ∀v0 v1 v2 x.
           (case x of LESS -> v0 || EQUAL -> v1 || GREATER -> v2) =
           (λm. if m < 1 then v0 else if m = 1 then v1 else v2) (ordering2num x)
   
   [ordering_size_def]  Definition
      
      |- ∀x. ordering_size x = 0
   
   [compare_equal]  Theorem
      
      |- (∀x y. (cmp x y = EQUAL) ⇔ (x = y)) ⇒
         ∀l1 l2. (list_compare cmp l1 l2 = EQUAL) ⇔ (l1 = l2)
   
   [datatype_ordering]  Theorem
      
      |- DATATYPE (ordering LESS EQUAL GREATER)
   
   [list_compare_def]  Theorem
      
      |- (∀cmp. list_compare cmp [] [] = EQUAL) ∧
         (∀v9 v8 cmp. list_compare cmp [] (v8::v9) = LESS) ∧
         (∀v5 v4 cmp. list_compare cmp (v4::v5) [] = GREATER) ∧
         ∀y x l2 l1 cmp.
           list_compare cmp (x::l1) (y::l2) =
           compare (cmp x y) LESS (list_compare cmp l1 l2) GREATER
   
   [list_compare_ind]  Theorem
      
      |- ∀P.
           (∀cmp. P cmp [] []) ∧ (∀cmp v8 v9. P cmp [] (v8::v9)) ∧
           (∀cmp v4 v5. P cmp (v4::v5) []) ∧
           (∀cmp x l1 y l2. P cmp l1 l2 ⇒ P cmp (x::l1) (y::l2)) ⇒
           ∀v v1 v2. P v v1 v2
   
   [list_merge_def]  Theorem
      
      |- (∀a_lt. list_merge a_lt [] [] = []) ∧
         (∀v5 v4 a_lt. list_merge a_lt (v4::v5) [] = v4::v5) ∧
         (∀v9 v8 a_lt. list_merge a_lt [] (v8::v9) = v8::v9) ∧
         ∀y x l2 l1 a_lt.
           list_merge a_lt (x::l1) (y::l2) =
           if a_lt x y then
             x::list_merge a_lt l1 (y::l2)
           else
             y::list_merge a_lt (x::l1) l2
   
   [list_merge_ind]  Theorem
      
      |- ∀P.
           (∀a_lt. P a_lt [] []) ∧ (∀a_lt v4 v5. P a_lt (v4::v5) []) ∧
           (∀a_lt v8 v9. P a_lt [] (v8::v9)) ∧
           (∀a_lt x l1 y l2.
              (¬a_lt x y ⇒ P a_lt (x::l1) l2) ∧ (a_lt x y ⇒ P a_lt l1 (y::l2)) ⇒
              P a_lt (x::l1) (y::l2)) ⇒
           ∀v v1 v2. P v v1 v2
   
   [num2ordering_11]  Theorem
      
      |- ∀r r'. r < 3 ⇒ r' < 3 ⇒ ((num2ordering r = num2ordering r') ⇔ (r = r'))
   
   [num2ordering_ONTO]  Theorem
      
      |- ∀a. ∃r. (a = num2ordering r) ∧ r < 3
   
   [num2ordering_ordering2num]  Theorem
      
      |- ∀a. num2ordering (ordering2num a) = a
   
   [num2ordering_thm]  Theorem
      
      |- (num2ordering 0 = LESS) ∧ (num2ordering 1 = EQUAL) ∧
         (num2ordering 2 = GREATER)
   
   [ordering2num_11]  Theorem
      
      |- ∀a a'. (ordering2num a = ordering2num a') ⇔ (a = a')
   
   [ordering2num_ONTO]  Theorem
      
      |- ∀r. r < 3 ⇔ ∃a. r = ordering2num a
   
   [ordering2num_num2ordering]  Theorem
      
      |- ∀r. r < 3 ⇔ (ordering2num (num2ordering r) = r)
   
   [ordering2num_thm]  Theorem
      
      |- (ordering2num LESS = 0) ∧ (ordering2num EQUAL = 1) ∧
         (ordering2num GREATER = 2)
   
   [ordering_Axiom]  Theorem
      
      |- ∀x0 x1 x2. ∃f. (f LESS = x0) ∧ (f EQUAL = x1) ∧ (f GREATER = x2)
   
   [ordering_EQ_ordering]  Theorem
      
      |- ∀a a'. (a = a') ⇔ (ordering2num a = ordering2num a')
   
   [ordering_case_cong]  Theorem
      
      |- ∀M M' v0 v1 v2.
           (M = M') ∧ ((M' = LESS) ⇒ (v0 = v0')) ∧ ((M' = EQUAL) ⇒ (v1 = v1')) ∧
           ((M' = GREATER) ⇒ (v2 = v2')) ⇒
           ((case M of LESS -> v0 || EQUAL -> v1 || GREATER -> v2) =
            case M' of LESS -> v0' || EQUAL -> v1' || GREATER -> v2')
   
   [ordering_case_def]  Theorem
      
      |- (∀v0 v1 v2.
            (case LESS of LESS -> v0 || EQUAL -> v1 || GREATER -> v2) = v0) ∧
         (∀v0 v1 v2.
            (case EQUAL of LESS -> v0 || EQUAL -> v1 || GREATER -> v2) = v1) ∧
         ∀v0 v1 v2. (case GREATER of LESS -> v0 || EQUAL -> v1 || GREATER -> v2) = v2
   
   [ordering_distinct]  Theorem
      
      |- LESS ≠ EQUAL ∧ LESS ≠ GREATER ∧ EQUAL ≠ GREATER
   
   [ordering_eq_dec]  Theorem
      
      |- (∀x. (x = x) ⇔ T) ∧ ((LESS = EQUAL) ⇔ F) ∧ ((LESS = GREATER) ⇔ F) ∧
         ((EQUAL = GREATER) ⇔ F) ∧ ((EQUAL = LESS) ⇔ F) ∧ ((GREATER = LESS) ⇔ F) ∧
         ((GREATER = EQUAL) ⇔ F)
   
   [ordering_induction]  Theorem
      
      |- ∀P. P EQUAL ∧ P GREATER ∧ P LESS ⇒ ∀a. P a
   
   [ordering_nchotomy]  Theorem
      
      |- ∀a. (a = LESS) ∨ (a = EQUAL) ∨ (a = GREATER)
   
   
*)
end
