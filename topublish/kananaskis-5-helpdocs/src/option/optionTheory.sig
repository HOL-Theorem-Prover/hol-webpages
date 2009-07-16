signature optionTheory =
sig
  type thm = Thm.thm
  
  (*  Definitions  *)
    val IS_NONE_DEF : thm
    val IS_SOME_DEF : thm
    val NONE_DEF : thm
    val OPTION_JOIN_DEF : thm
    val OPTION_MAP_DEF : thm
    val OPTREL_def : thm
    val SOME_DEF : thm
    val THE_DEF : thm
    val option_REP_ABS_DEF : thm
    val option_TY_DEF : thm
    val option_case_def : thm
  
  (*  Theorems  *)
    val FORALL_OPTION : thm
    val IS_NONE_EQ_NONE : thm
    val NOT_IS_SOME_EQ_NONE : thm
    val NOT_NONE_SOME : thm
    val NOT_SOME_NONE : thm
    val OPTION_JOIN_EQ_SOME : thm
    val OPTION_MAP_CONG : thm
    val OPTION_MAP_EQ_NONE : thm
    val OPTION_MAP_EQ_NONE_both_ways : thm
    val OPTION_MAP_EQ_SOME : thm
    val OPTREL_MONO : thm
    val SOME_11 : thm
    val option_Axiom : thm
    val option_CLAUSES : thm
    val option_case_ID : thm
    val option_case_SOME_ID : thm
    val option_case_compute : thm
    val option_case_cong : thm
    val option_induction : thm
    val option_nchotomy : thm
  
  val option_grammars : type_grammar.grammar * term_grammar.grammar
  
  val option_rwts : simpLib.ssfrag
  
  val option_Induct : thm
  val option_CASES : thm
  
(*
   [normalForms] Parent theory of "option"
   
   [one] Parent theory of "option"
   
   [sum] Parent theory of "option"
   
   [IS_NONE_DEF]  Definition
      
      |- (!x. IS_NONE (SOME x) <=> F) /\ (IS_NONE NONE <=> T)
   
   [IS_SOME_DEF]  Definition
      
      |- (!x. IS_SOME (SOME x) <=> T) /\ (IS_SOME NONE <=> F)
   
   [NONE_DEF]  Definition
      
      |- NONE = option_ABS (INR ())
   
   [OPTION_JOIN_DEF]  Definition
      
      |- (OPTION_JOIN NONE = NONE) /\ !x. OPTION_JOIN (SOME x) = x
   
   [OPTION_MAP_DEF]  Definition
      
      |- (!f x. OPTION_MAP f (SOME x) = SOME (f x)) /\
         !f. OPTION_MAP f NONE = NONE
   
   [OPTREL_def]  Definition
      
      |- !R x y.
           OPTREL R x y <=>
           (x = NONE) /\ (y = NONE) \/
           ?x0 y0. (x = SOME x0) /\ (y = SOME y0) /\ R x0 y0
   
   [SOME_DEF]  Definition
      
      |- !x. SOME x = option_ABS (INL x)
   
   [THE_DEF]  Definition
      
      |- !x. THE (SOME x) = x
   
   [option_REP_ABS_DEF]  Definition
      
      |- (!a. option_ABS (option_REP a) = a) /\
         !r. (\x. T) r <=> (option_REP (option_ABS r) = r)
   
   [option_TY_DEF]  Definition
      
      |- ?rep. TYPE_DEFINITION (\x. T) rep
   
   [option_case_def]  Definition
      
      |- (!u f. option_case u f NONE = u) /\
         !u f x. option_case u f (SOME x) = f x
   
   [FORALL_OPTION]  Theorem
      
      |- (!opt. P opt) <=> P NONE /\ !x. P (SOME x)
   
   [IS_NONE_EQ_NONE]  Theorem
      
      |- !x. IS_NONE x <=> (x = NONE)
   
   [NOT_IS_SOME_EQ_NONE]  Theorem
      
      |- !x. ~IS_SOME x <=> (x = NONE)
   
   [NOT_NONE_SOME]  Theorem
      
      |- !x. NONE <> SOME x
   
   [NOT_SOME_NONE]  Theorem
      
      |- !x. SOME x <> NONE
   
   [OPTION_JOIN_EQ_SOME]  Theorem
      
      |- !x y. (OPTION_JOIN x = SOME y) <=> (x = SOME (SOME y))
   
   [OPTION_MAP_CONG]  Theorem
      
      |- !opt1 opt2 f1 f2.
           (opt1 = opt2) /\ (!x. (opt2 = SOME x) ==> (f1 x = f2 x)) ==>
           (OPTION_MAP f1 opt1 = OPTION_MAP f2 opt2)
   
   [OPTION_MAP_EQ_NONE]  Theorem
      
      |- !f x. (OPTION_MAP f x = NONE) <=> (x = NONE)
   
   [OPTION_MAP_EQ_NONE_both_ways]  Theorem
      
      |- ((OPTION_MAP f x = NONE) <=> (x = NONE)) /\
         ((NONE = OPTION_MAP f x) <=> (x = NONE))
   
   [OPTION_MAP_EQ_SOME]  Theorem
      
      |- !f x y.
           (OPTION_MAP f x = SOME y) <=> ?z. (x = SOME z) /\ (y = f z)
   
   [OPTREL_MONO]  Theorem
      
      |- (!x y. P x y ==> Q x y) ==> OPTREL P x y ==> OPTREL Q x y
   
   [SOME_11]  Theorem
      
      |- !x y. (SOME x = SOME y) <=> (x = y)
   
   [option_Axiom]  Theorem
      
      |- !e f. ?fn. (!x. fn (SOME x) = f x) /\ (fn NONE = e)
   
   [option_CLAUSES]  Theorem
      
      |- (!x y. (SOME x = SOME y) <=> (x = y)) /\ (!x. THE (SOME x) = x) /\
         (!x. NONE <> SOME x) /\ (!x. SOME x <> NONE) /\
         (!x. IS_SOME (SOME x) <=> T) /\ (IS_SOME NONE <=> F) /\
         (!x. IS_NONE x <=> (x = NONE)) /\
         (!x. ~IS_SOME x <=> (x = NONE)) /\
         (!x. IS_SOME x ==> (SOME (THE x) = x)) /\
         (!x. option_case NONE SOME x = x) /\
         (!x. option_case x SOME x = x) /\
         (!x. IS_NONE x ==> (option_case e f x = e)) /\
         (!x. IS_SOME x ==> (option_case e f x = f (THE x))) /\
         (!x. IS_SOME x ==> (option_case e SOME x = x)) /\
         (!u f. option_case u f NONE = u) /\
         (!u f x. option_case u f (SOME x) = f x) /\
         (!f x. OPTION_MAP f (SOME x) = SOME (f x)) /\
         (!f. OPTION_MAP f NONE = NONE) /\ (OPTION_JOIN NONE = NONE) /\
         !x. OPTION_JOIN (SOME x) = x
   
   [option_case_ID]  Theorem
      
      |- !x. option_case NONE SOME x = x
   
   [option_case_SOME_ID]  Theorem
      
      |- !x. option_case x SOME x = x
   
   [option_case_compute]  Theorem
      
      |- option_case e f x = if IS_SOME x then f (THE x) else e
   
   [option_case_cong]  Theorem
      
      |- !M M' u f.
           (M = M') /\ ((M' = NONE) ==> (u = u')) /\
           (!x. (M' = SOME x) ==> (f x = f' x)) ==>
           (option_case u f M = option_case u' f' M')
   
   [option_induction]  Theorem
      
      |- !P. P NONE /\ (!a. P (SOME a)) ==> !x. P x
   
   [option_nchotomy]  Theorem
      
      |- !opt. (opt = NONE) \/ ?x. opt = SOME x
   
   
*)
end
