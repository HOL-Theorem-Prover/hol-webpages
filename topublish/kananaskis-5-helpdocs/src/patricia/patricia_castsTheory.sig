signature patricia_castsTheory =
sig
  type thm = Thm.thm
  
  (*  Definitions  *)
    val ADD_LISTs_def : thm
    val ADD_LISTw_def : thm
    val ADDs_def : thm
    val ADDw_def : thm
    val DEPTHw_def : thm
    val EVERY_LEAFw_def : thm
    val EXISTS_LEAFw_def : thm
    val FINDs_def : thm
    val FINDw_def : thm
    val INSERT_PTREEs_def : thm
    val INSERT_PTREEw_def : thm
    val IN_PTREEs_def : thm
    val IN_PTREEw_def : thm
    val KEYSs_def : thm
    val KEYSw_def : thm
    val PEEKs_def : thm
    val PEEKw_def : thm
    val PTREE_OF_STRINGSET_def : thm
    val PTREE_OF_WORDSET_def : thm
    val REMOVEs_def : thm
    val REMOVEw_def : thm
    val SIZEw_def : thm
    val SKIP1_def : thm
    val SOME_PTREE_def : thm
    val STRINGSET_OF_PTREE_def : thm
    val THE_PTREE_def : thm
    val TRANSFORMw_def : thm
    val TRAVERSEs_def : thm
    val TRAVERSEw_def : thm
    val UNION_PTREEw_def : thm
    val WORDSET_OF_PTREE_def : thm
    val WordEmpty_def : thm
    val num_to_string_def : thm
    val string_to_num_def : thm
    val word_ptree_TY_DEF : thm
    val word_ptree_case_def : thm
    val word_ptree_repfns : thm
    val word_ptree_size_def : thm
  
  (*  Theorems  *)
    val ADD_INSERT_STRING : thm
    val ADD_INSERT_WORD : thm
    val EVERY_MAP_ORD : thm
    val IMAGE_string_to_num : thm
    val MAP_11 : thm
    val REVERSE_11 : thm
    val THE_PTREE_SOME_PTREE : thm
    val datatype_word_ptree : thm
    val l2n_11 : thm
    val l2n_APPEND : thm
    val l2n_LENGTH : thm
    val num_to_string_string_to_num : thm
    val string_to_num_11 : thm
    val string_to_num_num_to_string : thm
    val word_ptree_11 : thm
    val word_ptree_Axiom : thm
    val word_ptree_case_cong : thm
    val word_ptree_induction : thm
    val word_ptree_nchotomy : thm
  
  val patricia_casts_grammars : type_grammar.grammar * term_grammar.grammar
  
  val patricia_casts_rwts : simpLib.ssfrag
(*
   [patricia] Parent theory of "patricia_casts"
   
   [ADD_LISTs_def]  Definition
      
      |- $|++ = FOLDL $|+
   
   [ADD_LISTw_def]  Definition
      
      |- $|++ = FOLDL $|+
   
   [ADDs_def]  Definition
      
      |- !t w d. t |+ (w,d) = t |+ (string_to_num w,d)
   
   [ADDw_def]  Definition
      
      |- !t w d. t |+ (w,d) = SOME_PTREE (THE_PTREE t |+ (w2n w,d))
   
   [DEPTHw_def]  Definition
      
      |- !t. DEPTHw t = DEPTH (THE_PTREE t)
   
   [EVERY_LEAFw_def]  Definition
      
      |- !P t.
           EVERY_LEAFw P t <=> EVERY_LEAF (\k d. P (n2w k) d) (THE_PTREE t)
   
   [EXISTS_LEAFw_def]  Definition
      
      |- !P t.
           EXISTS_LEAFw P t <=>
           EXISTS_LEAF (\k d. P (n2w k) d) (THE_PTREE t)
   
   [FINDs_def]  Definition
      
      |- !t w. FINDs t w = THE (t ' w)
   
   [FINDw_def]  Definition
      
      |- !t w. FINDw t w = THE (t ' w)
   
   [INSERT_PTREEs_def]  Definition
      
      |- !w t. w INSERT_PTREEs t = string_to_num w INSERT_PTREE t
   
   [INSERT_PTREEw_def]  Definition
      
      |- !w t.
           w INSERT_PTREEw t = SOME_PTREE (w2n w INSERT_PTREE THE_PTREE t)
   
   [IN_PTREEs_def]  Definition
      
      |- !w t. w IN_PTREEs t <=> string_to_num w IN_PTREE t
   
   [IN_PTREEw_def]  Definition
      
      |- !w t. w IN_PTREEw t <=> w2n w IN_PTREE THE_PTREE t
   
   [KEYSs_def]  Definition
      
      |- !t. KEYSs t = QSORT $< (TRAVERSEs t)
   
   [KEYSw_def]  Definition
      
      |- !t. KEYSw t = QSORT $<+ (TRAVERSEw t)
   
   [PEEKs_def]  Definition
      
      |- !t w. t ' w = t ' (string_to_num w)
   
   [PEEKw_def]  Definition
      
      |- !t w. t ' w = THE_PTREE t ' (w2n w)
   
   [PTREE_OF_STRINGSET_def]  Definition
      
      |- !t s. t |++ s = t |++ IMAGE string_to_num s
   
   [PTREE_OF_WORDSET_def]  Definition
      
      |- !t s. t |++ s = SOME_PTREE (THE_PTREE t |++ IMAGE w2n s)
   
   [REMOVEs_def]  Definition
      
      |- !t w. t \\ w = t \\ string_to_num w
   
   [REMOVEw_def]  Definition
      
      |- !t w. t \\ w = SOME_PTREE (THE_PTREE t \\ w2n w)
   
   [SIZEw_def]  Definition
      
      |- !t. SIZEw t = SIZE (THE_PTREE t)
   
   [SKIP1_def]  Definition
      
      |- !c s. SKIP1 (STRING c s) = s
   
   [SOME_PTREE_def]  Definition
      
      |- !t. SOME_PTREE t = Word_ptree (K ()) t
   
   [STRINGSET_OF_PTREE_def]  Definition
      
      |- !t. STRINGSET_OF_PTREE t = LIST_TO_SET (TRAVERSEs t)
   
   [THE_PTREE_def]  Definition
      
      |- !a t. THE_PTREE (Word_ptree a t) = t
   
   [TRANSFORMw_def]  Definition
      
      |- !f t. TRANSFORMw f t = SOME_PTREE (TRANSFORM f (THE_PTREE t))
   
   [TRAVERSEs_def]  Definition
      
      |- !t. TRAVERSEs t = MAP num_to_string (TRAVERSE t)
   
   [TRAVERSEw_def]  Definition
      
      |- !t. TRAVERSEw t = MAP n2w (TRAVERSE (THE_PTREE t))
   
   [UNION_PTREEw_def]  Definition
      
      |- !t1 t2.
           t1 UNION_PTREEw t2 =
           SOME_PTREE (THE_PTREE t1 UNION_PTREE THE_PTREE t2)
   
   [WORDSET_OF_PTREE_def]  Definition
      
      |- !t. WORDSET_OF_PTREE t = LIST_TO_SET (TRAVERSEw t)
   
   [WordEmpty_def]  Definition
      
      |- +{}+ = SOME_PTREE <{}>
   
   [num_to_string_def]  Definition
      
      |- !n. num_to_string n = SKIP1 (n2s 256 CHR n)
   
   [string_to_num_def]  Definition
      
      |- !s. string_to_num s = s2n 256 ORD (STRING #"\^A" s)
   
   [word_ptree_TY_DEF]  Definition
      
      |- ?rep.
           TYPE_DEFINITION
             (\a0'.
                !'word_ptree' .
                  (!a0'.
                     (?a0 a1.
                        a0' =
                        (\a0 a1.
                           ind_type$CONSTR 0 (a0,a1) (\n. ind_type$BOTTOM))
                          a0 a1) ==>
                     'word_ptree' a0') ==>
                  'word_ptree' a0') rep
   
   [word_ptree_case_def]  Definition
      
      |- !f a0 a1. word_ptree_case f (Word_ptree a0 a1) = f a0 a1
   
   [word_ptree_repfns]  Definition
      
      |- (!a. mk_word_ptree (dest_word_ptree a) = a) /\
         !r.
           (\a0'.
              !'word_ptree' .
                (!a0'.
                   (?a0 a1.
                      a0' =
                      (\a0 a1.
                         ind_type$CONSTR 0 (a0,a1) (\n. ind_type$BOTTOM))
                        a0 a1) ==>
                   'word_ptree' a0') ==>
                'word_ptree' a0') r <=>
           (dest_word_ptree (mk_word_ptree r) = r)
   
   [word_ptree_size_def]  Definition
      
      |- !f f1 a0 a1.
           word_ptree_size f f1 (Word_ptree a0 a1) = 1 + ptree_size f1 a1
   
   [ADD_INSERT_STRING]  Theorem
      
      |- !w v t. t |+ (w,v) = t |+ (w,())
   
   [ADD_INSERT_WORD]  Theorem
      
      |- !w v t. t |+ (w,v) = t |+ (w,())
   
   [EVERY_MAP_ORD]  Theorem
      
      |- !l. EVERY ($> 256) (MAP ORD l)
   
   [IMAGE_string_to_num]  Theorem
      
      |- !n.
           (n = 1) \/ 256 <= n /\ (n DIV 256 ** LOG 256 n = 1) <=>
           n IN IMAGE string_to_num UNIV
   
   [MAP_11]  Theorem
      
      |- !f l1 l2.
           (!x y. (f x = f y) <=> (x = y)) ==>
           ((MAP f l1 = MAP f l2) <=> (l1 = l2))
   
   [REVERSE_11]  Theorem
      
      |- !l1 l2. (REVERSE l1 = REVERSE l2) <=> (l1 = l2)
   
   [THE_PTREE_SOME_PTREE]  Theorem
      
      |- !t. THE_PTREE (SOME_PTREE t) = t
   
   [datatype_word_ptree]  Theorem
      
      |- DATATYPE (word_ptree Word_ptree)
   
   [l2n_11]  Theorem
      
      |- !b l1 l2.
           1 < b /\ EVERY ($> b) l1 /\ EVERY ($> b) l2 ==>
           ((l2n b (l1 ++ [1]) = l2n b (l2 ++ [1])) <=> (l1 = l2))
   
   [l2n_APPEND]  Theorem
      
      |- !b l1 l2. l2n b (l1 ++ l2) = l2n b l1 + b ** LENGTH l1 * l2n b l2
   
   [l2n_LENGTH]  Theorem
      
      |- !b l. 1 < b ==> l2n b l < b ** LENGTH l
   
   [num_to_string_string_to_num]  Theorem
      
      |- !s. num_to_string (string_to_num s) = s
   
   [string_to_num_11]  Theorem
      
      |- !s t. (string_to_num s = string_to_num t) <=> (s = t)
   
   [string_to_num_num_to_string]  Theorem
      
      |- !n.
           n IN IMAGE string_to_num UNIV ==>
           (string_to_num (num_to_string n) = n)
   
   [word_ptree_11]  Theorem
      
      |- !a0 a1 a0' a1'.
           (Word_ptree a0 a1 = Word_ptree a0' a1') <=>
           (a0 = a0') /\ (a1 = a1')
   
   [word_ptree_Axiom]  Theorem
      
      |- !f. ?fn. !a0 a1. fn (Word_ptree a0 a1) = f a0 a1
   
   [word_ptree_case_cong]  Theorem
      
      |- !M M' f.
           (M = M') /\
           (!a0 a1. (M' = Word_ptree a0 a1) ==> (f a0 a1 = f' a0 a1)) ==>
           (word_ptree_case f M = word_ptree_case f' M')
   
   [word_ptree_induction]  Theorem
      
      |- !P. (!f p. P (Word_ptree f p)) ==> !w. P w
   
   [word_ptree_nchotomy]  Theorem
      
      |- !ww. ?f p. ww = Word_ptree f p
   
   
*)
end
