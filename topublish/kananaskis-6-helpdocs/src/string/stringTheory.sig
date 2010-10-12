signature stringTheory =
sig
  type thm = Thm.thm
  
  (*  Definitions  *)
    val DEST_STRING_def : thm
    val EXPLODE_def : thm
    val EXTRACT_primitive_def : thm
    val FIELDS_curried_def : thm
    val FIELDS_tupled_primitive_def : thm
    val IMPLODE_def : thm
    val PAD_LEFT_def : thm
    val PAD_RIGHT_def : thm
    val STR_def : thm
    val SUBSTRING_def : thm
    val SUB_def : thm
    val TOKENS_curried_def : thm
    val TOKENS_tupled_primitive_def : thm
    val TRANSLATE_def : thm
    val char_BIJ : thm
    val char_TY_DEF : thm
    val char_ge_def : thm
    val char_gt_def : thm
    val char_le_def : thm
    val char_lt_def : thm
    val char_size_def : thm
    val isAlphaNum_def : thm
    val isAlpha_def : thm
    val isAscii_def : thm
    val isCntrl_def : thm
    val isDigit_def : thm
    val isGraph_def : thm
    val isHexDigit_def : thm
    val isLower_def : thm
    val isPrint_def : thm
    val isPunct_def : thm
    val isSpace_def : thm
    val isUpper_def : thm
    val string_ge_def : thm
    val string_gt_def : thm
    val string_le_def : thm
    val string_lt_curried_def : thm
    val string_lt_tupled_primitive_def : thm
    val toLower_def : thm
    val toUpper_def : thm
  
  (*  Theorems  *)
    val CHAR_EQ_THM : thm
    val CHAR_INDUCT_THM : thm
    val CHR_11 : thm
    val CHR_ONTO : thm
    val CHR_ORD : thm
    val DEST_STRING_LEMS : thm
    val EXPLODE_11 : thm
    val EXPLODE_DEST_STRING : thm
    val EXPLODE_EQNS : thm
    val EXPLODE_EQ_NIL : thm
    val EXPLODE_EQ_THM : thm
    val EXPLODE_IMPLODE : thm
    val EXPLODE_ONTO : thm
    val EXTRACT_def : thm
    val EXTRACT_ind : thm
    val FIELDS_def : thm
    val FIELDS_ind : thm
    val IMPLODE_11 : thm
    val IMPLODE_EQNS : thm
    val IMPLODE_EQ_EMPTYSTRING : thm
    val IMPLODE_EQ_THM : thm
    val IMPLODE_EXPLODE : thm
    val IMPLODE_EXPLODE_I : thm
    val IMPLODE_ONTO : thm
    val IMPLODE_STRING : thm
    val ORD_11 : thm
    val ORD_BOUND : thm
    val ORD_CHR : thm
    val ORD_CHR_COMPUTE : thm
    val ORD_CHR_RWT : thm
    val ORD_ONTO : thm
    val STRCAT : thm
    val STRCAT_11 : thm
    val STRCAT_ACYCLIC : thm
    val STRCAT_ASSOC : thm
    val STRCAT_EQNS : thm
    val STRCAT_EQ_EMPTY : thm
    val STRCAT_EXPLODE : thm
    val STRCAT_def : thm
    val STRING_ACYCLIC : thm
    val STRLEN_CAT : thm
    val STRLEN_DEF : thm
    val STRLEN_EQ_0 : thm
    val STRLEN_EXPLODE_THM : thm
    val STRLEN_THM : thm
    val TOKENS_def : thm
    val TOKENS_ind : thm
    val char_nchotomy : thm
    val isPREFIX_DEF : thm
    val isPREFIX_IND : thm
    val isPREFIX_STRCAT : thm
    val ranged_char_nchotomy : thm
    val string_lt_antisym : thm
    val string_lt_cases : thm
    val string_lt_def : thm
    val string_lt_ind : thm
    val string_lt_nonrefl : thm
    val string_lt_trans : thm
  
  val string_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [rich_list] Parent theory of "string"
   
   [DEST_STRING_def]  Definition
      
      |- (DEST_STRING "" = NONE) ∧ ∀c rst. DEST_STRING (STRING c rst) = SOME (c,rst)
   
   [EXPLODE_def]  Definition
      
      |- (EXPLODE "" = "") ∧ ∀c s. EXPLODE (STRING c s) = STRING c (EXPLODE s)
   
   [EXTRACT_primitive_def]  Definition
      
      |- EXTRACT =
         WFREC (@R. WF R)
           (λEXTRACT a.
              case a of
                 (s,i,NONE) -> I (SUBSTRING (s,i,STRLEN s − i))
              || (s,i,SOME n) -> I (SUBSTRING (s,i,n)))
   
   [FIELDS_curried_def]  Definition
      
      |- ∀x x1. FIELDS x x1 = FIELDS_tupled (x,x1)
   
   [FIELDS_tupled_primitive_def]  Definition
      
      |- FIELDS_tupled =
         WFREC
           (@R.
              WF R ∧
              (∀t h P l r.
                 ((l,r) = SPLITP P (STRING h t)) ∧ NULL l ⇒
                 R (P,TL r) (P,STRING h t)) ∧
              ∀t h P l r.
                ((l,r) = SPLITP P (STRING h t)) ∧ ¬NULL l ∧ ¬NULL r ⇒
                R (P,TL r) (P,STRING h t))
           (λFIELDS_tupled a.
              case a of
                 (P,"") -> I [""]
              || (P,STRING h t) ->
                   I
                     (let (l,r) = SPLITP P (STRING h t)
                      in
                        if NULL l then
                          ""::FIELDS_tupled (P,TL r)
                        else if NULL r then
                          [l]
                        else
                          l::FIELDS_tupled (P,TL r)))
   
   [IMPLODE_def]  Definition
      
      |- (IMPLODE "" = "") ∧ ∀c cs. IMPLODE (STRING c cs) = STRING c (IMPLODE cs)
   
   [PAD_LEFT_def]  Definition
      
      |- ∀c n s. PAD_LEFT c n s = STRCAT (GENLIST (K c) (n − STRLEN s)) s
   
   [PAD_RIGHT_def]  Definition
      
      |- ∀c n s. PAD_RIGHT c n s = STRCAT s (GENLIST (K c) (n − STRLEN s))
   
   [STR_def]  Definition
      
      |- ∀c. STR c = STRING c ""
   
   [SUBSTRING_def]  Definition
      
      |- ∀s i n. SUBSTRING (s,i,n) = SEG n i s
   
   [SUB_def]  Definition
      
      |- ∀s n. SUB (s,n) = EL n s
   
   [TOKENS_curried_def]  Definition
      
      |- ∀x x1. TOKENS x x1 = TOKENS_tupled (x,x1)
   
   [TOKENS_tupled_primitive_def]  Definition
      
      |- TOKENS_tupled =
         WFREC
           (@R.
              WF R ∧
              (∀t h P l r.
                 ((l,r) = SPLITP P (STRING h t)) ∧ NULL l ⇒
                 R (P,TL r) (P,STRING h t)) ∧
              ∀t h P l r.
                ((l,r) = SPLITP P (STRING h t)) ∧ ¬NULL l ⇒ R (P,r) (P,STRING h t))
           (λTOKENS_tupled a.
              case a of
                 (P,"") -> I []
              || (P,STRING h t) ->
                   I
                     (let (l,r) = SPLITP P (STRING h t)
                      in
                        if NULL l then
                          TOKENS_tupled (P,TL r)
                        else
                          l::TOKENS_tupled (P,r)))
   
   [TRANSLATE_def]  Definition
      
      |- ∀f s. TRANSLATE f s = CONCAT (MAP f s)
   
   [char_BIJ]  Definition
      
      |- (∀a. CHR (ORD a) = a) ∧ ∀r. (λn. n < 256) r ⇔ (ORD (CHR r) = r)
   
   [char_TY_DEF]  Definition
      
      |- ∃rep. TYPE_DEFINITION (λn. n < 256) rep
   
   [char_ge_def]  Definition
      
      |- ∀a b. a ≥ b ⇔ ORD a ≥ ORD b
   
   [char_gt_def]  Definition
      
      |- ∀a b. a > b ⇔ ORD a > ORD b
   
   [char_le_def]  Definition
      
      |- ∀a b. a ≤ b ⇔ ORD a ≤ ORD b
   
   [char_lt_def]  Definition
      
      |- ∀a b. a < b ⇔ ORD a < ORD b
   
   [char_size_def]  Definition
      
      |- ∀c. char_size c = 0
   
   [isAlphaNum_def]  Definition
      
      |- ∀c. isAlphaNum c ⇔ isAlpha c ∨ isDigit c
   
   [isAlpha_def]  Definition
      
      |- ∀c. isAlpha c ⇔ isLower c ∨ isUpper c
   
   [isAscii_def]  Definition
      
      |- ∀c. isAscii c ⇔ ORD c ≤ 127
   
   [isCntrl_def]  Definition
      
      |- ∀c. isCntrl c ⇔ ORD c < 32 ∨ 127 ≤ ORD c
   
   [isDigit_def]  Definition
      
      |- ∀c. isDigit c ⇔ 48 ≤ ORD c ∧ ORD c ≤ 57
   
   [isGraph_def]  Definition
      
      |- ∀c. isGraph c ⇔ isPrint c ∧ ¬isSpace c
   
   [isHexDigit_def]  Definition
      
      |- ∀c.
           isHexDigit c ⇔
           48 ≤ ORD c ∧ ORD c ≤ 57 ∨ 97 ≤ ORD c ∧ ORD c ≤ 102 ∨
           65 ≤ ORD c ∧ ORD c ≤ 70
   
   [isLower_def]  Definition
      
      |- ∀c. isLower c ⇔ 97 ≤ ORD c ∧ ORD c ≤ 122
   
   [isPrint_def]  Definition
      
      |- ∀c. isPrint c ⇔ 32 ≤ ORD c ∧ ORD c < 127
   
   [isPunct_def]  Definition
      
      |- ∀c. isPunct c ⇔ isGraph c ∧ ¬isAlphaNum c
   
   [isSpace_def]  Definition
      
      |- ∀c. isSpace c ⇔ (ORD c = 32) ∨ 9 ≤ ORD c ∧ ORD c ≤ 13
   
   [isUpper_def]  Definition
      
      |- ∀c. isUpper c ⇔ 65 ≤ ORD c ∧ ORD c ≤ 90
   
   [string_ge_def]  Definition
      
      |- ∀s1 s2. s1 ≥ s2 ⇔ s2 ≤ s1
   
   [string_gt_def]  Definition
      
      |- ∀s1 s2. s1 > s2 ⇔ s2 < s1
   
   [string_le_def]  Definition
      
      |- ∀s1 s2. s1 ≤ s2 ⇔ (s1 = s2) ∨ s1 < s2
   
   [string_lt_curried_def]  Definition
      
      |- ∀x x1. x < x1 ⇔ string_lt_tupled (x,x1)
   
   [string_lt_tupled_primitive_def]  Definition
      
      |- string_lt_tupled =
         WFREC (@R. WF R ∧ ∀c2 c1 s2 s1. R (s1,s2) (STRING c1 s1,STRING c2 s2))
           (λstring_lt_tupled a.
              case a of
                 ("","") -> I F
              || ("",STRING c s) -> I T
              || (STRING c1 s1,"") -> I F
              || (STRING c1 s1,STRING c2 s2) ->
                   I (c1 < c2 ∨ (c1 = c2) ∧ string_lt_tupled (s1,s2)))
   
   [toLower_def]  Definition
      
      |- ∀c. toLower c = if isUpper c then CHR (ORD c + 32) else c
   
   [toUpper_def]  Definition
      
      |- ∀c. toUpper c = if isLower c then CHR (ORD c − 32) else c
   
   [CHAR_EQ_THM]  Theorem
      
      |- ∀c1 c2. (c1 = c2) ⇔ (ORD c1 = ORD c2)
   
   [CHAR_INDUCT_THM]  Theorem
      
      |- ∀P. (∀n. n < 256 ⇒ P (CHR n)) ⇒ ∀c. P c
   
   [CHR_11]  Theorem
      
      |- ∀r r'. r < 256 ⇒ r' < 256 ⇒ ((CHR r = CHR r') ⇔ (r = r'))
   
   [CHR_ONTO]  Theorem
      
      |- ∀a. ∃r. (a = CHR r) ∧ r < 256
   
   [CHR_ORD]  Theorem
      
      |- ∀a. CHR (ORD a) = a
   
   [DEST_STRING_LEMS]  Theorem
      
      |- ∀s.
           ((DEST_STRING s = NONE) ⇔ (s = "")) ∧
           ((DEST_STRING s = SOME (c,t)) ⇔ (s = STRING c t))
   
   [EXPLODE_11]  Theorem
      
      |- (EXPLODE s1 = EXPLODE s2) ⇔ (s1 = s2)
   
   [EXPLODE_DEST_STRING]  Theorem
      
      |- ∀s.
           EXPLODE s =
           case DEST_STRING s of NONE -> "" || SOME (c,t) -> STRING c (EXPLODE t)
   
   [EXPLODE_EQNS]  Theorem
      
      |- (EXPLODE "" = "") ∧ ∀c s. EXPLODE (STRING c s) = STRING c (EXPLODE s)
   
   [EXPLODE_EQ_NIL]  Theorem
      
      |- ((EXPLODE s = "") ⇔ (s = "")) ∧ (("" = EXPLODE s) ⇔ (s = ""))
   
   [EXPLODE_EQ_THM]  Theorem
      
      |- ∀s h t.
           ((STRING h t = EXPLODE s) ⇔ (s = STRING h (IMPLODE t))) ∧
           ((EXPLODE s = STRING h t) ⇔ (s = STRING h (IMPLODE t)))
   
   [EXPLODE_IMPLODE]  Theorem
      
      |- EXPLODE (IMPLODE cs) = cs
   
   [EXPLODE_ONTO]  Theorem
      
      |- ∀cs. ∃s. cs = EXPLODE s
   
   [EXTRACT_def]  Theorem
      
      |- (EXTRACT (s,i,NONE) = SUBSTRING (s,i,STRLEN s − i)) ∧
         (EXTRACT (s,i,SOME n) = SUBSTRING (s,i,n))
   
   [EXTRACT_ind]  Theorem
      
      |- ∀P. (∀s i. P (s,i,NONE)) ∧ (∀s i n. P (s,i,SOME n)) ⇒ ∀v v1 v2. P (v,v1,v2)
   
   [FIELDS_def]  Theorem
      
      |- (FIELDS P "" = [""]) ∧
         (FIELDS P (STRING h t) =
          (let (l,r) = SPLITP P (STRING h t)
           in
             if NULL l then
               ""::FIELDS P (TL r)
             else if NULL r then
               [l]
             else
               l::FIELDS P (TL r)))
   
   [FIELDS_ind]  Theorem
      
      |- ∀P'.
           (∀P. P' P "") ∧
           (∀P h t.
              (∀l r. ((l,r) = SPLITP P (STRING h t)) ∧ NULL l ⇒ P' P (TL r)) ∧
              (∀l r.
                 ((l,r) = SPLITP P (STRING h t)) ∧ ¬NULL l ∧ ¬NULL r ⇒ P' P (TL r)) ⇒
              P' P (STRING h t)) ⇒
           ∀v v1. P' v v1
   
   [IMPLODE_11]  Theorem
      
      |- (IMPLODE cs1 = IMPLODE cs2) ⇔ (cs1 = cs2)
   
   [IMPLODE_EQNS]  Theorem
      
      |- (IMPLODE "" = "") ∧ ∀c cs. IMPLODE (STRING c cs) = STRING c (IMPLODE cs)
   
   [IMPLODE_EQ_EMPTYSTRING]  Theorem
      
      |- ((IMPLODE l = "") ⇔ (l = "")) ∧ (("" = IMPLODE l) ⇔ (l = ""))
   
   [IMPLODE_EQ_THM]  Theorem
      
      |- ∀c s l.
           ((STRING c s = IMPLODE l) ⇔ (l = STRING c (EXPLODE s))) ∧
           ((IMPLODE l = STRING c s) ⇔ (l = STRING c (EXPLODE s)))
   
   [IMPLODE_EXPLODE]  Theorem
      
      |- IMPLODE (EXPLODE s) = s
   
   [IMPLODE_EXPLODE_I]  Theorem
      
      |- (EXPLODE s = s) ∧ (IMPLODE s = s)
   
   [IMPLODE_ONTO]  Theorem
      
      |- ∀s. ∃cs. s = IMPLODE cs
   
   [IMPLODE_STRING]  Theorem
      
      |- ∀clist. IMPLODE clist = FOLDR STRING "" clist
   
   [ORD_11]  Theorem
      
      |- ∀a a'. (ORD a = ORD a') ⇔ (a = a')
   
   [ORD_BOUND]  Theorem
      
      |- ∀c. ORD c < 256
   
   [ORD_CHR]  Theorem
      
      |- ∀r. r < 256 ⇔ (ORD (CHR r) = r)
   
   [ORD_CHR_COMPUTE]  Theorem
      
      |- ∀n. ORD (CHR n) = if n < 256 then n else FAIL ORD > 255 (CHR n)
   
   [ORD_CHR_RWT]  Theorem
      
      |- ∀r. r < 256 ⇒ (ORD (CHR r) = r)
   
   [ORD_ONTO]  Theorem
      
      |- ∀r. r < 256 ⇔ ∃a. r = ORD a
   
   [STRCAT]  Theorem
      
      |- STRCAT s1 s2 = STRCAT s1 s2
   
   [STRCAT_11]  Theorem
      
      |- (∀l1 l2 l3. (STRCAT l1 l2 = STRCAT l1 l3) ⇔ (l2 = l3)) ∧
         ∀l1 l2 l3. (STRCAT l2 l1 = STRCAT l3 l1) ⇔ (l2 = l3)
   
   [STRCAT_ACYCLIC]  Theorem
      
      |- ∀s s1. ((s = STRCAT s s1) ⇔ (s1 = "")) ∧ ((s = STRCAT s1 s) ⇔ (s1 = ""))
   
   [STRCAT_ASSOC]  Theorem
      
      |- ∀l1 l2 l3. STRCAT l1 (STRCAT l2 l3) = STRCAT (STRCAT l1 l2) l3
   
   [STRCAT_EQNS]  Theorem
      
      |- (STRCAT "" s = s) ∧ (STRCAT s "" = s) ∧
         (STRCAT (STRING c s1) s2 = STRING c (STRCAT s1 s2))
   
   [STRCAT_EQ_EMPTY]  Theorem
      
      |- ∀l1 l2. (STRCAT l1 l2 = "") ⇔ (l1 = "") ∧ (l2 = "")
   
   [STRCAT_EXPLODE]  Theorem
      
      |- ∀s1 s2. STRCAT s1 s2 = FOLDR STRING s2 (EXPLODE s1)
   
   [STRCAT_def]  Theorem
      
      |- (∀l. STRCAT "" l = l) ∧
         ∀l1 l2 x. STRCAT (STRING x l1) l2 = STRING x (STRCAT l1 l2)
   
   [STRING_ACYCLIC]  Theorem
      
      |- ∀s c. STRING c s ≠ s ∧ s ≠ STRING c s
   
   [STRLEN_CAT]  Theorem
      
      |- ∀l1 l2. STRLEN (STRCAT l1 l2) = STRLEN l1 + STRLEN l2
   
   [STRLEN_DEF]  Theorem
      
      |- (STRLEN "" = 0) ∧ ∀x l. STRLEN (STRING x l) = SUC (STRLEN l)
   
   [STRLEN_EQ_0]  Theorem
      
      |- ∀l. (STRLEN l = 0) ⇔ (l = "")
   
   [STRLEN_EXPLODE_THM]  Theorem
      
      |- STRLEN s = STRLEN (EXPLODE s)
   
   [STRLEN_THM]  Theorem
      
      |- (STRLEN "" = 0) ∧ ∀x l. STRLEN (STRING x l) = SUC (STRLEN l)
   
   [TOKENS_def]  Theorem
      
      |- (TOKENS P "" = []) ∧
         (TOKENS P (STRING h t) =
          (let (l,r) = SPLITP P (STRING h t)
           in
             if NULL l then TOKENS P (TL r) else l::TOKENS P r))
   
   [TOKENS_ind]  Theorem
      
      |- ∀P'.
           (∀P. P' P "") ∧
           (∀P h t.
              (∀l r. ((l,r) = SPLITP P (STRING h t)) ∧ NULL l ⇒ P' P (TL r)) ∧
              (∀l r. ((l,r) = SPLITP P (STRING h t)) ∧ ¬NULL l ⇒ P' P r) ⇒
              P' P (STRING h t)) ⇒
           ∀v v1. P' v v1
   
   [char_nchotomy]  Theorem
      
      |- ∀c. ∃n. c = CHR n
   
   [isPREFIX_DEF]  Theorem
      
      |- ∀s1 s2.
           s1 ≼ s2 ⇔
           case (DEST_STRING s1,DEST_STRING s2) of
              (NONE,v1) -> T
           || (SOME (c1,t1),NONE) -> F
           || (SOME (c1,t1),SOME (c2,t2)) -> (c1 = c2) ∧ t1 ≼ t2
   
   [isPREFIX_IND]  Theorem
      
      |- ∀P.
           (∀s1 s2.
              (∀c t1 t2.
                 (DEST_STRING s1 = SOME (c,t1)) ∧ (DEST_STRING s2 = SOME (c,t2)) ⇒
                 P t1 t2) ⇒
              P s1 s2) ⇒
           ∀v v1. P v v1
   
   [isPREFIX_STRCAT]  Theorem
      
      |- ∀s1 s2. s1 ≼ s2 ⇔ ∃s3. s2 = STRCAT s1 s3
   
   [ranged_char_nchotomy]  Theorem
      
      |- ∀c. ∃n. (c = CHR n) ∧ n < 256
   
   [string_lt_antisym]  Theorem
      
      |- ∀s t. ¬(s < t ∧ t < s)
   
   [string_lt_cases]  Theorem
      
      |- ∀s t. (s = t) ∨ s < t ∨ t < s
   
   [string_lt_def]  Theorem
      
      |- ("" < "" ⇔ F) ∧ (∀v3 v2. STRING v2 v3 < "" ⇔ F) ∧
         (∀s c. "" < STRING c s ⇔ T) ∧
         ∀s2 s1 c2 c1. STRING c1 s1 < STRING c2 s2 ⇔ c1 < c2 ∨ (c1 = c2) ∧ s1 < s2
   
   [string_lt_ind]  Theorem
      
      |- ∀P.
           P "" "" ∧ (∀v2 v3. P (STRING v2 v3) "") ∧ (∀c s. P "" (STRING c s)) ∧
           (∀c1 s1 c2 s2. P s1 s2 ⇒ P (STRING c1 s1) (STRING c2 s2)) ⇒
           ∀v v1. P v v1
   
   [string_lt_nonrefl]  Theorem
      
      |- ∀s. ¬(s < s)
   
   [string_lt_trans]  Theorem
      
      |- ∀s1 s2 s3. s1 < s2 ∧ s2 < s3 ⇒ s1 < s3
   
   
*)
end
