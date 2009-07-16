signature rich_listTheory =
sig
  type thm = Thm.thm
  
  (*  Definitions  *)
    val AND_EL_DEF : thm
    val BUTLASTN : thm
    val ELL : thm
    val GENLIST : thm
    val IS_SUBLIST : thm
    val IS_SUFFIX : thm
    val LASTN : thm
    val LIST_ELEM_COUNT_DEF : thm
    val OR_EL_DEF : thm
    val PREFIX_DEF : thm
    val REPLACE_ELEMENT_DEF : thm
    val REPLICATE : thm
    val SCANL : thm
    val SCANR : thm
    val SEG : thm
    val SNOC : thm
    val SPLITP : thm
    val SUFFIX_DEF : thm
    val UNZIP_FST_DEF : thm
    val UNZIP_SND_DEF : thm
  
  (*  Theorems  *)
    val ALL_DISTINCT_SNOC : thm
    val ALL_EL : thm
    val ALL_EL_APPEND : thm
    val ALL_EL_BUTFIRSTN : thm
    val ALL_EL_BUTLASTN : thm
    val ALL_EL_CONJ : thm
    val ALL_EL_FIRSTN : thm
    val ALL_EL_FOLDL : thm
    val ALL_EL_FOLDL_MAP : thm
    val ALL_EL_FOLDR : thm
    val ALL_EL_FOLDR_MAP : thm
    val ALL_EL_LASTN : thm
    val ALL_EL_MAP : thm
    val ALL_EL_REPLICATE : thm
    val ALL_EL_REVERSE : thm
    val ALL_EL_SEG : thm
    val ALL_EL_SNOC : thm
    val AND_EL_FOLDL : thm
    val AND_EL_FOLDR : thm
    val APPEND : thm
    val APPEND_ASSOC : thm
    val APPEND_ASSOC_CONS : thm
    val APPEND_BUTLASTN_BUTFIRSTN : thm
    val APPEND_BUTLASTN_LASTN : thm
    val APPEND_BUTLAST_LAST : thm
    val APPEND_FIRSTN_BUTFIRSTN : thm
    val APPEND_FIRSTN_LASTN : thm
    val APPEND_FOLDL : thm
    val APPEND_FOLDR : thm
    val APPEND_LENGTH_EQ : thm
    val APPEND_NIL : thm
    val APPEND_SNOC : thm
    val APPEND_SNOC1 : thm
    val ASSOC_APPEND : thm
    val ASSOC_FOLDL_FLAT : thm
    val ASSOC_FOLDR_FLAT : thm
    val BUTFIRSTN : thm
    val BUTFIRSTN_APPEND1 : thm
    val BUTFIRSTN_APPEND2 : thm
    val BUTFIRSTN_BUTFIRSTN : thm
    val BUTFIRSTN_CONS_EL : thm
    val BUTFIRSTN_LASTN : thm
    val BUTFIRSTN_LENGTH_APPEND : thm
    val BUTFIRSTN_LENGTH_NIL : thm
    val BUTFIRSTN_REVERSE : thm
    val BUTFIRSTN_SEG : thm
    val BUTFIRSTN_SNOC : thm
    val BUTFIRSTN_compute : thm
    val BUTLAST : thm
    val BUTLASTN_1 : thm
    val BUTLASTN_APPEND1 : thm
    val BUTLASTN_APPEND2 : thm
    val BUTLASTN_BUTLAST : thm
    val BUTLASTN_BUTLASTN : thm
    val BUTLASTN_CONS : thm
    val BUTLASTN_FIRSTN : thm
    val BUTLASTN_LASTN : thm
    val BUTLASTN_LASTN_NIL : thm
    val BUTLASTN_LENGTH_APPEND : thm
    val BUTLASTN_LENGTH_CONS : thm
    val BUTLASTN_LENGTH_NIL : thm
    val BUTLASTN_MAP : thm
    val BUTLASTN_REVERSE : thm
    val BUTLASTN_SEG : thm
    val BUTLASTN_SUC_BUTLAST : thm
    val BUTLASTN_compute : thm
    val BUTLAST_CONS : thm
    val COMM_ASSOC_FOLDL_REVERSE : thm
    val COMM_ASSOC_FOLDR_REVERSE : thm
    val COMM_MONOID_FOLDL : thm
    val COMM_MONOID_FOLDR : thm
    val CONS : thm
    val CONS_11 : thm
    val CONS_APPEND : thm
    val EL : thm
    val ELL_0_SNOC : thm
    val ELL_APPEND1 : thm
    val ELL_APPEND2 : thm
    val ELL_CONS : thm
    val ELL_EL : thm
    val ELL_IS_EL : thm
    val ELL_LAST : thm
    val ELL_LENGTH_APPEND : thm
    val ELL_LENGTH_CONS : thm
    val ELL_LENGTH_SNOC : thm
    val ELL_MAP : thm
    val ELL_PRE_LENGTH : thm
    val ELL_REVERSE : thm
    val ELL_REVERSE_EL : thm
    val ELL_SEG : thm
    val ELL_SNOC : thm
    val ELL_SUC_SNOC : thm
    val ELL_compute : thm
    val EL_APPEND1 : thm
    val EL_APPEND2 : thm
    val EL_BUTFIRSTN : thm
    val EL_CONS : thm
    val EL_ELL : thm
    val EL_FIRSTN : thm
    val EL_FRONT : thm
    val EL_GENLIST : thm
    val EL_IS_EL : thm
    val EL_LENGTH_APPEND : thm
    val EL_LENGTH_SNOC : thm
    val EL_MAP : thm
    val EL_PRE_LENGTH : thm
    val EL_REVERSE : thm
    val EL_REVERSE_ELL : thm
    val EL_SEG : thm
    val EL_SNOC : thm
    val EQ_LIST : thm
    val EVERY_GENLIST : thm
    val FCOMM_FOLDL_APPEND : thm
    val FCOMM_FOLDL_FLAT : thm
    val FCOMM_FOLDR_APPEND : thm
    val FCOMM_FOLDR_FLAT : thm
    val FILTER : thm
    val FILTER_APPEND : thm
    val FILTER_COMM : thm
    val FILTER_FILTER : thm
    val FILTER_FLAT : thm
    val FILTER_FOLDL : thm
    val FILTER_FOLDR : thm
    val FILTER_IDEM : thm
    val FILTER_MAP : thm
    val FILTER_REVERSE : thm
    val FILTER_SNOC : thm
    val FIRSTN : thm
    val FIRSTN_APPEND1 : thm
    val FIRSTN_APPEND2 : thm
    val FIRSTN_BUTLASTN : thm
    val FIRSTN_FIRSTN : thm
    val FIRSTN_LENGTH_APPEND : thm
    val FIRSTN_LENGTH_ID : thm
    val FIRSTN_REVERSE : thm
    val FIRSTN_SEG : thm
    val FIRSTN_SNOC : thm
    val FIRSTN_compute : thm
    val FLAT : thm
    val FLAT_APPEND : thm
    val FLAT_FLAT : thm
    val FLAT_FOLDL : thm
    val FLAT_FOLDR : thm
    val FLAT_REVERSE : thm
    val FLAT_SNOC : thm
    val FOLDL : thm
    val FOLDL_APPEND : thm
    val FOLDL_FILTER : thm
    val FOLDL_FOLDR_REVERSE : thm
    val FOLDL_MAP : thm
    val FOLDL_MAP2 : thm
    val FOLDL_REVERSE : thm
    val FOLDL_SINGLE : thm
    val FOLDL_SNOC : thm
    val FOLDL_SNOC_NIL : thm
    val FOLDR : thm
    val FOLDR_APPEND : thm
    val FOLDR_CONS_NIL : thm
    val FOLDR_FILTER : thm
    val FOLDR_FILTER_REVERSE : thm
    val FOLDR_FOLDL : thm
    val FOLDR_FOLDL_REVERSE : thm
    val FOLDR_MAP : thm
    val FOLDR_MAP_REVERSE : thm
    val FOLDR_REVERSE : thm
    val FOLDR_SINGLE : thm
    val FOLDR_SNOC : thm
    val FRONT_APPEND : thm
    val FRONT___LENGTH : thm
    val GENLIST_APPEND : thm
    val GENLIST_FUN_EQ : thm
    val GENLIST_compute : thm
    val HD : thm
    val HD_GENLIST : thm
    val IS_EL : thm
    val IS_EL_APPEND : thm
    val IS_EL_BUTFIRSTN : thm
    val IS_EL_BUTLASTN : thm
    val IS_EL_DEF : thm
    val IS_EL_FILTER : thm
    val IS_EL_FIRSTN : thm
    val IS_EL_FOLDL : thm
    val IS_EL_FOLDL_MAP : thm
    val IS_EL_FOLDR : thm
    val IS_EL_FOLDR_MAP : thm
    val IS_EL_LASTN : thm
    val IS_EL_REPLICATE : thm
    val IS_EL_REVERSE : thm
    val IS_EL_SEG : thm
    val IS_EL_SNOC : thm
    val IS_EL_SOME_EL : thm
    val IS_PREFIX : thm
    val IS_PREFIX_ANTISYM : thm
    val IS_PREFIX_APPEND : thm
    val IS_PREFIX_APPEND1 : thm
    val IS_PREFIX_APPEND2 : thm
    val IS_PREFIX_APPENDS : thm
    val IS_PREFIX_BUTLAST : thm
    val IS_PREFIX_IS_SUBLIST : thm
    val IS_PREFIX_LENGTH : thm
    val IS_PREFIX_LENGTH_ANTI : thm
    val IS_PREFIX_NIL : thm
    val IS_PREFIX_PREFIX : thm
    val IS_PREFIX_REFL : thm
    val IS_PREFIX_REVERSE : thm
    val IS_PREFIX_SNOC : thm
    val IS_PREFIX_TRANS : thm
    val IS_SUBLIST_APPEND : thm
    val IS_SUBLIST_REVERSE : thm
    val IS_SUFFIX_APPEND : thm
    val IS_SUFFIX_IS_SUBLIST : thm
    val IS_SUFFIX_REVERSE : thm
    val IS_SUFFIX_compute : thm
    val LAST : thm
    val LASTN_1 : thm
    val LASTN_APPEND1 : thm
    val LASTN_APPEND2 : thm
    val LASTN_BUTFIRSTN : thm
    val LASTN_BUTLASTN : thm
    val LASTN_CONS : thm
    val LASTN_LASTN : thm
    val LASTN_LENGTH_APPEND : thm
    val LASTN_LENGTH_ID : thm
    val LASTN_MAP : thm
    val LASTN_REVERSE : thm
    val LASTN_SEG : thm
    val LASTN_compute : thm
    val LAST_APPEND : thm
    val LAST_CONS : thm
    val LAST_LASTN_LAST : thm
    val LENGTH : thm
    val LENGTH_APPEND : thm
    val LENGTH_BUTFIRSTN : thm
    val LENGTH_BUTLAST : thm
    val LENGTH_BUTLASTN : thm
    val LENGTH_CONS : thm
    val LENGTH_EQ : thm
    val LENGTH_EQ_NIL : thm
    val LENGTH_FIRSTN : thm
    val LENGTH_FLAT : thm
    val LENGTH_FOLDL : thm
    val LENGTH_FOLDR : thm
    val LENGTH_GENLIST : thm
    val LENGTH_LASTN : thm
    val LENGTH_MAP : thm
    val LENGTH_MAP2 : thm
    val LENGTH_NIL : thm
    val LENGTH_NOT_NULL : thm
    val LENGTH_REPLICATE : thm
    val LENGTH_REVERSE : thm
    val LENGTH_SCANL : thm
    val LENGTH_SCANR : thm
    val LENGTH_SEG : thm
    val LENGTH_SNOC : thm
    val LENGTH_UNZIP_FST : thm
    val LENGTH_UNZIP_SND : thm
    val LENGTH_ZIP : thm
    val LIST_ELEM_COUNT_MEM : thm
    val LIST_ELEM_COUNT_THM : thm
    val LIST_NOT_EQ : thm
    val MAP : thm
    val MAP2 : thm
    val MAP2_ZIP : thm
    val MAP_APPEND : thm
    val MAP_EQ_f : thm
    val MAP_FILTER : thm
    val MAP_FLAT : thm
    val MAP_FOLDL : thm
    val MAP_FOLDR : thm
    val MAP_GENLIST : thm
    val MAP_MAP_o : thm
    val MAP_REVERSE : thm
    val MAP_SNOC : thm
    val MAP_o : thm
    val MEM_FRONT : thm
    val MEM_LAST : thm
    val MEM_LAST_FRONT : thm
    val MONOID_APPEND_NIL : thm
    val NOT_ALL_EL_SOME_EL : thm
    val NOT_CONS_NIL : thm
    val NOT_EQ_LIST : thm
    val NOT_NIL_CONS : thm
    val NOT_NIL_SNOC : thm
    val NOT_NULL_SNOC : thm
    val NOT_SNOC_NIL : thm
    val NOT_SOME_EL_ALL_EL : thm
    val NULL : thm
    val NULL_DEF : thm
    val NULL_EQ_NIL : thm
    val NULL_FOLDL : thm
    val NULL_FOLDR : thm
    val OR_EL_FOLDL : thm
    val OR_EL_FOLDR : thm
    val PREFIX : thm
    val PREFIX_FOLDR : thm
    val REPLACE_ELEMENT_SEM : thm
    val REPLICATE_compute : thm
    val REVERSE : thm
    val REVERSE_APPEND : thm
    val REVERSE_EQ_NIL : thm
    val REVERSE_FLAT : thm
    val REVERSE_FOLDL : thm
    val REVERSE_FOLDR : thm
    val REVERSE_REVERSE : thm
    val REVERSE_SNOC : thm
    val SEG_0_SNOC : thm
    val SEG_APPEND : thm
    val SEG_APPEND1 : thm
    val SEG_APPEND2 : thm
    val SEG_FIRSTN_BUTFISTN : thm
    val SEG_LASTN_BUTLASTN : thm
    val SEG_LENGTH_ID : thm
    val SEG_LENGTH_SNOC : thm
    val SEG_REVERSE : thm
    val SEG_SEG : thm
    val SEG_SNOC : thm
    val SEG_SUC_CONS : thm
    val SEG_compute : thm
    val SNOC_11 : thm
    val SNOC_APPEND : thm
    val SNOC_Axiom : thm
    val SNOC_CASES : thm
    val SNOC_EL_FIRSTN : thm
    val SNOC_EQ_LENGTH_EQ : thm
    val SNOC_FOLDR : thm
    val SNOC_INDUCT : thm
    val SNOC_REVERSE_CONS : thm
    val SOME_EL : thm
    val SOME_EL_APPEND : thm
    val SOME_EL_BUTFIRSTN : thm
    val SOME_EL_BUTLASTN : thm
    val SOME_EL_DISJ : thm
    val SOME_EL_FIRSTN : thm
    val SOME_EL_FOLDL : thm
    val SOME_EL_FOLDL_MAP : thm
    val SOME_EL_FOLDR : thm
    val SOME_EL_FOLDR_MAP : thm
    val SOME_EL_LASTN : thm
    val SOME_EL_MAP : thm
    val SOME_EL_REVERSE : thm
    val SOME_EL_SEG : thm
    val SOME_EL_SNOC : thm
    val SPLITP_EVERY : thm
    val SUM : thm
    val SUM_APPEND : thm
    val SUM_FLAT : thm
    val SUM_FOLDL : thm
    val SUM_FOLDR : thm
    val SUM_REVERSE : thm
    val SUM_SNOC : thm
    val TL : thm
    val TL_SNOC : thm
    val UNZIP : thm
    val UNZIP_SNOC : thm
    val UNZIP_ZIP : thm
    val ZIP : thm
    val ZIP_APPEND : thm
    val ZIP_FIRSTN : thm
    val ZIP_FIRSTN_LEQ : thm
    val ZIP_GENLIST : thm
    val ZIP_SNOC : thm
    val ZIP_UNZIP : thm
    val list_CASES : thm
    val list_INDUCT : thm
  
  val rich_list_grammars : type_grammar.grammar * term_grammar.grammar
  
  
(*
   [list] Parent theory of "rich_list"
   
   [AND_EL_DEF]  Definition
      
      |- AND_EL = EVERY I
   
   [BUTLASTN]  Definition
      
      |- (!l. BUTLASTN 0 l = l) /\
         !n x l. BUTLASTN (SUC n) (SNOC x l) = BUTLASTN n l
   
   [ELL]  Definition
      
      |- (!l. ELL 0 l = LAST l) /\ !n l. ELL (SUC n) l = ELL n (FRONT l)
   
   [GENLIST]  Definition
      
      |- (!f. GENLIST f 0 = []) /\
         !f n. GENLIST f (SUC n) = SNOC (f n) (GENLIST f n)
   
   [IS_SUBLIST]  Definition
      
      |- (!l. IS_SUBLIST l [] <=> T) /\
         (!x l. IS_SUBLIST [] (x::l) <=> F) /\
         !x1 l1 x2 l2.
           IS_SUBLIST (x1::l1) (x2::l2) <=>
           (x1 = x2) /\ l2 <<= l1 \/ IS_SUBLIST l1 (x2::l2)
   
   [IS_SUFFIX]  Definition
      
      |- (!l. IS_SUFFIX l [] <=> T) /\
         (!x l. IS_SUFFIX [] (SNOC x l) <=> F) /\
         !x1 l1 x2 l2.
           IS_SUFFIX (SNOC x1 l1) (SNOC x2 l2) <=>
           (x1 = x2) /\ IS_SUFFIX l1 l2
   
   [LASTN]  Definition
      
      |- (!l. LASTN 0 l = []) /\
         !n x l. LASTN (SUC n) (SNOC x l) = SNOC x (LASTN n l)
   
   [LIST_ELEM_COUNT_DEF]  Definition
      
      |- !e l. LIST_ELEM_COUNT e l = LENGTH (FILTER (\x. x = e) l)
   
   [OR_EL_DEF]  Definition
      
      |- OR_EL = EXISTS I
   
   [PREFIX_DEF]  Definition
      
      |- !P l. PREFIX P l = FST (SPLITP ($~ o P) l)
   
   [REPLACE_ELEMENT_DEF]  Definition
      
      |- (!e n. REPLACE_ELEMENT e n [] = []) /\
         (!e x l. REPLACE_ELEMENT e 0 (x::l) = e::l) /\
         !e n x l.
           REPLACE_ELEMENT e (SUC n) (x::l) = x::REPLACE_ELEMENT e n l
   
   [REPLICATE]  Definition
      
      |- (!x. REPLICATE 0 x = []) /\
         !n x. REPLICATE (SUC n) x = x::REPLICATE n x
   
   [SCANL]  Definition
      
      |- (!f e. SCANL f e [] = [e]) /\
         !f e x l. SCANL f e (x::l) = e::SCANL f (f e x) l
   
   [SCANR]  Definition
      
      |- (!f e. SCANR f e [] = [e]) /\
         !f e x l. SCANR f e (x::l) = f x (HD (SCANR f e l))::SCANR f e l
   
   [SEG]  Definition
      
      |- (!k l. SEG 0 k l = []) /\
         (!m x l. SEG (SUC m) 0 (x::l) = x::SEG m 0 l) /\
         !m k x l. SEG (SUC m) (SUC k) (x::l) = SEG (SUC m) k l
   
   [SNOC]  Definition
      
      |- (!x. SNOC x [] = [x]) /\ !x x' l. SNOC x (x'::l) = x'::SNOC x l
   
   [SPLITP]  Definition
      
      |- (!P. SPLITP P [] = ([],[])) /\
         !P x l.
           SPLITP P (x::l) =
           if P x then
             ([],x::l)
           else
             (x::FST (SPLITP P l),SND (SPLITP P l))
   
   [SUFFIX_DEF]  Definition
      
      |- !P l.
           SUFFIX P l = FOLDL (\l' x. if P x then SNOC x l' else []) [] l
   
   [UNZIP_FST_DEF]  Definition
      
      |- !l. UNZIP_FST l = FST (UNZIP l)
   
   [UNZIP_SND_DEF]  Definition
      
      |- !l. UNZIP_SND l = SND (UNZIP l)
   
   [ALL_DISTINCT_SNOC]  Theorem
      
      |- !x l. ALL_DISTINCT (SNOC x l) <=> ~MEM x l /\ ALL_DISTINCT l
   
   [ALL_EL]  Theorem
      
      |- (!P. EVERY P [] <=> T) /\
         !P h t. EVERY P (h::t) <=> P h /\ EVERY P t
   
   [ALL_EL_APPEND]  Theorem
      
      |- !P l1 l2. EVERY P (l1 ++ l2) <=> EVERY P l1 /\ EVERY P l2
   
   [ALL_EL_BUTFIRSTN]  Theorem
      
      |- !P l. EVERY P l ==> !m. m <= LENGTH l ==> EVERY P (DROP m l)
   
   [ALL_EL_BUTLASTN]  Theorem
      
      |- !P l. EVERY P l ==> !m. m <= LENGTH l ==> EVERY P (BUTLASTN m l)
   
   [ALL_EL_CONJ]  Theorem
      
      |- !P Q l. EVERY (\x. P x /\ Q x) l <=> EVERY P l /\ EVERY Q l
   
   [ALL_EL_FIRSTN]  Theorem
      
      |- !P l. EVERY P l ==> !m. m <= LENGTH l ==> EVERY P (TAKE m l)
   
   [ALL_EL_FOLDL]  Theorem
      
      |- !P l. EVERY P l <=> FOLDL (\l' x. l' /\ P x) T l
   
   [ALL_EL_FOLDL_MAP]  Theorem
      
      |- !P l. EVERY P l <=> FOLDL $/\ T (MAP P l)
   
   [ALL_EL_FOLDR]  Theorem
      
      |- !P l. EVERY P l <=> FOLDR (\x l'. P x /\ l') T l
   
   [ALL_EL_FOLDR_MAP]  Theorem
      
      |- !P l. EVERY P l <=> FOLDR $/\ T (MAP P l)
   
   [ALL_EL_LASTN]  Theorem
      
      |- !P l. EVERY P l ==> !m. m <= LENGTH l ==> EVERY P (LASTN m l)
   
   [ALL_EL_MAP]  Theorem
      
      |- !P f l. EVERY P (MAP f l) <=> EVERY (P o f) l
   
   [ALL_EL_REPLICATE]  Theorem
      
      |- !x n. EVERY ($= x) (REPLICATE n x)
   
   [ALL_EL_REVERSE]  Theorem
      
      |- !P l. EVERY P (REVERSE l) <=> EVERY P l
   
   [ALL_EL_SEG]  Theorem
      
      |- !P l.
           EVERY P l ==> !m k. m + k <= LENGTH l ==> EVERY P (SEG m k l)
   
   [ALL_EL_SNOC]  Theorem
      
      |- !P x l. EVERY P (SNOC x l) <=> EVERY P l /\ P x
   
   [AND_EL_FOLDL]  Theorem
      
      |- !l. AND_EL l <=> FOLDL $/\ T l
   
   [AND_EL_FOLDR]  Theorem
      
      |- !l. AND_EL l <=> FOLDR $/\ T l
   
   [APPEND]  Theorem
      
      |- (!l. [] ++ l = l) /\ !l1 l2 x. x::l1 ++ l2 = x::(l1 ++ l2)
   
   [APPEND_ASSOC]  Theorem
      
      |- !l1 l2 l3. l1 ++ (l2 ++ l3) = l1 ++ l2 ++ l3
   
   [APPEND_ASSOC_CONS]  Theorem
      
      |- !l1 h l2 l3. l1 ++ h::l2 ++ l3 = l1 ++ h::(l2 ++ l3)
   
   [APPEND_BUTLASTN_BUTFIRSTN]  Theorem
      
      |- !m n l. (m + n = LENGTH l) ==> (BUTLASTN m l ++ DROP n l = l)
   
   [APPEND_BUTLASTN_LASTN]  Theorem
      
      |- !n l. n <= LENGTH l ==> (BUTLASTN n l ++ LASTN n l = l)
   
   [APPEND_BUTLAST_LAST]  Theorem
      
      |- !l. l <> [] ==> (FRONT l ++ [LAST l] = l)
   
   [APPEND_FIRSTN_BUTFIRSTN]  Theorem
      
      |- !n l. n <= LENGTH l ==> (TAKE n l ++ DROP n l = l)
   
   [APPEND_FIRSTN_LASTN]  Theorem
      
      |- !m n l. (m + n = LENGTH l) ==> (TAKE n l ++ LASTN m l = l)
   
   [APPEND_FOLDL]  Theorem
      
      |- !l1 l2. l1 ++ l2 = FOLDL (\l' x. SNOC x l') l1 l2
   
   [APPEND_FOLDR]  Theorem
      
      |- !l1 l2. l1 ++ l2 = FOLDR CONS l2 l1
   
   [APPEND_LENGTH_EQ]  Theorem
      
      |- !l1 l1'.
           (LENGTH l1 = LENGTH l1') ==>
           !l2 l2'.
             (LENGTH l2 = LENGTH l2') ==>
             ((l1 ++ l2 = l1' ++ l2') <=> (l1 = l1') /\ (l2 = l2'))
   
   [APPEND_NIL]  Theorem
      
      |- (!l. l ++ [] = l) /\ !l. [] ++ l = l
   
   [APPEND_SNOC]  Theorem
      
      |- !l1 x l2. l1 ++ SNOC x l2 = SNOC x (l1 ++ l2)
   
   [APPEND_SNOC1]  Theorem
      
      |- !l1 x l2. SNOC x l1 ++ l2 = l1 ++ x::l2
   
   [ASSOC_APPEND]  Theorem
      
      |- ASSOC $++
   
   [ASSOC_FOLDL_FLAT]  Theorem
      
      |- !f.
           ASSOC f ==>
           !e.
             RIGHT_ID f e ==>
             !l. FOLDL f e (FLAT l) = FOLDL f e (MAP (FOLDL f e) l)
   
   [ASSOC_FOLDR_FLAT]  Theorem
      
      |- !f.
           ASSOC f ==>
           !e.
             LEFT_ID f e ==>
             !l. FOLDR f e (FLAT l) = FOLDR f e (MAP (FOLDR f e) l)
   
   [BUTFIRSTN]  Theorem
      
      |- (!l. DROP 0 l = l) /\ !n x l. DROP (SUC n) (x::l) = DROP n l
   
   [BUTFIRSTN_APPEND1]  Theorem
      
      |- !n l1. n <= LENGTH l1 ==> !l2. DROP n (l1 ++ l2) = DROP n l1 ++ l2
   
   [BUTFIRSTN_APPEND2]  Theorem
      
      |- !l1 n.
           LENGTH l1 <= n ==>
           !l2. DROP n (l1 ++ l2) = DROP (n - LENGTH l1) l2
   
   [BUTFIRSTN_BUTFIRSTN]  Theorem
      
      |- !n m l. n + m <= LENGTH l ==> (DROP n (DROP m l) = DROP (n + m) l)
   
   [BUTFIRSTN_CONS_EL]  Theorem
      
      |- !n. n < LENGTH l ==> (DROP n l = EL n l::DROP (SUC n) l)
   
   [BUTFIRSTN_LASTN]  Theorem
      
      |- !n l. n <= LENGTH l ==> (DROP n l = LASTN (LENGTH l - n) l)
   
   [BUTFIRSTN_LENGTH_APPEND]  Theorem
      
      |- !l1 l2. DROP (LENGTH l1) (l1 ++ l2) = l2
   
   [BUTFIRSTN_LENGTH_NIL]  Theorem
      
      |- !l. DROP (LENGTH l) l = []
   
   [BUTFIRSTN_REVERSE]  Theorem
      
      |- !n l.
           n <= LENGTH l ==> (DROP n (REVERSE l) = REVERSE (BUTLASTN n l))
   
   [BUTFIRSTN_SEG]  Theorem
      
      |- !n l. n <= LENGTH l ==> (DROP n l = SEG (LENGTH l - n) n l)
   
   [BUTFIRSTN_SNOC]  Theorem
      
      |- !n l. n <= LENGTH l ==> !x. DROP n (SNOC x l) = SNOC x (DROP n l)
   
   [BUTFIRSTN_compute]  Theorem
      
      |- (!l. DROP 0 l = l) /\
         (!n x l.
            DROP (NUMERAL (BIT1 n)) (x::l) =
            DROP (NUMERAL (BIT1 n) - 1) l) /\
         !n x l. DROP (NUMERAL (BIT2 n)) (x::l) = DROP (NUMERAL (BIT1 n)) l
   
   [BUTLAST]  Theorem
      
      |- !x l. FRONT (SNOC x l) = l
   
   [BUTLASTN_1]  Theorem
      
      |- !l. l <> [] ==> (BUTLASTN 1 l = FRONT l)
   
   [BUTLASTN_APPEND1]  Theorem
      
      |- !l2 n.
           LENGTH l2 <= n ==>
           !l1. BUTLASTN n (l1 ++ l2) = BUTLASTN (n - LENGTH l2) l1
   
   [BUTLASTN_APPEND2]  Theorem
      
      |- !n l1 l2.
           n <= LENGTH l2 ==> (BUTLASTN n (l1 ++ l2) = l1 ++ BUTLASTN n l2)
   
   [BUTLASTN_BUTLAST]  Theorem
      
      |- !n l.
           n < LENGTH l ==> (BUTLASTN n (FRONT l) = FRONT (BUTLASTN n l))
   
   [BUTLASTN_BUTLASTN]  Theorem
      
      |- !m n l.
           n + m <= LENGTH l ==>
           (BUTLASTN n (BUTLASTN m l) = BUTLASTN (n + m) l)
   
   [BUTLASTN_CONS]  Theorem
      
      |- !n l. n <= LENGTH l ==> !x. BUTLASTN n (x::l) = x::BUTLASTN n l
   
   [BUTLASTN_FIRSTN]  Theorem
      
      |- !n l. n <= LENGTH l ==> (BUTLASTN n l = TAKE (LENGTH l - n) l)
   
   [BUTLASTN_LASTN]  Theorem
      
      |- !m n l.
           m <= n /\ n <= LENGTH l ==>
           (BUTLASTN m (LASTN n l) = LASTN (n - m) (BUTLASTN m l))
   
   [BUTLASTN_LASTN_NIL]  Theorem
      
      |- !n l. n <= LENGTH l ==> (BUTLASTN n (LASTN n l) = [])
   
   [BUTLASTN_LENGTH_APPEND]  Theorem
      
      |- !l2 l1. BUTLASTN (LENGTH l2) (l1 ++ l2) = l1
   
   [BUTLASTN_LENGTH_CONS]  Theorem
      
      |- !l x. BUTLASTN (LENGTH l) (x::l) = [x]
   
   [BUTLASTN_LENGTH_NIL]  Theorem
      
      |- !l. BUTLASTN (LENGTH l) l = []
   
   [BUTLASTN_MAP]  Theorem
      
      |- !n l.
           n <= LENGTH l ==>
           !f. BUTLASTN n (MAP f l) = MAP f (BUTLASTN n l)
   
   [BUTLASTN_REVERSE]  Theorem
      
      |- !n l.
           n <= LENGTH l ==> (BUTLASTN n (REVERSE l) = REVERSE (DROP n l))
   
   [BUTLASTN_SEG]  Theorem
      
      |- !n l. n <= LENGTH l ==> (BUTLASTN n l = SEG (LENGTH l - n) 0 l)
   
   [BUTLASTN_SUC_BUTLAST]  Theorem
      
      |- !n l. n < LENGTH l ==> (BUTLASTN (SUC n) l = BUTLASTN n (FRONT l))
   
   [BUTLASTN_compute]  Theorem
      
      |- !n l.
           BUTLASTN n l =
           (let m = LENGTH l in
              if n <= m then
                TAKE (m - n) l
              else
                FAIL BUTLASTN longer than list n l)
   
   [BUTLAST_CONS]  Theorem
      
      |- (!x. FRONT [x] = []) /\ !x y z. FRONT (x::y::z) = x::FRONT (y::z)
   
   [COMM_ASSOC_FOLDL_REVERSE]  Theorem
      
      |- !f.
           COMM f ==> ASSOC f ==> !e l. FOLDL f e (REVERSE l) = FOLDL f e l
   
   [COMM_ASSOC_FOLDR_REVERSE]  Theorem
      
      |- !f.
           COMM f ==> ASSOC f ==> !e l. FOLDR f e (REVERSE l) = FOLDR f e l
   
   [COMM_MONOID_FOLDL]  Theorem
      
      |- !f.
           COMM f ==>
           !e'. MONOID f e' ==> !e l. FOLDL f e l = f e (FOLDL f e' l)
   
   [COMM_MONOID_FOLDR]  Theorem
      
      |- !f.
           COMM f ==>
           !e'. MONOID f e' ==> !e l. FOLDR f e l = f e (FOLDR f e' l)
   
   [CONS]  Theorem
      
      |- !l. ~NULL l ==> (HD l::TL l = l)
   
   [CONS_11]  Theorem
      
      |- !x l x' l'. (x::l = x'::l') <=> (x = x') /\ (l = l')
   
   [CONS_APPEND]  Theorem
      
      |- !x l. x::l = [x] ++ l
   
   [EL]  Theorem
      
      |- (!l. EL 0 l = HD l) /\ !n l. EL (SUC n) l = EL n (TL l)
   
   [ELL_0_SNOC]  Theorem
      
      |- !l x. ELL 0 (SNOC x l) = x
   
   [ELL_APPEND1]  Theorem
      
      |- !l2 n.
           LENGTH l2 <= n ==>
           !l1. ELL n (l1 ++ l2) = ELL (n - LENGTH l2) l1
   
   [ELL_APPEND2]  Theorem
      
      |- !n l2. n < LENGTH l2 ==> !l1. ELL n (l1 ++ l2) = ELL n l2
   
   [ELL_CONS]  Theorem
      
      |- !n l. n < LENGTH l ==> !x. ELL n (x::l) = ELL n l
   
   [ELL_EL]  Theorem
      
      |- !n l. n < LENGTH l ==> (ELL n l = EL (PRE (LENGTH l - n)) l)
   
   [ELL_IS_EL]  Theorem
      
      |- !n l. n < LENGTH l ==> MEM (ELL n l) l
   
   [ELL_LAST]  Theorem
      
      |- !l. ~NULL l ==> (ELL 0 l = LAST l)
   
   [ELL_LENGTH_APPEND]  Theorem
      
      |- !l1 l2. ~NULL l1 ==> (ELL (LENGTH l2) (l1 ++ l2) = LAST l1)
   
   [ELL_LENGTH_CONS]  Theorem
      
      |- !l x. ELL (LENGTH l) (x::l) = x
   
   [ELL_LENGTH_SNOC]  Theorem
      
      |- !l x. ELL (LENGTH l) (SNOC x l) = if NULL l then x else HD l
   
   [ELL_MAP]  Theorem
      
      |- !n l f. n < LENGTH l ==> (ELL n (MAP f l) = f (ELL n l))
   
   [ELL_PRE_LENGTH]  Theorem
      
      |- !l. l <> [] ==> (ELL (PRE (LENGTH l)) l = HD l)
   
   [ELL_REVERSE]  Theorem
      
      |- !n l.
           n < LENGTH l ==>
           (ELL n (REVERSE l) = ELL (PRE (LENGTH l - n)) l)
   
   [ELL_REVERSE_EL]  Theorem
      
      |- !n l. n < LENGTH l ==> (ELL n (REVERSE l) = EL n l)
   
   [ELL_SEG]  Theorem
      
      |- !n l.
           n < LENGTH l ==> (ELL n l = HD (SEG 1 (PRE (LENGTH l - n)) l))
   
   [ELL_SNOC]  Theorem
      
      |- !n. 0 < n ==> !x l. ELL n (SNOC x l) = ELL (PRE n) l
   
   [ELL_SUC_SNOC]  Theorem
      
      |- !n x l. ELL (SUC n) (SNOC x l) = ELL n l
   
   [ELL_compute]  Theorem
      
      |- (!l. ELL 0 l = LAST l) /\
         (!n l.
            ELL (NUMERAL (BIT1 n)) l =
            ELL (NUMERAL (BIT1 n) - 1) (FRONT l)) /\
         !n l. ELL (NUMERAL (BIT2 n)) l = ELL (NUMERAL (BIT1 n)) (FRONT l)
   
   [EL_APPEND1]  Theorem
      
      |- !n l1 l2. n < LENGTH l1 ==> (EL n (l1 ++ l2) = EL n l1)
   
   [EL_APPEND2]  Theorem
      
      |- !l1 n.
           LENGTH l1 <= n ==> !l2. EL n (l1 ++ l2) = EL (n - LENGTH l1) l2
   
   [EL_BUTFIRSTN]  Theorem
      
      |- !m n l. m + n < LENGTH l ==> (EL m (DROP n l) = EL (m + n) l)
   
   [EL_CONS]  Theorem
      
      |- !n. 0 < n ==> !x l. EL n (x::l) = EL (PRE n) l
   
   [EL_ELL]  Theorem
      
      |- !n l. n < LENGTH l ==> (EL n l = ELL (PRE (LENGTH l - n)) l)
   
   [EL_FIRSTN]  Theorem
      
      |- !n x l. x < n /\ n <= LENGTH l ==> (EL x (TAKE n l) = EL x l)
   
   [EL_FRONT]  Theorem
      
      |- !l n.
           n < LENGTH (FRONT l) /\ ~NULL l ==> (EL n (FRONT l) = EL n l)
   
   [EL_GENLIST]  Theorem
      
      |- !f n x. x < n ==> (EL x (GENLIST f n) = f x)
   
   [EL_IS_EL]  Theorem
      
      |- !n l. n < LENGTH l ==> MEM (EL n l) l
   
   [EL_LENGTH_APPEND]  Theorem
      
      |- !l2 l1. ~NULL l2 ==> (EL (LENGTH l1) (l1 ++ l2) = HD l2)
   
   [EL_LENGTH_SNOC]  Theorem
      
      |- !l x. EL (LENGTH l) (SNOC x l) = x
   
   [EL_MAP]  Theorem
      
      |- !n l. n < LENGTH l ==> !f. EL n (MAP f l) = f (EL n l)
   
   [EL_PRE_LENGTH]  Theorem
      
      |- !l. l <> [] ==> (EL (PRE (LENGTH l)) l = LAST l)
   
   [EL_REVERSE]  Theorem
      
      |- !n l.
           n < LENGTH l ==> (EL n (REVERSE l) = EL (PRE (LENGTH l - n)) l)
   
   [EL_REVERSE_ELL]  Theorem
      
      |- !n l. n < LENGTH l ==> (EL n (REVERSE l) = ELL n l)
   
   [EL_SEG]  Theorem
      
      |- !n l. n < LENGTH l ==> (EL n l = HD (SEG 1 n l))
   
   [EL_SNOC]  Theorem
      
      |- !n l. n < LENGTH l ==> !x. EL n (SNOC x l) = EL n l
   
   [EQ_LIST]  Theorem
      
      |- !x1 x2. (x1 = x2) ==> !l1 l2. (l1 = l2) ==> (x1::l1 = x2::l2)
   
   [EVERY_GENLIST]  Theorem
      
      |- !n. (!i. i < n ==> P (f i)) ==> EVERY P (GENLIST f n)
   
   [FCOMM_FOLDL_APPEND]  Theorem
      
      |- !f g.
           FCOMM f g ==>
           !e.
             RIGHT_ID g e ==>
             !l1 l2. FOLDL f e (l1 ++ l2) = g (FOLDL f e l1) (FOLDL f e l2)
   
   [FCOMM_FOLDL_FLAT]  Theorem
      
      |- !f g.
           FCOMM f g ==>
           !e.
             RIGHT_ID g e ==>
             !l. FOLDL f e (FLAT l) = FOLDL g e (MAP (FOLDL f e) l)
   
   [FCOMM_FOLDR_APPEND]  Theorem
      
      |- !g f.
           FCOMM g f ==>
           !e.
             LEFT_ID g e ==>
             !l1 l2. FOLDR f e (l1 ++ l2) = g (FOLDR f e l1) (FOLDR f e l2)
   
   [FCOMM_FOLDR_FLAT]  Theorem
      
      |- !g f.
           FCOMM g f ==>
           !e.
             LEFT_ID g e ==>
             !l. FOLDR f e (FLAT l) = FOLDR g e (MAP (FOLDR f e) l)
   
   [FILTER]  Theorem
      
      |- (!P. FILTER P [] = []) /\
         !P h t.
           FILTER P (h::t) = if P h then h::FILTER P t else FILTER P t
   
   [FILTER_APPEND]  Theorem
      
      |- !f l1 l2. FILTER f (l1 ++ l2) = FILTER f l1 ++ FILTER f l2
   
   [FILTER_COMM]  Theorem
      
      |- !f1 f2 l. FILTER f1 (FILTER f2 l) = FILTER f2 (FILTER f1 l)
   
   [FILTER_FILTER]  Theorem
      
      |- !P Q l. FILTER P (FILTER Q l) = FILTER (\x. P x /\ Q x) l
   
   [FILTER_FLAT]  Theorem
      
      |- !P l. FILTER P (FLAT l) = FLAT (MAP (FILTER P) l)
   
   [FILTER_FOLDL]  Theorem
      
      |- !P l.
           FILTER P l = FOLDL (\l' x. if P x then SNOC x l' else l') [] l
   
   [FILTER_FOLDR]  Theorem
      
      |- !P l. FILTER P l = FOLDR (\x l'. if P x then x::l' else l') [] l
   
   [FILTER_IDEM]  Theorem
      
      |- !f l. FILTER f (FILTER f l) = FILTER f l
   
   [FILTER_MAP]  Theorem
      
      |- !f1 f2 l. FILTER f1 (MAP f2 l) = MAP f2 (FILTER (f1 o f2) l)
   
   [FILTER_REVERSE]  Theorem
      
      |- !P l. FILTER P (REVERSE l) = REVERSE (FILTER P l)
   
   [FILTER_SNOC]  Theorem
      
      |- !P x l.
           FILTER P (SNOC x l) =
           if P x then SNOC x (FILTER P l) else FILTER P l
   
   [FIRSTN]  Theorem
      
      |- (!l. TAKE 0 l = []) /\ !n x l. TAKE (SUC n) (x::l) = x::TAKE n l
   
   [FIRSTN_APPEND1]  Theorem
      
      |- !n l1. n <= LENGTH l1 ==> !l2. TAKE n (l1 ++ l2) = TAKE n l1
   
   [FIRSTN_APPEND2]  Theorem
      
      |- !l1 n.
           LENGTH l1 <= n ==>
           !l2. TAKE n (l1 ++ l2) = l1 ++ TAKE (n - LENGTH l1) l2
   
   [FIRSTN_BUTLASTN]  Theorem
      
      |- !n l. n <= LENGTH l ==> (TAKE n l = BUTLASTN (LENGTH l - n) l)
   
   [FIRSTN_FIRSTN]  Theorem
      
      |- !m l.
           m <= LENGTH l ==> !n. n <= m ==> (TAKE n (TAKE m l) = TAKE n l)
   
   [FIRSTN_LENGTH_APPEND]  Theorem
      
      |- !l1 l2. TAKE (LENGTH l1) (l1 ++ l2) = l1
   
   [FIRSTN_LENGTH_ID]  Theorem
      
      |- !l. TAKE (LENGTH l) l = l
   
   [FIRSTN_REVERSE]  Theorem
      
      |- !n l. n <= LENGTH l ==> (TAKE n (REVERSE l) = REVERSE (LASTN n l))
   
   [FIRSTN_SEG]  Theorem
      
      |- !n l. n <= LENGTH l ==> (TAKE n l = SEG n 0 l)
   
   [FIRSTN_SNOC]  Theorem
      
      |- !n l. n <= LENGTH l ==> !x. TAKE n (SNOC x l) = TAKE n l
   
   [FIRSTN_compute]  Theorem
      
      |- (!l. TAKE 0 l = []) /\
         (!n x l.
            TAKE (NUMERAL (BIT1 n)) (x::l) =
            x::TAKE (NUMERAL (BIT1 n) - 1) l) /\
         !n x l.
           TAKE (NUMERAL (BIT2 n)) (x::l) = x::TAKE (NUMERAL (BIT1 n)) l
   
   [FLAT]  Theorem
      
      |- (FLAT [] = []) /\ !x l. FLAT (x::l) = x ++ FLAT l
   
   [FLAT_APPEND]  Theorem
      
      |- !l1 l2. FLAT (l1 ++ l2) = FLAT l1 ++ FLAT l2
   
   [FLAT_FLAT]  Theorem
      
      |- !l. FLAT (FLAT l) = FLAT (MAP FLAT l)
   
   [FLAT_FOLDL]  Theorem
      
      |- !l. FLAT l = FOLDL $++ [] l
   
   [FLAT_FOLDR]  Theorem
      
      |- !l. FLAT l = FOLDR $++ [] l
   
   [FLAT_REVERSE]  Theorem
      
      |- !l. FLAT (REVERSE l) = REVERSE (FLAT (MAP REVERSE l))
   
   [FLAT_SNOC]  Theorem
      
      |- !x l. FLAT (SNOC x l) = FLAT l ++ x
   
   [FOLDL]  Theorem
      
      |- (!f e. FOLDL f e [] = e) /\
         !f e x l. FOLDL f e (x::l) = FOLDL f (f e x) l
   
   [FOLDL_APPEND]  Theorem
      
      |- !f e l1 l2. FOLDL f e (l1 ++ l2) = FOLDL f (FOLDL f e l1) l2
   
   [FOLDL_FILTER]  Theorem
      
      |- !f e P l.
           FOLDL f e (FILTER P l) =
           FOLDL (\x y. if P y then f x y else x) e l
   
   [FOLDL_FOLDR_REVERSE]  Theorem
      
      |- !f e l. FOLDL f e l = FOLDR (\x y. f y x) e (REVERSE l)
   
   [FOLDL_MAP]  Theorem
      
      |- !f e g l. FOLDL f e (MAP g l) = FOLDL (\x y. f x (g y)) e l
   
   [FOLDL_MAP2]  Theorem
      
      |- !f e g l. FOLDL f e (MAP g l) = FOLDL (\x y. f x (g y)) e l
   
   [FOLDL_REVERSE]  Theorem
      
      |- !f e l. FOLDL f e (REVERSE l) = FOLDR (\x y. f y x) e l
   
   [FOLDL_SINGLE]  Theorem
      
      |- !f e x. FOLDL f e [x] = f e x
   
   [FOLDL_SNOC]  Theorem
      
      |- !f e x l. FOLDL f e (SNOC x l) = f (FOLDL f e l) x
   
   [FOLDL_SNOC_NIL]  Theorem
      
      |- !l. FOLDL (\xs x. SNOC x xs) [] l = l
   
   [FOLDR]  Theorem
      
      |- (!f e. FOLDR f e [] = e) /\
         !f e x l. FOLDR f e (x::l) = f x (FOLDR f e l)
   
   [FOLDR_APPEND]  Theorem
      
      |- !f e l1 l2. FOLDR f e (l1 ++ l2) = FOLDR f (FOLDR f e l2) l1
   
   [FOLDR_CONS_NIL]  Theorem
      
      |- !l. FOLDR CONS [] l = l
   
   [FOLDR_FILTER]  Theorem
      
      |- !f e P l.
           FOLDR f e (FILTER P l) =
           FOLDR (\x y. if P x then f x y else y) e l
   
   [FOLDR_FILTER_REVERSE]  Theorem
      
      |- !f.
           (!a b c. f a (f b c) = f b (f a c)) ==>
           !e P l.
             FOLDR f e (FILTER P (REVERSE l)) = FOLDR f e (FILTER P l)
   
   [FOLDR_FOLDL]  Theorem
      
      |- !f e. MONOID f e ==> !l. FOLDR f e l = FOLDL f e l
   
   [FOLDR_FOLDL_REVERSE]  Theorem
      
      |- !f e l. FOLDR f e l = FOLDL (\x y. f y x) e (REVERSE l)
   
   [FOLDR_MAP]  Theorem
      
      |- !f e g l. FOLDR f e (MAP g l) = FOLDR (\x y. f (g x) y) e l
   
   [FOLDR_MAP_REVERSE]  Theorem
      
      |- !f.
           (!a b c. f a (f b c) = f b (f a c)) ==>
           !e g l. FOLDR f e (MAP g (REVERSE l)) = FOLDR f e (MAP g l)
   
   [FOLDR_REVERSE]  Theorem
      
      |- !f e l. FOLDR f e (REVERSE l) = FOLDL (\x y. f y x) e l
   
   [FOLDR_SINGLE]  Theorem
      
      |- !f e x. FOLDR f e [x] = f x e
   
   [FOLDR_SNOC]  Theorem
      
      |- !f e x l. FOLDR f e (SNOC x l) = FOLDR f (f x e) l
   
   [FRONT_APPEND]  Theorem
      
      |- FRONT (l1 ++ e::l2) = l1 ++ FRONT (e::l2)
   
   [FRONT___LENGTH]  Theorem
      
      |- !l. l <> [] ==> (LENGTH (FRONT l) = PRE (LENGTH l))
   
   [GENLIST_APPEND]  Theorem
      
      |- !f a b.
           GENLIST f (a + b) = GENLIST f b ++ GENLIST (\t. f (t + b)) a
   
   [GENLIST_FUN_EQ]  Theorem
      
      |- !n f g.
           (!x. x < n ==> (f x = g x)) ==> (GENLIST f n = GENLIST g n)
   
   [GENLIST_compute]  Theorem
      
      |- (!f. GENLIST f 0 = []) /\
         (!f n.
            GENLIST f (NUMERAL (BIT1 n)) =
            SNOC (f (NUMERAL (BIT1 n) - 1))
              (GENLIST f (NUMERAL (BIT1 n) - 1))) /\
         !f n.
           GENLIST f (NUMERAL (BIT2 n)) =
           SNOC (f (NUMERAL (BIT1 n))) (GENLIST f (NUMERAL (BIT1 n)))
   
   [HD]  Theorem
      
      |- !x l. HD (x::l) = x
   
   [HD_GENLIST]  Theorem
      
      |- HD (GENLIST f (SUC n)) = f 0
   
   [IS_EL]  Theorem
      
      |- (!x. MEM x [] <=> F) /\
         !y x l. MEM y (x::l) <=> (y = x) \/ MEM y l
   
   [IS_EL_APPEND]  Theorem
      
      |- !l1 l2 x. MEM x (l1 ++ l2) <=> MEM x l1 \/ MEM x l2
   
   [IS_EL_BUTFIRSTN]  Theorem
      
      |- !m l. m <= LENGTH l ==> !x. MEM x (DROP m l) ==> MEM x l
   
   [IS_EL_BUTLASTN]  Theorem
      
      |- !m l. m <= LENGTH l ==> !x. MEM x (BUTLASTN m l) ==> MEM x l
   
   [IS_EL_DEF]  Theorem
      
      |- !x l. MEM x l <=> EXISTS ($= x) l
   
   [IS_EL_FILTER]  Theorem
      
      |- !P x. P x ==> !l. MEM x (FILTER P l) <=> MEM x l
   
   [IS_EL_FIRSTN]  Theorem
      
      |- !m l. m <= LENGTH l ==> !x. MEM x (TAKE m l) ==> MEM x l
   
   [IS_EL_FOLDL]  Theorem
      
      |- !y l. MEM y l <=> FOLDL (\l' x. l' \/ (y = x)) F l
   
   [IS_EL_FOLDL_MAP]  Theorem
      
      |- !x l. MEM x l <=> FOLDL $\/ F (MAP ($= x) l)
   
   [IS_EL_FOLDR]  Theorem
      
      |- !y l. MEM y l <=> FOLDR (\x l'. (y = x) \/ l') F l
   
   [IS_EL_FOLDR_MAP]  Theorem
      
      |- !x l. MEM x l <=> FOLDR $\/ F (MAP ($= x) l)
   
   [IS_EL_LASTN]  Theorem
      
      |- !m l. m <= LENGTH l ==> !x. MEM x (LASTN m l) ==> MEM x l
   
   [IS_EL_REPLICATE]  Theorem
      
      |- !n. 0 < n ==> !x. MEM x (REPLICATE n x)
   
   [IS_EL_REVERSE]  Theorem
      
      |- !x l. MEM x (REVERSE l) <=> MEM x l
   
   [IS_EL_SEG]  Theorem
      
      |- !n m l. n + m <= LENGTH l ==> !x. MEM x (SEG n m l) ==> MEM x l
   
   [IS_EL_SNOC]  Theorem
      
      |- !y x l. MEM y (SNOC x l) <=> (y = x) \/ MEM y l
   
   [IS_EL_SOME_EL]  Theorem
      
      |- !x l. MEM x l <=> EXISTS ($= x) l
   
   [IS_PREFIX]  Theorem
      
      |- (!l. [] <<= l <=> T) /\ (!x l. x::l <<= [] <=> F) /\
         !x1 l1 x2 l2. x2::l2 <<= x1::l1 <=> (x1 = x2) /\ l2 <<= l1
   
   [IS_PREFIX_ANTISYM]  Theorem
      
      |- !x y. x <<= y /\ y <<= x ==> (x = y)
   
   [IS_PREFIX_APPEND]  Theorem
      
      |- !l1 l2. l2 <<= l1 <=> ?l. l1 = l2 ++ l
   
   [IS_PREFIX_APPEND1]  Theorem
      
      |- !a b c. a ++ b <<= c ==> a <<= c
   
   [IS_PREFIX_APPEND2]  Theorem
      
      |- !a b c. a <<= b ++ c ==> a <<= b \/ b <<= a
   
   [IS_PREFIX_APPENDS]  Theorem
      
      |- !a b c. a ++ b <<= a ++ c <=> b <<= c
   
   [IS_PREFIX_BUTLAST]  Theorem
      
      |- !x y. FRONT (x::y) <<= x::y
   
   [IS_PREFIX_IS_SUBLIST]  Theorem
      
      |- !l1 l2. l2 <<= l1 ==> IS_SUBLIST l1 l2
   
   [IS_PREFIX_LENGTH]  Theorem
      
      |- !x y. x <<= y ==> LENGTH x <= LENGTH y
   
   [IS_PREFIX_LENGTH_ANTI]  Theorem
      
      |- !x y. x <<= y /\ (LENGTH x = LENGTH y) <=> (x = y)
   
   [IS_PREFIX_NIL]  Theorem
      
      |- !x. [] <<= x /\ (x <<= [] <=> (x = []))
   
   [IS_PREFIX_PREFIX]  Theorem
      
      |- !P l. PREFIX P l <<= l
   
   [IS_PREFIX_REFL]  Theorem
      
      |- !x. x <<= x
   
   [IS_PREFIX_REVERSE]  Theorem
      
      |- !l1 l2. REVERSE l2 <<= REVERSE l1 <=> IS_SUFFIX l1 l2
   
   [IS_PREFIX_SNOC]  Theorem
      
      |- !x y z. z <<= SNOC x y <=> z <<= y \/ (z = SNOC x y)
   
   [IS_PREFIX_TRANS]  Theorem
      
      |- !x y z. y <<= x /\ z <<= y ==> z <<= x
   
   [IS_SUBLIST_APPEND]  Theorem
      
      |- !l1 l2. IS_SUBLIST l1 l2 <=> ?l l'. l1 = l ++ (l2 ++ l')
   
   [IS_SUBLIST_REVERSE]  Theorem
      
      |- !l1 l2. IS_SUBLIST (REVERSE l1) (REVERSE l2) <=> IS_SUBLIST l1 l2
   
   [IS_SUFFIX_APPEND]  Theorem
      
      |- !l1 l2. IS_SUFFIX l1 l2 <=> ?l. l1 = l ++ l2
   
   [IS_SUFFIX_IS_SUBLIST]  Theorem
      
      |- !l1 l2. IS_SUFFIX l1 l2 ==> IS_SUBLIST l1 l2
   
   [IS_SUFFIX_REVERSE]  Theorem
      
      |- !l2 l1. IS_SUFFIX (REVERSE l1) (REVERSE l2) <=> l2 <<= l1
   
   [IS_SUFFIX_compute]  Theorem
      
      |- !l1 l2. IS_SUFFIX l1 l2 <=> REVERSE l2 <<= REVERSE l1
   
   [LAST]  Theorem
      
      |- !x l. LAST (SNOC x l) = x
   
   [LASTN_1]  Theorem
      
      |- !l. l <> [] ==> (LASTN 1 l = [LAST l])
   
   [LASTN_APPEND1]  Theorem
      
      |- !l2 n.
           LENGTH l2 <= n ==>
           !l1. LASTN n (l1 ++ l2) = LASTN (n - LENGTH l2) l1 ++ l2
   
   [LASTN_APPEND2]  Theorem
      
      |- !n l2. n <= LENGTH l2 ==> !l1. LASTN n (l1 ++ l2) = LASTN n l2
   
   [LASTN_BUTFIRSTN]  Theorem
      
      |- !n l. n <= LENGTH l ==> (LASTN n l = DROP (LENGTH l - n) l)
   
   [LASTN_BUTLASTN]  Theorem
      
      |- !n m l.
           n + m <= LENGTH l ==>
           (LASTN n (BUTLASTN m l) = BUTLASTN m (LASTN (n + m) l))
   
   [LASTN_CONS]  Theorem
      
      |- !n l. n <= LENGTH l ==> !x. LASTN n (x::l) = LASTN n l
   
   [LASTN_LASTN]  Theorem
      
      |- !l n m.
           m <= LENGTH l ==> n <= m ==> (LASTN n (LASTN m l) = LASTN n l)
   
   [LASTN_LENGTH_APPEND]  Theorem
      
      |- !l2 l1. LASTN (LENGTH l2) (l1 ++ l2) = l2
   
   [LASTN_LENGTH_ID]  Theorem
      
      |- !l. LASTN (LENGTH l) l = l
   
   [LASTN_MAP]  Theorem
      
      |- !n l. n <= LENGTH l ==> !f. LASTN n (MAP f l) = MAP f (LASTN n l)
   
   [LASTN_REVERSE]  Theorem
      
      |- !n l. n <= LENGTH l ==> (LASTN n (REVERSE l) = REVERSE (TAKE n l))
   
   [LASTN_SEG]  Theorem
      
      |- !n l. n <= LENGTH l ==> (LASTN n l = SEG n (LENGTH l - n) l)
   
   [LASTN_compute]  Theorem
      
      |- !n l.
           LASTN n l =
           (let m = LENGTH l in
              if n <= m then
                DROP (m - n) l
              else
                FAIL LASTN longer than list n l)
   
   [LAST_APPEND]  Theorem
      
      |- !e l1 l2. LAST (l1 ++ e::l2) = LAST (e::l2)
   
   [LAST_CONS]  Theorem
      
      |- (!x. LAST [x] = x) /\ !x y z. LAST (x::y::z) = LAST (y::z)
   
   [LAST_LASTN_LAST]  Theorem
      
      |- !n l. n <= LENGTH l ==> 0 < n ==> (LAST (LASTN n l) = LAST l)
   
   [LENGTH]  Theorem
      
      |- (LENGTH [] = 0) /\ !x l. LENGTH (x::l) = SUC (LENGTH l)
   
   [LENGTH_APPEND]  Theorem
      
      |- !l1 l2. LENGTH (l1 ++ l2) = LENGTH l1 + LENGTH l2
   
   [LENGTH_BUTFIRSTN]  Theorem
      
      |- !n l. n <= LENGTH l ==> (LENGTH (DROP n l) = LENGTH l - n)
   
   [LENGTH_BUTLAST]  Theorem
      
      |- !l. l <> [] ==> (LENGTH (FRONT l) = PRE (LENGTH l))
   
   [LENGTH_BUTLASTN]  Theorem
      
      |- !n l. n <= LENGTH l ==> (LENGTH (BUTLASTN n l) = LENGTH l - n)
   
   [LENGTH_CONS]  Theorem
      
      |- !l n. (LENGTH l = SUC n) <=> ?x l'. (LENGTH l' = n) /\ (l = x::l')
   
   [LENGTH_EQ]  Theorem
      
      |- !x y. (x = y) ==> (LENGTH x = LENGTH y)
   
   [LENGTH_EQ_NIL]  Theorem
      
      |- !P. (!l. (LENGTH l = 0) ==> P l) <=> P []
   
   [LENGTH_FIRSTN]  Theorem
      
      |- !n l. n <= LENGTH l ==> (LENGTH (TAKE n l) = n)
   
   [LENGTH_FLAT]  Theorem
      
      |- !l. LENGTH (FLAT l) = SUM (MAP LENGTH l)
   
   [LENGTH_FOLDL]  Theorem
      
      |- !l. LENGTH l = FOLDL (\l' x. SUC l') 0 l
   
   [LENGTH_FOLDR]  Theorem
      
      |- !l. LENGTH l = FOLDR (\x l'. SUC l') 0 l
   
   [LENGTH_GENLIST]  Theorem
      
      |- !f n. LENGTH (GENLIST f n) = n
   
   [LENGTH_LASTN]  Theorem
      
      |- !n l. n <= LENGTH l ==> (LENGTH (LASTN n l) = n)
   
   [LENGTH_MAP]  Theorem
      
      |- !l f. LENGTH (MAP f l) = LENGTH l
   
   [LENGTH_MAP2]  Theorem
      
      |- !l1 l2.
           (LENGTH l1 = LENGTH l2) ==>
           !f.
             (LENGTH (MAP2 f l1 l2) = LENGTH l1) /\
             (LENGTH (MAP2 f l1 l2) = LENGTH l2)
   
   [LENGTH_NIL]  Theorem
      
      |- !l. (LENGTH l = 0) <=> (l = [])
   
   [LENGTH_NOT_NULL]  Theorem
      
      |- !l. 0 < LENGTH l <=> ~NULL l
   
   [LENGTH_REPLICATE]  Theorem
      
      |- !n x. LENGTH (REPLICATE n x) = n
   
   [LENGTH_REVERSE]  Theorem
      
      |- !l. LENGTH (REVERSE l) = LENGTH l
   
   [LENGTH_SCANL]  Theorem
      
      |- !f e l. LENGTH (SCANL f e l) = SUC (LENGTH l)
   
   [LENGTH_SCANR]  Theorem
      
      |- !f e l. LENGTH (SCANR f e l) = SUC (LENGTH l)
   
   [LENGTH_SEG]  Theorem
      
      |- !n k l. n + k <= LENGTH l ==> (LENGTH (SEG n k l) = n)
   
   [LENGTH_SNOC]  Theorem
      
      |- !x l. LENGTH (SNOC x l) = SUC (LENGTH l)
   
   [LENGTH_UNZIP_FST]  Theorem
      
      |- !l. LENGTH (UNZIP_FST l) = LENGTH l
   
   [LENGTH_UNZIP_SND]  Theorem
      
      |- !l. LENGTH (UNZIP_SND l) = LENGTH l
   
   [LENGTH_ZIP]  Theorem
      
      |- !l1 l2.
           (LENGTH l1 = LENGTH l2) ==>
           (LENGTH (ZIP (l1,l2)) = LENGTH l1) /\
           (LENGTH (ZIP (l1,l2)) = LENGTH l2)
   
   [LIST_ELEM_COUNT_MEM]  Theorem
      
      |- !e l. LIST_ELEM_COUNT e l > 0 <=> MEM e l
   
   [LIST_ELEM_COUNT_THM]  Theorem
      
      |- (!e. LIST_ELEM_COUNT e [] = 0) /\
         (!e l1 l2.
            LIST_ELEM_COUNT e (l1 ++ l2) =
            LIST_ELEM_COUNT e l1 + LIST_ELEM_COUNT e l2) /\
         (!e h l.
            (h = e) ==>
            (LIST_ELEM_COUNT e (h::l) = SUC (LIST_ELEM_COUNT e l))) /\
         !e h l.
           h <> e ==> (LIST_ELEM_COUNT e (h::l) = LIST_ELEM_COUNT e l)
   
   [LIST_NOT_EQ]  Theorem
      
      |- !l1 l2. l1 <> l2 ==> !x1 x2. x1::l1 <> x2::l2
   
   [MAP]  Theorem
      
      |- (!f. MAP f [] = []) /\ !f x l. MAP f (x::l) = f x::MAP f l
   
   [MAP2]  Theorem
      
      |- (!f. MAP2 f [] [] = []) /\
         !f x1 l1 x2 l2. MAP2 f (x1::l1) (x2::l2) = f x1 x2::MAP2 f l1 l2
   
   [MAP2_ZIP]  Theorem
      
      |- !l1 l2.
           (LENGTH l1 = LENGTH l2) ==>
           !f. MAP2 f l1 l2 = MAP (UNCURRY f) (ZIP (l1,l2))
   
   [MAP_APPEND]  Theorem
      
      |- !f l1 l2. MAP f (l1 ++ l2) = MAP f l1 ++ MAP f l2
   
   [MAP_EQ_f]  Theorem
      
      |- !f1 f2 l. (MAP f1 l = MAP f2 l) <=> !e. MEM e l ==> (f1 e = f2 e)
   
   [MAP_FILTER]  Theorem
      
      |- !f P l.
           (!x. P (f x) <=> P x) ==>
           (MAP f (FILTER P l) = FILTER P (MAP f l))
   
   [MAP_FLAT]  Theorem
      
      |- !f l. MAP f (FLAT l) = FLAT (MAP (MAP f) l)
   
   [MAP_FOLDL]  Theorem
      
      |- !f l. MAP f l = FOLDL (\l' x. SNOC (f x) l') [] l
   
   [MAP_FOLDR]  Theorem
      
      |- !f l. MAP f l = FOLDR (\x l'. f x::l') [] l
   
   [MAP_GENLIST]  Theorem
      
      |- !f g n. MAP f (GENLIST g n) = GENLIST (f o g) n
   
   [MAP_MAP_o]  Theorem
      
      |- !f g l. MAP f (MAP g l) = MAP (f o g) l
   
   [MAP_REVERSE]  Theorem
      
      |- !f l. MAP f (REVERSE l) = REVERSE (MAP f l)
   
   [MAP_SNOC]  Theorem
      
      |- !f x l. MAP f (SNOC x l) = SNOC (f x) (MAP f l)
   
   [MAP_o]  Theorem
      
      |- !f g. MAP (f o g) = MAP f o MAP g
   
   [MEM_FRONT]  Theorem
      
      |- !l e y. MEM y (FRONT (e::l)) ==> MEM y (e::l)
   
   [MEM_LAST]  Theorem
      
      |- !e l. MEM (LAST (e::l)) (e::l)
   
   [MEM_LAST_FRONT]  Theorem
      
      |- !e l h. MEM e l /\ e <> LAST (h::l) ==> MEM e (FRONT (h::l))
   
   [MONOID_APPEND_NIL]  Theorem
      
      |- MONOID $++ []
   
   [NOT_ALL_EL_SOME_EL]  Theorem
      
      |- !P l. ~EVERY P l <=> EXISTS ($~ o P) l
   
   [NOT_CONS_NIL]  Theorem
      
      |- !x l. x::l <> []
   
   [NOT_EQ_LIST]  Theorem
      
      |- !x1 x2. x1 <> x2 ==> !l1 l2. x1::l1 <> x2::l2
   
   [NOT_NIL_CONS]  Theorem
      
      |- !x l. [] <> x::l
   
   [NOT_NIL_SNOC]  Theorem
      
      |- !x l. [] <> SNOC x l
   
   [NOT_NULL_SNOC]  Theorem
      
      |- !x l. ~NULL (SNOC x l)
   
   [NOT_SNOC_NIL]  Theorem
      
      |- !x l. SNOC x l <> []
   
   [NOT_SOME_EL_ALL_EL]  Theorem
      
      |- !P l. ~EXISTS P l <=> EVERY ($~ o P) l
   
   [NULL]  Theorem
      
      |- NULL [] /\ !x l. ~NULL (x::l)
   
   [NULL_DEF]  Theorem
      
      |- (NULL [] <=> T) /\ !x l. NULL (x::l) <=> F
   
   [NULL_EQ_NIL]  Theorem
      
      |- !l. NULL l <=> (l = [])
   
   [NULL_FOLDL]  Theorem
      
      |- !l. NULL l <=> FOLDL (\x l'. F) T l
   
   [NULL_FOLDR]  Theorem
      
      |- !l. NULL l <=> FOLDR (\x l'. F) T l
   
   [OR_EL_FOLDL]  Theorem
      
      |- !l. OR_EL l <=> FOLDL $\/ F l
   
   [OR_EL_FOLDR]  Theorem
      
      |- !l. OR_EL l <=> FOLDR $\/ F l
   
   [PREFIX]  Theorem
      
      |- (!P. PREFIX P [] = []) /\
         !P x l. PREFIX P (x::l) = if P x then x::PREFIX P l else []
   
   [PREFIX_FOLDR]  Theorem
      
      |- !P l. PREFIX P l = FOLDR (\x l'. if P x then x::l' else []) [] l
   
   [REPLACE_ELEMENT_SEM]  Theorem
      
      |- (!e n l. LENGTH (REPLACE_ELEMENT e n l) = LENGTH l) /\
         !e n l p.
           p < LENGTH l ==>
           (EL p (REPLACE_ELEMENT e n l) = if p = n then e else EL p l)
   
   [REPLICATE_compute]  Theorem
      
      |- (!x. REPLICATE 0 x = []) /\
         (!n x.
            REPLICATE (NUMERAL (BIT1 n)) x =
            x::REPLICATE (NUMERAL (BIT1 n) - 1) x) /\
         !n x.
           REPLICATE (NUMERAL (BIT2 n)) x =
           x::REPLICATE (NUMERAL (BIT1 n)) x
   
   [REVERSE]  Theorem
      
      |- (REVERSE [] = []) /\ !x l. REVERSE (x::l) = SNOC x (REVERSE l)
   
   [REVERSE_APPEND]  Theorem
      
      |- !l1 l2. REVERSE (l1 ++ l2) = REVERSE l2 ++ REVERSE l1
   
   [REVERSE_EQ_NIL]  Theorem
      
      |- !l. (REVERSE l = []) <=> (l = [])
   
   [REVERSE_FLAT]  Theorem
      
      |- !l. REVERSE (FLAT l) = FLAT (REVERSE (MAP REVERSE l))
   
   [REVERSE_FOLDL]  Theorem
      
      |- !l. REVERSE l = FOLDL (\l' x. x::l') [] l
   
   [REVERSE_FOLDR]  Theorem
      
      |- !l. REVERSE l = FOLDR SNOC [] l
   
   [REVERSE_REVERSE]  Theorem
      
      |- !l. REVERSE (REVERSE l) = l
   
   [REVERSE_SNOC]  Theorem
      
      |- !x l. REVERSE (SNOC x l) = x::REVERSE l
   
   [SEG_0_SNOC]  Theorem
      
      |- !m l x. m <= LENGTH l ==> (SEG m 0 (SNOC x l) = SEG m 0 l)
   
   [SEG_APPEND]  Theorem
      
      |- !m l1 n l2.
           m < LENGTH l1 /\ LENGTH l1 <= n + m /\
           n + m <= LENGTH l1 + LENGTH l2 ==>
           (SEG n m (l1 ++ l2) =
            SEG (LENGTH l1 - m) m l1 ++ SEG (n + m - LENGTH l1) 0 l2)
   
   [SEG_APPEND1]  Theorem
      
      |- !n m l1.
           n + m <= LENGTH l1 ==> !l2. SEG n m (l1 ++ l2) = SEG n m l1
   
   [SEG_APPEND2]  Theorem
      
      |- !l1 m n l2.
           LENGTH l1 <= m /\ n <= LENGTH l2 ==>
           (SEG n m (l1 ++ l2) = SEG n (m - LENGTH l1) l2)
   
   [SEG_FIRSTN_BUTFISTN]  Theorem
      
      |- !n m l. n + m <= LENGTH l ==> (SEG n m l = TAKE n (DROP m l))
   
   [SEG_LASTN_BUTLASTN]  Theorem
      
      |- !n m l.
           n + m <= LENGTH l ==>
           (SEG n m l = LASTN n (BUTLASTN (LENGTH l - (n + m)) l))
   
   [SEG_LENGTH_ID]  Theorem
      
      |- !l. SEG (LENGTH l) 0 l = l
   
   [SEG_LENGTH_SNOC]  Theorem
      
      |- !l x. SEG 1 (LENGTH l) (SNOC x l) = [x]
   
   [SEG_REVERSE]  Theorem
      
      |- !n m l.
           n + m <= LENGTH l ==>
           (SEG n m (REVERSE l) = REVERSE (SEG n (LENGTH l - (n + m)) l))
   
   [SEG_SEG]  Theorem
      
      |- !n1 m1 n2 m2 l.
           n1 + m1 <= LENGTH l /\ n2 + m2 <= n1 ==>
           (SEG n2 m2 (SEG n1 m1 l) = SEG n2 (m1 + m2) l)
   
   [SEG_SNOC]  Theorem
      
      |- !n m l. n + m <= LENGTH l ==> !x. SEG n m (SNOC x l) = SEG n m l
   
   [SEG_SUC_CONS]  Theorem
      
      |- !m n l x. SEG m (SUC n) (x::l) = SEG m n l
   
   [SEG_compute]  Theorem
      
      |- (!k l. SEG 0 k l = []) /\
         (!m x l.
            SEG (NUMERAL (BIT1 m)) 0 (x::l) =
            x::SEG (NUMERAL (BIT1 m) - 1) 0 l) /\
         (!m x l.
            SEG (NUMERAL (BIT2 m)) 0 (x::l) =
            x::SEG (NUMERAL (BIT1 m)) 0 l) /\
         (!m k x l.
            SEG (NUMERAL (BIT1 m)) (NUMERAL (BIT1 k)) (x::l) =
            SEG (NUMERAL (BIT1 m)) (NUMERAL (BIT1 k) - 1) l) /\
         (!m k x l.
            SEG (NUMERAL (BIT2 m)) (NUMERAL (BIT1 k)) (x::l) =
            SEG (NUMERAL (BIT2 m)) (NUMERAL (BIT1 k) - 1) l) /\
         (!m k x l.
            SEG (NUMERAL (BIT1 m)) (NUMERAL (BIT2 k)) (x::l) =
            SEG (NUMERAL (BIT1 m)) (NUMERAL (BIT1 k)) l) /\
         !m k x l.
           SEG (NUMERAL (BIT2 m)) (NUMERAL (BIT2 k)) (x::l) =
           SEG (NUMERAL (BIT2 m)) (NUMERAL (BIT1 k)) l
   
   [SNOC_11]  Theorem
      
      |- !x l x' l'. (SNOC x l = SNOC x' l') <=> (x = x') /\ (l = l')
   
   [SNOC_APPEND]  Theorem
      
      |- !x l. SNOC x l = l ++ [x]
   
   [SNOC_Axiom]  Theorem
      
      |- !e f. ?fn. (fn [] = e) /\ !x l. fn (SNOC x l) = f x l (fn l)
   
   [SNOC_CASES]  Theorem
      
      |- !ll. (ll = []) \/ ?x l. ll = SNOC x l
   
   [SNOC_EL_FIRSTN]  Theorem
      
      |- !n l. n < LENGTH l ==> (SNOC (EL n l) (TAKE n l) = TAKE (SUC n) l)
   
   [SNOC_EQ_LENGTH_EQ]  Theorem
      
      |- !x1 l1 x2 l2.
           (SNOC x1 l1 = SNOC x2 l2) ==> (LENGTH l1 = LENGTH l2)
   
   [SNOC_FOLDR]  Theorem
      
      |- !x l. SNOC x l = FOLDR CONS [x] l
   
   [SNOC_INDUCT]  Theorem
      
      |- !P. P [] /\ (!l. P l ==> !x. P (SNOC x l)) ==> !l. P l
   
   [SNOC_REVERSE_CONS]  Theorem
      
      |- !x l. SNOC x l = REVERSE (x::REVERSE l)
   
   [SOME_EL]  Theorem
      
      |- (!P. EXISTS P [] <=> F) /\
         !P h t. EXISTS P (h::t) <=> P h \/ EXISTS P t
   
   [SOME_EL_APPEND]  Theorem
      
      |- !P l1 l2. EXISTS P (l1 ++ l2) <=> EXISTS P l1 \/ EXISTS P l2
   
   [SOME_EL_BUTFIRSTN]  Theorem
      
      |- !m l. m <= LENGTH l ==> !P. EXISTS P (DROP m l) ==> EXISTS P l
   
   [SOME_EL_BUTLASTN]  Theorem
      
      |- !m l. m <= LENGTH l ==> !P. EXISTS P (BUTLASTN m l) ==> EXISTS P l
   
   [SOME_EL_DISJ]  Theorem
      
      |- !P Q l. EXISTS (\x. P x \/ Q x) l <=> EXISTS P l \/ EXISTS Q l
   
   [SOME_EL_FIRSTN]  Theorem
      
      |- !m l. m <= LENGTH l ==> !P. EXISTS P (TAKE m l) ==> EXISTS P l
   
   [SOME_EL_FOLDL]  Theorem
      
      |- !P l. EXISTS P l <=> FOLDL (\l' x. l' \/ P x) F l
   
   [SOME_EL_FOLDL_MAP]  Theorem
      
      |- !P l. EXISTS P l <=> FOLDL $\/ F (MAP P l)
   
   [SOME_EL_FOLDR]  Theorem
      
      |- !P l. EXISTS P l <=> FOLDR (\x l'. P x \/ l') F l
   
   [SOME_EL_FOLDR_MAP]  Theorem
      
      |- !P l. EXISTS P l <=> FOLDR $\/ F (MAP P l)
   
   [SOME_EL_LASTN]  Theorem
      
      |- !m l. m <= LENGTH l ==> !P. EXISTS P (LASTN m l) ==> EXISTS P l
   
   [SOME_EL_MAP]  Theorem
      
      |- !P f l. EXISTS P (MAP f l) <=> EXISTS (P o f) l
   
   [SOME_EL_REVERSE]  Theorem
      
      |- !P l. EXISTS P (REVERSE l) <=> EXISTS P l
   
   [SOME_EL_SEG]  Theorem
      
      |- !m k l.
           m + k <= LENGTH l ==> !P. EXISTS P (SEG m k l) ==> EXISTS P l
   
   [SOME_EL_SNOC]  Theorem
      
      |- !P x l. EXISTS P (SNOC x l) <=> P x \/ EXISTS P l
   
   [SPLITP_EVERY]  Theorem
      
      |- !P l. EVERY (\x. ~P x) l ==> (SPLITP P l = (l,[]))
   
   [SUM]  Theorem
      
      |- (SUM [] = 0) /\ !x l. SUM (x::l) = x + SUM l
   
   [SUM_APPEND]  Theorem
      
      |- !l1 l2. SUM (l1 ++ l2) = SUM l1 + SUM l2
   
   [SUM_FLAT]  Theorem
      
      |- !l. SUM (FLAT l) = SUM (MAP SUM l)
   
   [SUM_FOLDL]  Theorem
      
      |- !l. SUM l = FOLDL $+ 0 l
   
   [SUM_FOLDR]  Theorem
      
      |- !l. SUM l = FOLDR $+ 0 l
   
   [SUM_REVERSE]  Theorem
      
      |- !l. SUM (REVERSE l) = SUM l
   
   [SUM_SNOC]  Theorem
      
      |- !x l. SUM (SNOC x l) = SUM l + x
   
   [TL]  Theorem
      
      |- !x l. TL (x::l) = l
   
   [TL_SNOC]  Theorem
      
      |- !x l. TL (SNOC x l) = if NULL l then [] else SNOC x (TL l)
   
   [UNZIP]  Theorem
      
      |- (UNZIP [] = ([],[])) /\
         !x l. UNZIP (x::l) = (FST x::FST (UNZIP l),SND x::SND (UNZIP l))
   
   [UNZIP_SNOC]  Theorem
      
      |- !x l.
           UNZIP (SNOC x l) =
           (SNOC (FST x) (FST (UNZIP l)),SNOC (SND x) (SND (UNZIP l)))
   
   [UNZIP_ZIP]  Theorem
      
      |- !l1 l2.
           (LENGTH l1 = LENGTH l2) ==> (UNZIP (ZIP (l1,l2)) = (l1,l2))
   
   [ZIP]  Theorem
      
      |- (ZIP ([],[]) = []) /\
         !x1 l1 x2 l2. ZIP (x1::l1,x2::l2) = (x1,x2)::ZIP (l1,l2)
   
   [ZIP_APPEND]  Theorem
      
      |- !a b c d.
           (LENGTH a = LENGTH b) /\ (LENGTH c = LENGTH d) ==>
           (ZIP (a,b) ++ ZIP (c,d) = ZIP (a ++ c,b ++ d))
   
   [ZIP_FIRSTN]  Theorem
      
      |- !n a b.
           n <= LENGTH a /\ (LENGTH a = LENGTH b) ==>
           (ZIP (TAKE n a,TAKE n b) = TAKE n (ZIP (a,b)))
   
   [ZIP_FIRSTN_LEQ]  Theorem
      
      |- !n a b.
           n <= LENGTH a /\ LENGTH a <= LENGTH b ==>
           (ZIP (TAKE n a,TAKE n b) = TAKE n (ZIP (a,TAKE (LENGTH a) b)))
   
   [ZIP_GENLIST]  Theorem
      
      |- !l f n.
           (LENGTH l = n) ==>
           (ZIP (l,GENLIST f n) = GENLIST (\x. (EL x l,f x)) n)
   
   [ZIP_SNOC]  Theorem
      
      |- !l1 l2.
           (LENGTH l1 = LENGTH l2) ==>
           !x1 x2. ZIP (SNOC x1 l1,SNOC x2 l2) = SNOC (x1,x2) (ZIP (l1,l2))
   
   [ZIP_UNZIP]  Theorem
      
      |- !l. ZIP (UNZIP l) = l
   
   [list_CASES]  Theorem
      
      |- !l. (l = []) \/ ?t h. l = h::t
   
   [list_INDUCT]  Theorem
      
      |- !P. P [] /\ (!l. P l ==> !x. P (x::l)) ==> !l. P l
   
   
*)
end
