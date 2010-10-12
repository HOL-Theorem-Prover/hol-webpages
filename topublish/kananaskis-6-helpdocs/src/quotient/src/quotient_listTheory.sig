signature quotient_listTheory =
sig
  type thm = Thm.thm
  
  (*  Definitions  *)
    val LIST_REL_curried_def : thm
    val LIST_REL_tupled_primitive_def : thm
  
  (*  Theorems  *)
    val ALL_EL_PRS : thm
    val ALL_EL_RSP : thm
    val APPEND_PRS : thm
    val APPEND_RSP : thm
    val CONS_PRS : thm
    val CONS_RSP : thm
    val FILTER_PRS : thm
    val FILTER_RSP : thm
    val FLAT_PRS : thm
    val FLAT_RSP : thm
    val FOLDL_PRS : thm
    val FOLDL_RSP : thm
    val FOLDR_PRS : thm
    val FOLDR_RSP : thm
    val LENGTH_PRS : thm
    val LENGTH_RSP : thm
    val LIST_EQUIV : thm
    val LIST_MAP_I : thm
    val LIST_QUOTIENT : thm
    val LIST_REL_EQ : thm
    val LIST_REL_REFL : thm
    val LIST_REL_REL : thm
    val LIST_REL_def : thm
    val LIST_REL_ind : thm
    val MAP_PRS : thm
    val MAP_RSP : thm
    val NIL_PRS : thm
    val NIL_RSP : thm
    val NULL_PRS : thm
    val NULL_RSP : thm
    val REVERSE_PRS : thm
    val REVERSE_RSP : thm
    val SOME_EL_PRS : thm
    val SOME_EL_RSP : thm
  
  val quotient_list_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [quotient] Parent theory of "quotient_list"
   
   [rich_list] Parent theory of "quotient_list"
   
   [LIST_REL_curried_def]  Definition
      
      |- ∀x x1 x2. LIST_REL x x1 x2 ⇔ LIST_REL_tupled (x,x1,x2)
   
   [LIST_REL_tupled_primitive_def]  Definition
      
      |- LIST_REL_tupled =
         WFREC (@R'. WF R' ∧ ∀b a bs as R. R' (R,as,bs) (R,a::as,b::bs))
           (λLIST_REL_tupled a'.
              case a' of
                 (R,[],[]) -> I T
              || (R,[],b::bs) -> I F
              || (R,a::as,[]) -> I F
              || (R,a::as,b'::bs') -> I (R a b' ∧ LIST_REL_tupled (R,as,bs')))
   
   [ALL_EL_PRS]  Theorem
      
      |- ∀R abs rep.
           QUOTIENT R abs rep ⇒ ∀l P. EVERY P l ⇔ EVERY ((abs --> I) P) (MAP rep l)
   
   [ALL_EL_RSP]  Theorem
      
      |- ∀R abs rep.
           QUOTIENT R abs rep ⇒
           ∀l1 l2 P1 P2.
             (R ===> $<=>) P1 P2 ∧ LIST_REL R l1 l2 ⇒ (EVERY P1 l1 ⇔ EVERY P2 l2)
   
   [APPEND_PRS]  Theorem
      
      |- ∀R abs rep.
           QUOTIENT R abs rep ⇒ ∀l m. l ++ m = MAP abs (MAP rep l ++ MAP rep m)
   
   [APPEND_RSP]  Theorem
      
      |- ∀R abs rep.
           QUOTIENT R abs rep ⇒
           ∀l1 l2 m1 m2.
             LIST_REL R l1 l2 ∧ LIST_REL R m1 m2 ⇒ LIST_REL R (l1 ++ m1) (l2 ++ m2)
   
   [CONS_PRS]  Theorem
      
      |- ∀R abs rep. QUOTIENT R abs rep ⇒ ∀t h. h::t = MAP abs (rep h::MAP rep t)
   
   [CONS_RSP]  Theorem
      
      |- ∀R abs rep.
           QUOTIENT R abs rep ⇒
           ∀t1 t2 h1 h2. R h1 h2 ∧ LIST_REL R t1 t2 ⇒ LIST_REL R (h1::t1) (h2::t2)
   
   [FILTER_PRS]  Theorem
      
      |- ∀R abs rep.
           QUOTIENT R abs rep ⇒
           ∀P l. FILTER P l = MAP abs (FILTER ((abs --> I) P) (MAP rep l))
   
   [FILTER_RSP]  Theorem
      
      |- ∀R abs rep.
           QUOTIENT R abs rep ⇒
           ∀P1 P2 l1 l2.
             (R ===> $<=>) P1 P2 ∧ LIST_REL R l1 l2 ⇒
             LIST_REL R (FILTER P1 l1) (FILTER P2 l2)
   
   [FLAT_PRS]  Theorem
      
      |- ∀R abs rep.
           QUOTIENT R abs rep ⇒ ∀l. FLAT l = MAP abs (FLAT (MAP (MAP rep) l))
   
   [FLAT_RSP]  Theorem
      
      |- ∀R abs rep.
           QUOTIENT R abs rep ⇒
           ∀l1 l2. LIST_REL (LIST_REL R) l1 l2 ⇒ LIST_REL R (FLAT l1) (FLAT l2)
   
   [FOLDL_PRS]  Theorem
      
      |- ∀R1 abs1 rep1.
           QUOTIENT R1 abs1 rep1 ⇒
           ∀R2 abs2 rep2.
             QUOTIENT R2 abs2 rep2 ⇒
             ∀l f e.
               FOLDL f e l =
               abs1 (FOLDL ((abs1 --> abs2 --> rep1) f) (rep1 e) (MAP rep2 l))
   
   [FOLDL_RSP]  Theorem
      
      |- ∀R1 abs1 rep1.
           QUOTIENT R1 abs1 rep1 ⇒
           ∀R2 abs2 rep2.
             QUOTIENT R2 abs2 rep2 ⇒
             ∀l1 l2 f1 f2 e1 e2.
               (R1 ===> R2 ===> R1) f1 f2 ∧ R1 e1 e2 ∧ LIST_REL R2 l1 l2 ⇒
               R1 (FOLDL f1 e1 l1) (FOLDL f2 e2 l2)
   
   [FOLDR_PRS]  Theorem
      
      |- ∀R1 abs1 rep1.
           QUOTIENT R1 abs1 rep1 ⇒
           ∀R2 abs2 rep2.
             QUOTIENT R2 abs2 rep2 ⇒
             ∀l f e.
               FOLDR f e l =
               abs2 (FOLDR ((abs1 --> abs2 --> rep2) f) (rep2 e) (MAP rep1 l))
   
   [FOLDR_RSP]  Theorem
      
      |- ∀R1 abs1 rep1.
           QUOTIENT R1 abs1 rep1 ⇒
           ∀R2 abs2 rep2.
             QUOTIENT R2 abs2 rep2 ⇒
             ∀l1 l2 f1 f2 e1 e2.
               (R1 ===> R2 ===> R2) f1 f2 ∧ R2 e1 e2 ∧ LIST_REL R1 l1 l2 ⇒
               R2 (FOLDR f1 e1 l1) (FOLDR f2 e2 l2)
   
   [LENGTH_PRS]  Theorem
      
      |- ∀R abs rep. QUOTIENT R abs rep ⇒ ∀l. LENGTH l = LENGTH (MAP rep l)
   
   [LENGTH_RSP]  Theorem
      
      |- ∀R abs rep.
           QUOTIENT R abs rep ⇒ ∀l1 l2. LIST_REL R l1 l2 ⇒ (LENGTH l1 = LENGTH l2)
   
   [LIST_EQUIV]  Theorem
      
      |- ∀R. EQUIV R ⇒ EQUIV (LIST_REL R)
   
   [LIST_MAP_I]  Theorem
      
      |- MAP I = I
   
   [LIST_QUOTIENT]  Theorem
      
      |- ∀R abs rep. QUOTIENT R abs rep ⇒ QUOTIENT (LIST_REL R) (MAP abs) (MAP rep)
   
   [LIST_REL_EQ]  Theorem
      
      |- LIST_REL $= = $=
   
   [LIST_REL_REFL]  Theorem
      
      |- ∀R. (∀x y. R x y ⇔ (R x = R y)) ⇒ ∀x. LIST_REL R x x
   
   [LIST_REL_REL]  Theorem
      
      |- ∀R abs rep.
           QUOTIENT R abs rep ⇒
           ∀r s.
             LIST_REL R r s ⇔
             LIST_REL R r r ∧ LIST_REL R s s ∧ (MAP abs r = MAP abs s)
   
   [LIST_REL_def]  Theorem
      
      |- (∀R. LIST_REL R [] [] ⇔ T) ∧ (∀as a R. LIST_REL R (a::as) [] ⇔ F) ∧
         (∀bs b R. LIST_REL R [] (b::bs) ⇔ F) ∧
         ∀bs b as a R. LIST_REL R (a::as) (b::bs) ⇔ R a b ∧ LIST_REL R as bs
   
   [LIST_REL_ind]  Theorem
      
      |- ∀P.
           (∀R. P R [] []) ∧ (∀R a as. P R (a::as) []) ∧ (∀R b bs. P R [] (b::bs)) ∧
           (∀R a as b bs. P R as bs ⇒ P R (a::as) (b::bs)) ⇒
           ∀v v1 v2. P v v1 v2
   
   [MAP_PRS]  Theorem
      
      |- ∀R1 abs1 rep1.
           QUOTIENT R1 abs1 rep1 ⇒
           ∀R2 abs2 rep2.
             QUOTIENT R2 abs2 rep2 ⇒
             ∀l f. MAP f l = MAP abs2 (MAP ((abs1 --> rep2) f) (MAP rep1 l))
   
   [MAP_RSP]  Theorem
      
      |- ∀R1 abs1 rep1.
           QUOTIENT R1 abs1 rep1 ⇒
           ∀R2 abs2 rep2.
             QUOTIENT R2 abs2 rep2 ⇒
             ∀l1 l2 f1 f2.
               (R1 ===> R2) f1 f2 ∧ LIST_REL R1 l1 l2 ⇒
               LIST_REL R2 (MAP f1 l1) (MAP f2 l2)
   
   [NIL_PRS]  Theorem
      
      |- ∀R abs rep. QUOTIENT R abs rep ⇒ ([] = MAP abs [])
   
   [NIL_RSP]  Theorem
      
      |- ∀R abs rep. QUOTIENT R abs rep ⇒ LIST_REL R [] []
   
   [NULL_PRS]  Theorem
      
      |- ∀R abs rep. QUOTIENT R abs rep ⇒ ∀l. NULL l ⇔ NULL (MAP rep l)
   
   [NULL_RSP]  Theorem
      
      |- ∀R abs rep.
           QUOTIENT R abs rep ⇒ ∀l1 l2. LIST_REL R l1 l2 ⇒ (NULL l1 ⇔ NULL l2)
   
   [REVERSE_PRS]  Theorem
      
      |- ∀R abs rep.
           QUOTIENT R abs rep ⇒ ∀l. REVERSE l = MAP abs (REVERSE (MAP rep l))
   
   [REVERSE_RSP]  Theorem
      
      |- ∀R abs rep.
           QUOTIENT R abs rep ⇒
           ∀l1 l2. LIST_REL R l1 l2 ⇒ LIST_REL R (REVERSE l1) (REVERSE l2)
   
   [SOME_EL_PRS]  Theorem
      
      |- ∀R abs rep.
           QUOTIENT R abs rep ⇒ ∀l P. EXISTS P l ⇔ EXISTS ((abs --> I) P) (MAP rep l)
   
   [SOME_EL_RSP]  Theorem
      
      |- ∀R abs rep.
           QUOTIENT R abs rep ⇒
           ∀l1 l2 P1 P2.
             (R ===> $<=>) P1 P2 ∧ LIST_REL R l1 l2 ⇒ (EXISTS P1 l1 ⇔ EXISTS P2 l2)
   
   
*)
end
