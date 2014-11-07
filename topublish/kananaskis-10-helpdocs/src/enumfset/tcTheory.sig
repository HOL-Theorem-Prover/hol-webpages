signature tcTheory =
sig
  type thm = Thm.thm

  (*  Definitions  *)
    val BRESTR : thm
    val DRESTR : thm
    val FMAP_TO_RELN : thm
    val RELN_TO_FMAP : thm
    val RRESTR : thm
    val TC_ITER : thm
    val TC_MOD : thm
    val subTC : thm

  (*  Theorems  *)
    val DRESTR_EMPTY : thm
    val DRESTR_IN : thm
    val DRESTR_RDOM : thm
    val FDOM_RDOM : thm
    val FINITE_RDOM : thm
    val I_o_f : thm
    val NOT_IN_RDOM : thm
    val O_REMPTY_O : thm
    val RDOM_SUBSET_FDOM : thm
    val RDOM_subTC : thm
    val RELN_TO_FMAP_TO_RELN_ID : thm
    val REMPTY_RRESTR : thm
    val RTC_INSERT : thm
    val SUBSET_FDOM_LEM : thm
    val TC_ITER_THM : thm
    val TC_MOD_EMPTY_ID : thm
    val TC_MOD_LEM : thm
    val subTC_EMPTY : thm
    val subTC_FDOM : thm
    val subTC_FDOM_RDOM : thm
    val subTC_INSERT : thm
    val subTC_INSERT_COR : thm
    val subTC_MAX_RDOM : thm
    val subTC_RDOM : thm
    val subTC_SUPERSET_RDOM : thm
    val subTC_thm : thm

  val tc_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [finite_map] Parent theory of "tc"

   [toto] Parent theory of "tc"

   [BRESTR]  Definition

      |- !R s. R ^|^ s = R ^| s |^ s

   [DRESTR]  Definition

      |- !R s a b. (R ^| s) a b <=> a IN s /\ R a b

   [FMAP_TO_RELN]  Definition

      |- !f x. FMAP_TO_RELN f x = if x IN FDOM f then f ' x else {}

   [RELN_TO_FMAP]  Definition

      |- !R. RELN_TO_FMAP R = FUN_FMAP R (RDOM R)

   [RRESTR]  Definition

      |- !R s a b. (R |^ s) a b <=> b IN s /\ R a b

   [TC_ITER]  Definition

      |- (!r. TC_ITER [] r = r) /\
         !x d r. TC_ITER (x::d) r = TC_ITER d (TC_MOD x (r ' x) o_f r)

   [TC_MOD]  Definition

      |- !x rx ra. TC_MOD x rx ra = if x IN ra then ra UNION rx else ra

   [subTC]  Definition

      |- !R s x y.
           subTC R s x y <=>
           R x y \/
           ?a b. (R ^|^ s)^* a b /\ a IN s /\ b IN s /\ R x a /\ R b y

   [DRESTR_EMPTY]  Theorem

      |- !R. R ^| {} = REMPTY

   [DRESTR_IN]  Theorem

      |- !R s a. (R ^| s) a = if a IN s then R a else {}

   [DRESTR_RDOM]  Theorem

      |- !R. R ^| RDOM R = R

   [FDOM_RDOM]  Theorem

      |- !R. FINITE (RDOM R) ==> (FDOM (RELN_TO_FMAP R) = RDOM R)

   [FINITE_RDOM]  Theorem

      |- !f. FINITE (RDOM (FMAP_TO_RELN f))

   [I_o_f]  Theorem

      |- !f. I o_f f = f

   [NOT_IN_RDOM]  Theorem

      |- !Q x. (Q x = {}) <=> x NOTIN RDOM Q

   [O_REMPTY_O]  Theorem

      |- (!R. R O REMPTY = REMPTY) /\ !R. REMPTY O R = REMPTY

   [RDOM_SUBSET_FDOM]  Theorem

      |- !f. RDOM (FMAP_TO_RELN f) SUBSET FDOM f

   [RDOM_subTC]  Theorem

      |- !R s. RDOM (subTC R s) = RDOM R

   [RELN_TO_FMAP_TO_RELN_ID]  Theorem

      |- !R. FINITE (RDOM R) ==> (FMAP_TO_RELN (RELN_TO_FMAP R) = R)

   [REMPTY_RRESTR]  Theorem

      |- !s. REMPTY |^ s = REMPTY

   [RTC_INSERT]  Theorem

      |- !R s a w z.
           (R ^|^ (a INSERT s))^* w z <=>
           (R ^|^ s)^* w z \/
           ((a = w) \/ ?x. x IN s /\ (R ^|^ s)^* w x /\ R x a) /\
           ((a = z) \/ ?y. y IN s /\ R a y /\ (R ^|^ s)^* y z)

   [SUBSET_FDOM_LEM]  Theorem

      |- !R s f. (subTC R s = FMAP_TO_RELN f) ==> RDOM R SUBSET FDOM f

   [TC_ITER_THM]  Theorem

      |- !R d f s.
           (s UNION set d = FDOM f) /\ (subTC R s = FMAP_TO_RELN f) ==>
           (R^+ = FMAP_TO_RELN (TC_ITER d f))

   [TC_MOD_EMPTY_ID]  Theorem

      |- !x ra. TC_MOD x {} = I

   [TC_MOD_LEM]  Theorem

      |- !R s x f.
           x IN FDOM f /\ (subTC R s = FMAP_TO_RELN f) ==>
           (subTC R (x INSERT s) = FMAP_TO_RELN (TC_MOD x (f ' x) o_f f))

   [subTC_EMPTY]  Theorem

      |- !R. subTC R {} = R

   [subTC_FDOM]  Theorem

      |- !g R.
           (subTC R (RDOM R) = FMAP_TO_RELN g) ==>
           (subTC R (FDOM g) = subTC R (RDOM R))

   [subTC_FDOM_RDOM]  Theorem

      |- !R f.
           (subTC R (FDOM f) = FMAP_TO_RELN f) ==>
           (subTC R (RDOM R) = FMAP_TO_RELN f)

   [subTC_INSERT]  Theorem

      |- !R s q x y.
           subTC R (q INSERT s) x y <=>
           subTC R s x y \/ subTC R s x q /\ subTC R s q y

   [subTC_INSERT_COR]  Theorem

      |- !R s x a.
           subTC R (x INSERT s) a =
           if x IN subTC R s a then subTC R s a UNION subTC R s x
           else subTC R s a

   [subTC_MAX_RDOM]  Theorem

      |- !R s x. x NOTIN RDOM R ==> (subTC R (x INSERT s) = subTC R s)

   [subTC_RDOM]  Theorem

      |- !R. subTC R (RDOM R) = R^+

   [subTC_SUPERSET_RDOM]  Theorem

      |- !R s. FINITE s ==> (subTC R (RDOM R UNION s) = subTC R (RDOM R))

   [subTC_thm]  Theorem

      |- !R s. subTC R s = R RUNION R O ((R ^|^ s)^* ^| s) O R


*)
end
