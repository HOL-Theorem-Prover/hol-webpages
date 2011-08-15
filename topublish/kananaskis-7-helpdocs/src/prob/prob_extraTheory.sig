signature prob_extraTheory =
sig
  type thm = Thm.thm
  
  (*  Definitions  *)
    val inf_def : thm
  
  (*  Theorems  *)
    val ABS_BETWEEN_LE : thm
    val ABS_UNIT_INTERVAL : thm
    val APPEND_MEM : thm
    val BOOL_BOOL_CASES : thm
    val BOOL_BOOL_CASES_THM : thm
    val COMPL_CLAUSES : thm
    val COMPL_COMPL : thm
    val COMPL_SPLITS : thm
    val DIVISION_TWO : thm
    val DIV_THEN_MULT : thm
    val DIV_TWO : thm
    val DIV_TWO_BASIC : thm
    val DIV_TWO_CANCEL : thm
    val DIV_TWO_EXP : thm
    val DIV_TWO_MONO : thm
    val DIV_TWO_MONO_EVEN : thm
    val DIV_TWO_UNIQUE : thm
    val EQ_EXT_EQ : thm
    val EVEN_EXP_TWO : thm
    val EVEN_ODD_BASIC : thm
    val EVEN_ODD_EXISTS_EQ : thm
    val EXISTS_LONGEST : thm
    val EXP_DIV_TWO : thm
    val FILTER_FALSE : thm
    val FILTER_MEM : thm
    val FILTER_OUT_ELT : thm
    val FILTER_TRUE : thm
    val FOLDR_MAP : thm
    val GSPEC_DEF_ALT : thm
    val HALF_CANCEL : thm
    val HALF_LT_1 : thm
    val HALF_POS : thm
    val INF_DEF_ALT : thm
    val INTER_IS_EMPTY : thm
    val INTER_UNION_COMPL : thm
    val INTER_UNION_RDISTRIB : thm
    val INV_SUC : thm
    val INV_SUC_MAX : thm
    val INV_SUC_POS : thm
    val IN_COMPL : thm
    val IN_EMPTY : thm
    val IS_PREFIX_ANTISYM : thm
    val IS_PREFIX_BUTLAST : thm
    val IS_PREFIX_LENGTH : thm
    val IS_PREFIX_LENGTH_ANTI : thm
    val IS_PREFIX_NIL : thm
    val IS_PREFIX_REFL : thm
    val IS_PREFIX_SNOC : thm
    val IS_PREFIX_TRANS : thm
    val LAST_MAP_CONS : thm
    val LAST_MEM : thm
    val LENGTH_FILTER : thm
    val MAP_ID : thm
    val MAP_MEM : thm
    val MEM_FILTER : thm
    val MEM_NIL : thm
    val MEM_NIL_MAP_CONS : thm
    val MOD_TWO : thm
    val ONE_MINUS_HALF : thm
    val POW_HALF_EXP : thm
    val POW_HALF_MONO : thm
    val POW_HALF_POS : thm
    val POW_HALF_TWICE : thm
    val RAND_THM : thm
    val REAL_INF_MIN : thm
    val REAL_INVINV_ALL : thm
    val REAL_LE_EQ : thm
    val REAL_LE_INV_LE : thm
    val REAL_POW : thm
    val REAL_SUP_EXISTS_UNIQUE : thm
    val REAL_SUP_LE_X : thm
    val REAL_SUP_MAX : thm
    val REAL_X_LE_SUP : thm
    val SET_EQ_EXT : thm
    val SUBSET_EQ : thm
    val SUBSET_EQ_DECOMP : thm
    val UNION_DEF_ALT : thm
    val UNION_DISJOINT_SPLIT : thm
    val X_HALF_HALF : thm
  
  val prob_extra_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [poly] Parent theory of "prob_extra"
   
   [transc] Parent theory of "prob_extra"
   
   [inf_def]  Definition
      
      |- ∀P. inf P = -sup (IMAGE numeric_negate P)
   
   [ABS_BETWEEN_LE]  Theorem
      
      |- ∀x y d. 0 ≤ d ∧ x − d ≤ y ∧ y ≤ x + d ⇔ abs (y − x) ≤ d
   
   [ABS_UNIT_INTERVAL]  Theorem
      
      |- ∀x y. 0 ≤ x ∧ x ≤ 1 ∧ 0 ≤ y ∧ y ≤ 1 ⇒ abs (x − y) ≤ 1
   
   [APPEND_MEM]  Theorem
      
      |- ∀x l1 l2. MEM x (l1 ++ l2) ⇔ MEM x l1 ∨ MEM x l2
   
   [BOOL_BOOL_CASES]  Theorem
      
      |- ∀P. P (λb. F) ∧ P (λb. T) ∧ P (λb. b) ∧ P (λb. ¬b) ⇒ ∀f. P f
   
   [BOOL_BOOL_CASES_THM]  Theorem
      
      |- ∀f. (f = (λb. F)) ∨ (f = (λb. T)) ∨ (f = (λb. b)) ∨ (f = (λb. ¬b))
   
   [COMPL_CLAUSES]  Theorem
      
      |- ∀s. (COMPL s ∩ s = ∅) ∧ (COMPL s ∪ s = 𝕌(:α))
   
   [COMPL_COMPL]  Theorem
      
      |- ∀s. COMPL (COMPL s) = s
   
   [COMPL_SPLITS]  Theorem
      
      |- ∀p q. p ∩ q ∪ COMPL p ∩ q = q
   
   [DIVISION_TWO]  Theorem
      
      |- ∀n.
           (n = 2 * (n DIV 2) + n MOD 2) ∧ ((n MOD 2 = 0) ∨ (n MOD 2 = 1))
   
   [DIV_THEN_MULT]  Theorem
      
      |- ∀p q. SUC q * (p DIV SUC q) ≤ p
   
   [DIV_TWO]  Theorem
      
      |- ∀n. n = 2 * (n DIV 2) + n MOD 2
   
   [DIV_TWO_BASIC]  Theorem
      
      |- (0 DIV 2 = 0) ∧ (1 DIV 2 = 0) ∧ (2 DIV 2 = 1)
   
   [DIV_TWO_CANCEL]  Theorem
      
      |- ∀n. (2 * n DIV 2 = n) ∧ (SUC (2 * n) DIV 2 = n)
   
   [DIV_TWO_EXP]  Theorem
      
      |- ∀n k. k DIV 2 < 2 ** n ⇔ k < 2 ** SUC n
   
   [DIV_TWO_MONO]  Theorem
      
      |- ∀m n. m DIV 2 < n DIV 2 ⇒ m < n
   
   [DIV_TWO_MONO_EVEN]  Theorem
      
      |- ∀m n. EVEN n ⇒ (m DIV 2 < n DIV 2 ⇔ m < n)
   
   [DIV_TWO_UNIQUE]  Theorem
      
      |- ∀n q r.
           (n = 2 * q + r) ∧ ((r = 0) ∨ (r = 1)) ⇒
           (q = n DIV 2) ∧ (r = n MOD 2)
   
   [EQ_EXT_EQ]  Theorem
      
      |- ∀f g. (∀x. f x = g x) ⇔ (f = g)
   
   [EVEN_EXP_TWO]  Theorem
      
      |- ∀n. EVEN (2 ** n) ⇔ n ≠ 0
   
   [EVEN_ODD_BASIC]  Theorem
      
      |- EVEN 0 ∧ ¬EVEN 1 ∧ EVEN 2 ∧ ¬ODD 0 ∧ ODD 1 ∧ ¬ODD 2
   
   [EVEN_ODD_EXISTS_EQ]  Theorem
      
      |- ∀n. (EVEN n ⇔ ∃m. n = 2 * m) ∧ (ODD n ⇔ ∃m. n = SUC (2 * m))
   
   [EXISTS_LONGEST]  Theorem
      
      |- ∀x y. ∃z. MEM z (x::y) ∧ ∀w. MEM w (x::y) ⇒ LENGTH w ≤ LENGTH z
   
   [EXP_DIV_TWO]  Theorem
      
      |- ∀n. 2 ** SUC n DIV 2 = 2 ** n
   
   [FILTER_FALSE]  Theorem
      
      |- ∀l. FILTER (λx. F) l = []
   
   [FILTER_MEM]  Theorem
      
      |- ∀P x l. MEM x (FILTER P l) ⇒ P x
   
   [FILTER_OUT_ELT]  Theorem
      
      |- ∀x l. MEM x l ∨ (FILTER (λy. y ≠ x) l = l)
   
   [FILTER_TRUE]  Theorem
      
      |- ∀l. FILTER (λx. T) l = l
   
   [FOLDR_MAP]  Theorem
      
      |- ∀f e g l. FOLDR f e (MAP g l) = FOLDR (λx y. f (g x) y) e l
   
   [GSPEC_DEF_ALT]  Theorem
      
      |- ∀f. GSPEC f = (λv. ∃x. (v,T) = f x)
   
   [HALF_CANCEL]  Theorem
      
      |- 2 * (1 / 2) = 1
   
   [HALF_LT_1]  Theorem
      
      |- 1 / 2 < 1
   
   [HALF_POS]  Theorem
      
      |- 0 < 1 / 2
   
   [INF_DEF_ALT]  Theorem
      
      |- ∀P. inf P = -sup (λr. P (-r))
   
   [INTER_IS_EMPTY]  Theorem
      
      |- ∀s t. (s ∩ t = ∅) ⇔ ∀x. ¬s x ∨ ¬t x
   
   [INTER_UNION_COMPL]  Theorem
      
      |- ∀s t. s ∩ t = COMPL (COMPL s ∪ COMPL t)
   
   [INTER_UNION_RDISTRIB]  Theorem
      
      |- ∀p q r. (p ∪ q) ∩ r = p ∩ r ∪ q ∩ r
   
   [INV_SUC]  Theorem
      
      |- ∀n. 0 < 1 / &SUC n ∧ 1 / &SUC n ≤ 1
   
   [INV_SUC_MAX]  Theorem
      
      |- ∀n. 1 / &SUC n ≤ 1
   
   [INV_SUC_POS]  Theorem
      
      |- ∀n. 0 < 1 / &SUC n
   
   [IN_COMPL]  Theorem
      
      |- ∀x s. x ∈ COMPL s ⇔ x ∉ s
   
   [IN_EMPTY]  Theorem
      
      |- ∀x. x ∉ ∅
   
   [IS_PREFIX_ANTISYM]  Theorem
      
      |- ∀x y. x ≼ y ∧ y ≼ x ⇒ (x = y)
   
   [IS_PREFIX_BUTLAST]  Theorem
      
      |- ∀x y. FRONT (x::y) ≼ x::y
   
   [IS_PREFIX_LENGTH]  Theorem
      
      |- ∀x y. x ≼ y ⇒ LENGTH x ≤ LENGTH y
   
   [IS_PREFIX_LENGTH_ANTI]  Theorem
      
      |- ∀x y. x ≼ y ∧ (LENGTH x = LENGTH y) ⇒ (x = y)
   
   [IS_PREFIX_NIL]  Theorem
      
      |- ∀x. [] ≼ x ∧ (x ≼ [] ⇔ (x = []))
   
   [IS_PREFIX_REFL]  Theorem
      
      |- ∀x. x ≼ x
   
   [IS_PREFIX_SNOC]  Theorem
      
      |- ∀x y z. z ≼ SNOC x y ⇔ z ≼ y ∨ (z = SNOC x y)
   
   [IS_PREFIX_TRANS]  Theorem
      
      |- ∀x y z. y ≼ x ∧ z ≼ y ⇒ z ≼ x
   
   [LAST_MAP_CONS]  Theorem
      
      |- ∀b h t. ∃x. LAST (MAP (CONS b) (h::t)) = b::x
   
   [LAST_MEM]  Theorem
      
      |- ∀h t. MEM (LAST (h::t)) (h::t)
   
   [LENGTH_FILTER]  Theorem
      
      |- ∀P l. LENGTH (FILTER P l) ≤ LENGTH l
   
   [MAP_ID]  Theorem
      
      |- ∀l. MAP (λx. x) l = l
   
   [MAP_MEM]  Theorem
      
      |- ∀f l x. MEM x (MAP f l) ⇔ ∃y. MEM y l ∧ (x = f y)
   
   [MEM_FILTER]  Theorem
      
      |- ∀P l x. MEM x (FILTER P l) ⇒ MEM x l
   
   [MEM_NIL]  Theorem
      
      |- ∀l. (∀x. ¬MEM x l) ⇔ (l = [])
   
   [MEM_NIL_MAP_CONS]  Theorem
      
      |- ∀x l. ¬MEM [] (MAP (CONS x) l)
   
   [MOD_TWO]  Theorem
      
      |- ∀n. n MOD 2 = if EVEN n then 0 else 1
   
   [ONE_MINUS_HALF]  Theorem
      
      |- 1 − 1 / 2 = 1 / 2
   
   [POW_HALF_EXP]  Theorem
      
      |- ∀n. (1 / 2) pow n = inv (&(2 ** n))
   
   [POW_HALF_MONO]  Theorem
      
      |- ∀m n. m ≤ n ⇒ (1 / 2) pow n ≤ (1 / 2) pow m
   
   [POW_HALF_POS]  Theorem
      
      |- ∀n. 0 < (1 / 2) pow n
   
   [POW_HALF_TWICE]  Theorem
      
      |- ∀n. (1 / 2) pow n = 2 * (1 / 2) pow SUC n
   
   [RAND_THM]  Theorem
      
      |- ∀f x y. (x = y) ⇒ (f x = f y)
   
   [REAL_INF_MIN]  Theorem
      
      |- ∀P z. P z ∧ (∀x. P x ⇒ z ≤ x) ⇒ (inf P = z)
   
   [REAL_INVINV_ALL]  Theorem
      
      |- ∀x. inv (inv x) = x
   
   [REAL_LE_EQ]  Theorem
      
      |- ∀x y. x ≤ y ∧ y ≤ x ⇒ (x = y)
   
   [REAL_LE_INV_LE]  Theorem
      
      |- ∀x y. 0 < x ∧ x ≤ y ⇒ inv y ≤ inv x
   
   [REAL_POW]  Theorem
      
      |- ∀m n. &m pow n = &(m ** n)
   
   [REAL_SUP_EXISTS_UNIQUE]  Theorem
      
      |- ∀P.
           (∃x. P x) ∧ (∃z. ∀x. P x ⇒ x ≤ z) ⇒
           ∃!s. ∀y. (∃x. P x ∧ y < x) ⇔ y < s
   
   [REAL_SUP_LE_X]  Theorem
      
      |- ∀P x. (∃r. P r) ∧ (∀r. P r ⇒ r ≤ x) ⇒ sup P ≤ x
   
   [REAL_SUP_MAX]  Theorem
      
      |- ∀P z. P z ∧ (∀x. P x ⇒ x ≤ z) ⇒ (sup P = z)
   
   [REAL_X_LE_SUP]  Theorem
      
      |- ∀P x.
           (∃r. P r) ∧ (∃z. ∀r. P r ⇒ r ≤ z) ∧ (∃r. P r ∧ x ≤ r) ⇒
           x ≤ sup P
   
   [SET_EQ_EXT]  Theorem
      
      |- ∀s t. (s = t) ⇔ ∀v. v ∈ s ⇔ v ∈ t
   
   [SUBSET_EQ]  Theorem
      
      |- ∀s t. (s = t) ⇔ s ⊆ t ∧ t ⊆ s
   
   [SUBSET_EQ_DECOMP]  Theorem
      
      |- ∀s t. s ⊆ t ∧ t ⊆ s ⇒ (s = t)
   
   [UNION_DEF_ALT]  Theorem
      
      |- ∀s t. s ∪ t = (λx. s x ∨ t x)
   
   [UNION_DISJOINT_SPLIT]  Theorem
      
      |- ∀s t u. (s ∪ t = s ∪ u) ∧ (s ∩ t = ∅) ∧ (s ∩ u = ∅) ⇒ (t = u)
   
   [X_HALF_HALF]  Theorem
      
      |- ∀x. 1 / 2 * x + 1 / 2 * x = x
   
   
*)
end
