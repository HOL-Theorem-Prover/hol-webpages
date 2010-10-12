signature polyTheory =
sig
  type thm = Thm.thm
  
  (*  Definitions  *)
    val degree : thm
    val normalize : thm
    val poly_add_def : thm
    val poly_cmul_def : thm
    val poly_def : thm
    val poly_diff_aux_def : thm
    val poly_diff_def : thm
    val poly_divides : thm
    val poly_exp_def : thm
    val poly_mul_def : thm
    val poly_neg_def : thm
    val poly_order : thm
    val rsquarefree : thm
  
  (*  Theorems  *)
    val DEGREE_ZERO : thm
    val FINITE_LEMMA : thm
    val ORDER : thm
    val ORDER_DECOMP : thm
    val ORDER_DIFF : thm
    val ORDER_DIVIDES : thm
    val ORDER_MUL : thm
    val ORDER_POLY : thm
    val ORDER_ROOT : thm
    val ORDER_THM : thm
    val ORDER_UNIQUE : thm
    val POLY_ADD : thm
    val POLY_ADD_CLAUSES : thm
    val POLY_ADD_RZERO : thm
    val POLY_CMUL : thm
    val POLY_CMUL_CLAUSES : thm
    val POLY_CONT : thm
    val POLY_DIFF : thm
    val POLY_DIFFERENTIABLE : thm
    val POLY_DIFF_ADD : thm
    val POLY_DIFF_AUX_ADD : thm
    val POLY_DIFF_AUX_CMUL : thm
    val POLY_DIFF_AUX_ISZERO : thm
    val POLY_DIFF_AUX_MUL_LEMMA : thm
    val POLY_DIFF_AUX_NEG : thm
    val POLY_DIFF_CLAUSES : thm
    val POLY_DIFF_CMUL : thm
    val POLY_DIFF_EXP : thm
    val POLY_DIFF_EXP_PRIME : thm
    val POLY_DIFF_ISZERO : thm
    val POLY_DIFF_LEMMA : thm
    val POLY_DIFF_MUL : thm
    val POLY_DIFF_MUL_LEMMA : thm
    val POLY_DIFF_NEG : thm
    val POLY_DIFF_WELLDEF : thm
    val POLY_DIFF_ZERO : thm
    val POLY_DIVIDES_ADD : thm
    val POLY_DIVIDES_EXP : thm
    val POLY_DIVIDES_REFL : thm
    val POLY_DIVIDES_SUB : thm
    val POLY_DIVIDES_SUB2 : thm
    val POLY_DIVIDES_TRANS : thm
    val POLY_DIVIDES_ZERO : thm
    val POLY_ENTIRE : thm
    val POLY_ENTIRE_LEMMA : thm
    val POLY_EXP : thm
    val POLY_EXP_ADD : thm
    val POLY_EXP_DIVIDES : thm
    val POLY_EXP_EQ_0 : thm
    val POLY_EXP_PRIME_EQ_0 : thm
    val POLY_IVT_NEG : thm
    val POLY_IVT_POS : thm
    val POLY_LENGTH_MUL : thm
    val POLY_LINEAR_DIVIDES : thm
    val POLY_LINEAR_REM : thm
    val POLY_MONO : thm
    val POLY_MUL : thm
    val POLY_MUL_ASSOC : thm
    val POLY_MUL_CLAUSES : thm
    val POLY_MUL_LCANCEL : thm
    val POLY_MVT : thm
    val POLY_NEG : thm
    val POLY_NEG_CLAUSES : thm
    val POLY_NORMALIZE : thm
    val POLY_ORDER : thm
    val POLY_ORDER_EXISTS : thm
    val POLY_PRIMES : thm
    val POLY_PRIME_EQ_0 : thm
    val POLY_ROOTS_FINITE : thm
    val POLY_ROOTS_FINITE_LEMMA : thm
    val POLY_ROOTS_FINITE_SET : thm
    val POLY_ROOTS_INDEX_LEMMA : thm
    val POLY_ROOTS_INDEX_LENGTH : thm
    val POLY_SQUAREFREE_DECOMP : thm
    val POLY_SQUAREFREE_DECOMP_ORDER : thm
    val POLY_ZERO : thm
    val POLY_ZERO_LEMMA : thm
    val RSQUAREFREE_DECOMP : thm
    val RSQUAREFREE_ROOTS : thm
  
  val poly_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [lim] Parent theory of "poly"
   
   [degree]  Definition
      
      |- ∀p. degree p = PRE (LENGTH (normalize p))
   
   [normalize]  Definition
      
      |- (normalize [] = []) ∧
         ∀h t.
           normalize (h::t) =
           if normalize t = [] then if h = 0 then [] else [h] else h::normalize t
   
   [poly_add_def]  Definition
      
      |- (∀l2. [] + l2 = l2) ∧
         ∀h t l2. (h::t) + l2 = if l2 = [] then h::t else h + HD l2::t + TL l2
   
   [poly_cmul_def]  Definition
      
      |- (∀c. c ## [] = []) ∧ ∀c h t. c ## (h::t) = c * h::c ## t
   
   [poly_def]  Definition
      
      |- (∀x. poly [] x = 0) ∧ ∀h t x. poly (h::t) x = h + x * poly t x
   
   [poly_diff_aux_def]  Definition
      
      |- (∀n. poly_diff_aux n [] = []) ∧
         ∀n h t. poly_diff_aux n (h::t) = &n * h::poly_diff_aux (SUC n) t
   
   [poly_diff_def]  Definition
      
      |- ∀l. diff l = if l = [] then [] else poly_diff_aux 1 (TL l)
   
   [poly_divides]  Definition
      
      |- ∀p1 p2. p1 poly_divides p2 ⇔ ∃q. poly p2 = poly (p1 * q)
   
   [poly_exp_def]  Definition
      
      |- (∀p. p poly_exp 0 = [1]) ∧ ∀p n. p poly_exp SUC n = p * p poly_exp n
   
   [poly_mul_def]  Definition
      
      |- (∀l2. [] * l2 = []) ∧
         ∀h t l2. (h::t) * l2 = if t = [] then h ## l2 else h ## l2 + (0::t * l2)
   
   [poly_neg_def]  Definition
      
      |- $~ = $## (-1)
   
   [poly_order]  Definition
      
      |- ∀a p.
           poly_order a p =
           @n.
             [-a; 1] poly_exp n poly_divides p ∧
             ¬([-a; 1] poly_exp SUC n poly_divides p)
   
   [rsquarefree]  Definition
      
      |- ∀p.
           rsquarefree p ⇔
           poly p ≠ poly [] ∧ ∀a. (poly_order a p = 0) ∨ (poly_order a p = 1)
   
   [DEGREE_ZERO]  Theorem
      
      |- ∀p. (poly p = poly []) ⇒ (degree p = 0)
   
   [FINITE_LEMMA]  Theorem
      
      |- ∀i N P. (∀x. P x ⇒ ∃n. n < N ∧ (x = i n)) ⇒ ∃a. ∀x. P x ⇒ x < a
   
   [ORDER]  Theorem
      
      |- ∀p a n.
           [-a; 1] poly_exp n poly_divides p ∧
           ¬([-a; 1] poly_exp SUC n poly_divides p) ⇔
           (n = poly_order a p) ∧ poly p ≠ poly []
   
   [ORDER_DECOMP]  Theorem
      
      |- ∀p a.
           poly p ≠ poly [] ⇒
           ∃q.
             (poly p = poly ([-a; 1] poly_exp poly_order a p * q)) ∧
             ¬([-a; 1] poly_divides q)
   
   [ORDER_DIFF]  Theorem
      
      |- ∀p a.
           poly (diff p) ≠ poly [] ∧ poly_order a p ≠ 0 ⇒
           (poly_order a p = SUC (poly_order a (diff p)))
   
   [ORDER_DIVIDES]  Theorem
      
      |- ∀p a n.
           [-a; 1] poly_exp n poly_divides p ⇔
           (poly p = poly []) ∨ n ≤ poly_order a p
   
   [ORDER_MUL]  Theorem
      
      |- ∀a p q.
           poly (p * q) ≠ poly [] ⇒
           (poly_order a (p * q) = poly_order a p + poly_order a q)
   
   [ORDER_POLY]  Theorem
      
      |- ∀p q a. (poly p = poly q) ⇒ (poly_order a p = poly_order a q)
   
   [ORDER_ROOT]  Theorem
      
      |- ∀p a. (poly p a = 0) ⇔ (poly p = poly []) ∨ poly_order a p ≠ 0
   
   [ORDER_THM]  Theorem
      
      |- ∀p a.
           poly p ≠ poly [] ⇒
           [-a; 1] poly_exp poly_order a p poly_divides p ∧
           ¬([-a; 1] poly_exp SUC (poly_order a p) poly_divides p)
   
   [ORDER_UNIQUE]  Theorem
      
      |- ∀p a n.
           poly p ≠ poly [] ∧ [-a; 1] poly_exp n poly_divides p ∧
           ¬([-a; 1] poly_exp SUC n poly_divides p) ⇒
           (n = poly_order a p)
   
   [POLY_ADD]  Theorem
      
      |- ∀p1 p2 x. poly (p1 + p2) x = poly p1 x + poly p2 x
   
   [POLY_ADD_CLAUSES]  Theorem
      
      |- ([] + p2 = p2) ∧ (p1 + [] = p1) ∧ ((h1::t1) + (h2::t2) = h1 + h2::t1 + t2)
   
   [POLY_ADD_RZERO]  Theorem
      
      |- ∀p. poly (p + []) = poly p
   
   [POLY_CMUL]  Theorem
      
      |- ∀p c x. poly (c ## p) x = c * poly p x
   
   [POLY_CMUL_CLAUSES]  Theorem
      
      |- (c ## [] = []) ∧ (c ## (h::t) = c * h::c ## t)
   
   [POLY_CONT]  Theorem
      
      |- ∀l x. (λx. poly l x) contl x
   
   [POLY_DIFF]  Theorem
      
      |- ∀l x. ((λx. poly l x) diffl poly (diff l) x) x
   
   [POLY_DIFFERENTIABLE]  Theorem
      
      |- ∀l x. (λx. poly l x) differentiable x
   
   [POLY_DIFF_ADD]  Theorem
      
      |- ∀p1 p2. poly (diff (p1 + p2)) = poly (diff p1 + diff p2)
   
   [POLY_DIFF_AUX_ADD]  Theorem
      
      |- ∀p1 p2 n.
           poly (poly_diff_aux n (p1 + p2)) =
           poly (poly_diff_aux n p1 + poly_diff_aux n p2)
   
   [POLY_DIFF_AUX_CMUL]  Theorem
      
      |- ∀p c n. poly (poly_diff_aux n (c ## p)) = poly (c ## poly_diff_aux n p)
   
   [POLY_DIFF_AUX_ISZERO]  Theorem
      
      |- ∀p n. EVERY (λc. c = 0) (poly_diff_aux (SUC n) p) ⇔ EVERY (λc. c = 0) p
   
   [POLY_DIFF_AUX_MUL_LEMMA]  Theorem
      
      |- ∀p n. poly (poly_diff_aux (SUC n) p) = poly (poly_diff_aux n p + p)
   
   [POLY_DIFF_AUX_NEG]  Theorem
      
      |- ∀p n. poly (poly_diff_aux n (¬p)) = poly (¬poly_diff_aux n p)
   
   [POLY_DIFF_CLAUSES]  Theorem
      
      |- (diff [] = []) ∧ (diff [c] = []) ∧ (diff (h::t) = poly_diff_aux 1 t)
   
   [POLY_DIFF_CMUL]  Theorem
      
      |- ∀p c. poly (diff (c ## p)) = poly (c ## diff p)
   
   [POLY_DIFF_EXP]  Theorem
      
      |- ∀p n.
           poly (diff (p poly_exp SUC n)) = poly (&SUC n ## p poly_exp n * diff p)
   
   [POLY_DIFF_EXP_PRIME]  Theorem
      
      |- ∀n a.
           poly (diff ([-a; 1] poly_exp SUC n)) = poly (&SUC n ## [-a; 1] poly_exp n)
   
   [POLY_DIFF_ISZERO]  Theorem
      
      |- ∀p. (poly (diff p) = poly []) ⇒ ∃h. poly p = poly [h]
   
   [POLY_DIFF_LEMMA]  Theorem
      
      |- ∀l n x.
           ((λx. x pow SUC n * poly l x) diffl
            (x pow n * poly (poly_diff_aux (SUC n) l) x)) x
   
   [POLY_DIFF_MUL]  Theorem
      
      |- ∀p1 p2. poly (diff (p1 * p2)) = poly (p1 * diff p2 + diff p1 * p2)
   
   [POLY_DIFF_MUL_LEMMA]  Theorem
      
      |- ∀t h. poly (diff (h::t)) = poly ((0::diff t) + t)
   
   [POLY_DIFF_NEG]  Theorem
      
      |- ∀p. poly (diff (¬p)) = poly (¬diff p)
   
   [POLY_DIFF_WELLDEF]  Theorem
      
      |- ∀p q. (poly p = poly q) ⇒ (poly (diff p) = poly (diff q))
   
   [POLY_DIFF_ZERO]  Theorem
      
      |- ∀p. (poly p = poly []) ⇒ (poly (diff p) = poly [])
   
   [POLY_DIVIDES_ADD]  Theorem
      
      |- ∀p q r. p poly_divides q ∧ p poly_divides r ⇒ p poly_divides q + r
   
   [POLY_DIVIDES_EXP]  Theorem
      
      |- ∀p m n. m ≤ n ⇒ p poly_exp m poly_divides p poly_exp n
   
   [POLY_DIVIDES_REFL]  Theorem
      
      |- ∀p. p poly_divides p
   
   [POLY_DIVIDES_SUB]  Theorem
      
      |- ∀p q r. p poly_divides q ∧ p poly_divides q + r ⇒ p poly_divides r
   
   [POLY_DIVIDES_SUB2]  Theorem
      
      |- ∀p q r. p poly_divides r ∧ p poly_divides q + r ⇒ p poly_divides q
   
   [POLY_DIVIDES_TRANS]  Theorem
      
      |- ∀p q r. p poly_divides q ∧ q poly_divides r ⇒ p poly_divides r
   
   [POLY_DIVIDES_ZERO]  Theorem
      
      |- ∀p q. (poly p = poly []) ⇒ q poly_divides p
   
   [POLY_ENTIRE]  Theorem
      
      |- ∀p q. (poly (p * q) = poly []) ⇔ (poly p = poly []) ∨ (poly q = poly [])
   
   [POLY_ENTIRE_LEMMA]  Theorem
      
      |- ∀p q. poly p ≠ poly [] ∧ poly q ≠ poly [] ⇒ poly (p * q) ≠ poly []
   
   [POLY_EXP]  Theorem
      
      |- ∀p n x. poly (p poly_exp n) x = poly p x pow n
   
   [POLY_EXP_ADD]  Theorem
      
      |- ∀d n p. poly (p poly_exp (n + d)) = poly (p poly_exp n * p poly_exp d)
   
   [POLY_EXP_DIVIDES]  Theorem
      
      |- ∀p q m n. p poly_exp n poly_divides q ∧ m ≤ n ⇒ p poly_exp m poly_divides q
   
   [POLY_EXP_EQ_0]  Theorem
      
      |- ∀p n. (poly (p poly_exp n) = poly []) ⇔ (poly p = poly []) ∧ n ≠ 0
   
   [POLY_EXP_PRIME_EQ_0]  Theorem
      
      |- ∀a n. poly ([a; 1] poly_exp n) ≠ poly []
   
   [POLY_IVT_NEG]  Theorem
      
      |- ∀p a b.
           a < b ∧ poly p a > 0 ∧ poly p b < 0 ⇒ ∃x. a < x ∧ x < b ∧ (poly p x = 0)
   
   [POLY_IVT_POS]  Theorem
      
      |- ∀p a b.
           a < b ∧ poly p a < 0 ∧ poly p b > 0 ⇒ ∃x. a < x ∧ x < b ∧ (poly p x = 0)
   
   [POLY_LENGTH_MUL]  Theorem
      
      |- ∀q. LENGTH ([-a; 1] * q) = SUC (LENGTH q)
   
   [POLY_LINEAR_DIVIDES]  Theorem
      
      |- ∀a p. (poly p a = 0) ⇔ (p = []) ∨ ∃q. p = [-a; 1] * q
   
   [POLY_LINEAR_REM]  Theorem
      
      |- ∀t h. ∃q r. h::t = [r] + [-a; 1] * q
   
   [POLY_MONO]  Theorem
      
      |- ∀x k p. abs x ≤ k ⇒ abs (poly p x) ≤ poly (MAP abs p) k
   
   [POLY_MUL]  Theorem
      
      |- ∀x p1 p2. poly (p1 * p2) x = poly p1 x * poly p2 x
   
   [POLY_MUL_ASSOC]  Theorem
      
      |- ∀p q r. poly (p * (q * r)) = poly (p * q * r)
   
   [POLY_MUL_CLAUSES]  Theorem
      
      |- ([] * p2 = []) ∧ ([h1] * p2 = h1 ## p2) ∧
         ((h1::k1::t1) * p2 = h1 ## p2 + (0::(k1::t1) * p2))
   
   [POLY_MUL_LCANCEL]  Theorem
      
      |- ∀p q r.
           (poly (p * q) = poly (p * r)) ⇔ (poly p = poly []) ∨ (poly q = poly r)
   
   [POLY_MVT]  Theorem
      
      |- ∀p a b.
           a < b ⇒
           ∃x. a < x ∧ x < b ∧ (poly p b − poly p a = (b − a) * poly (diff p) x)
   
   [POLY_NEG]  Theorem
      
      |- ∀p x. poly (¬p) x = -poly p x
   
   [POLY_NEG_CLAUSES]  Theorem
      
      |- (¬[] = []) ∧ (¬(h::t) = -h::¬t)
   
   [POLY_NORMALIZE]  Theorem
      
      |- ∀p. poly (normalize p) = poly p
   
   [POLY_ORDER]  Theorem
      
      |- ∀p a.
           poly p ≠ poly [] ⇒
           ∃!n.
             [-a; 1] poly_exp n poly_divides p ∧
             ¬([-a; 1] poly_exp SUC n poly_divides p)
   
   [POLY_ORDER_EXISTS]  Theorem
      
      |- ∀a d p.
           (LENGTH p = d) ∧ poly p ≠ poly [] ⇒
           ∃n.
             [-a; 1] poly_exp n poly_divides p ∧
             ¬([-a; 1] poly_exp SUC n poly_divides p)
   
   [POLY_PRIMES]  Theorem
      
      |- ∀a p q.
           [a; 1] poly_divides p * q ⇔ [a; 1] poly_divides p ∨ [a; 1] poly_divides q
   
   [POLY_PRIME_EQ_0]  Theorem
      
      |- ∀a. poly [a; 1] ≠ poly []
   
   [POLY_ROOTS_FINITE]  Theorem
      
      |- ∀p. poly p ≠ poly [] ⇔ ∃N i. ∀x. (poly p x = 0) ⇒ ∃n. n < N ∧ (x = i n)
   
   [POLY_ROOTS_FINITE_LEMMA]  Theorem
      
      |- ∀p. poly p ≠ poly [] ⇒ ∃N i. ∀x. (poly p x = 0) ⇒ ∃n. n < N ∧ (x = i n)
   
   [POLY_ROOTS_FINITE_SET]  Theorem
      
      |- ∀p. poly p ≠ poly [] ⇒ FINITE {x | poly p x = 0}
   
   [POLY_ROOTS_INDEX_LEMMA]  Theorem
      
      |- ∀n p.
           poly p ≠ poly [] ∧ (LENGTH p = n) ⇒
           ∃i. ∀x. (poly p x = 0) ⇒ ∃m. m ≤ n ∧ (x = i m)
   
   [POLY_ROOTS_INDEX_LENGTH]  Theorem
      
      |- ∀p. poly p ≠ poly [] ⇒ ∃i. ∀x. (poly p x = 0) ⇒ ∃n. n ≤ LENGTH p ∧ (x = i n)
   
   [POLY_SQUAREFREE_DECOMP]  Theorem
      
      |- ∀p q d e r s.
           poly (diff p) ≠ poly [] ∧ (poly p = poly (q * d)) ∧
           (poly (diff p) = poly (e * d)) ∧ (poly d = poly (r * p + s * diff p)) ⇒
           rsquarefree q ∧ ∀a. (poly q a = 0) ⇔ (poly p a = 0)
   
   [POLY_SQUAREFREE_DECOMP_ORDER]  Theorem
      
      |- ∀p q d e r s.
           poly (diff p) ≠ poly [] ∧ (poly p = poly (q * d)) ∧
           (poly (diff p) = poly (e * d)) ∧ (poly d = poly (r * p + s * diff p)) ⇒
           ∀a. poly_order a q = if poly_order a p = 0 then 0 else 1
   
   [POLY_ZERO]  Theorem
      
      |- ∀p. (poly p = poly []) ⇔ EVERY (λc. c = 0) p
   
   [POLY_ZERO_LEMMA]  Theorem
      
      |- ∀h t. (poly (h::t) = poly []) ⇒ (h = 0) ∧ (poly t = poly [])
   
   [RSQUAREFREE_DECOMP]  Theorem
      
      |- ∀p a.
           rsquarefree p ∧ (poly p a = 0) ⇒
           ∃q. (poly p = poly ([-a; 1] * q)) ∧ poly q a ≠ 0
   
   [RSQUAREFREE_ROOTS]  Theorem
      
      |- ∀p. rsquarefree p ⇔ ∀a. ¬((poly p a = 0) ∧ (poly (diff p) a = 0))
   
   
*)
end
