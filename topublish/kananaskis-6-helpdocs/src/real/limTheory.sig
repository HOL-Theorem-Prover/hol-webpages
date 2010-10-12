signature limTheory =
sig
  type thm = Thm.thm
  
  (*  Definitions  *)
    val contl : thm
    val differentiable : thm
    val diffl : thm
    val tends_real_real : thm
  
  (*  Theorems  *)
    val CONTL_LIM : thm
    val CONT_ADD : thm
    val CONT_ATTAINS : thm
    val CONT_ATTAINS2 : thm
    val CONT_ATTAINS_ALL : thm
    val CONT_BOUNDED : thm
    val CONT_COMPOSE : thm
    val CONT_CONST : thm
    val CONT_DIV : thm
    val CONT_HASSUP : thm
    val CONT_INJ_LEMMA : thm
    val CONT_INJ_LEMMA2 : thm
    val CONT_INJ_RANGE : thm
    val CONT_INV : thm
    val CONT_INVERSE : thm
    val CONT_MUL : thm
    val CONT_NEG : thm
    val CONT_SUB : thm
    val DIFF_ADD : thm
    val DIFF_CARAT : thm
    val DIFF_CHAIN : thm
    val DIFF_CMUL : thm
    val DIFF_CONST : thm
    val DIFF_CONT : thm
    val DIFF_DIV : thm
    val DIFF_INV : thm
    val DIFF_INVERSE : thm
    val DIFF_INVERSE_LT : thm
    val DIFF_INVERSE_OPEN : thm
    val DIFF_ISCONST : thm
    val DIFF_ISCONST_ALL : thm
    val DIFF_ISCONST_END : thm
    val DIFF_LCONST : thm
    val DIFF_LDEC : thm
    val DIFF_LINC : thm
    val DIFF_LMAX : thm
    val DIFF_LMIN : thm
    val DIFF_MUL : thm
    val DIFF_NEG : thm
    val DIFF_POW : thm
    val DIFF_SUB : thm
    val DIFF_SUM : thm
    val DIFF_UNIQ : thm
    val DIFF_X : thm
    val DIFF_XM1 : thm
    val INTERVAL_ABS : thm
    val INTERVAL_CLEMMA : thm
    val INTERVAL_LEMMA : thm
    val IVT : thm
    val IVT2 : thm
    val LIM : thm
    val LIM_ADD : thm
    val LIM_CONST : thm
    val LIM_DIV : thm
    val LIM_EQUAL : thm
    val LIM_INV : thm
    val LIM_MUL : thm
    val LIM_NEG : thm
    val LIM_NULL : thm
    val LIM_SUB : thm
    val LIM_TRANSFORM : thm
    val LIM_UNIQ : thm
    val LIM_X : thm
    val MVT : thm
    val MVT_LEMMA : thm
    val ROLLE : thm
  
  val lim_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [seq] Parent theory of "lim"
   
   [contl]  Definition
      
      |- ∀f x. f contl x ⇔ ((λh. f (x + h)) -> f x) 0
   
   [differentiable]  Definition
      
      |- ∀f x. f differentiable x ⇔ ∃l. (f diffl l) x
   
   [diffl]  Definition
      
      |- ∀f l x. (f diffl l) x ⇔ ((λh. (f (x + h) − f x) / h) -> l) 0
   
   [tends_real_real]  Definition
      
      |- ∀f l x0. (f -> l) x0 ⇔ (f tends l) (mtop mr1,tendsto (mr1,x0))
   
   [CONTL_LIM]  Theorem
      
      |- ∀f x. f contl x ⇔ (f -> f x) x
   
   [CONT_ADD]  Theorem
      
      |- ∀f g x. f contl x ∧ g contl x ⇒ (λx. f x + g x) contl x
   
   [CONT_ATTAINS]  Theorem
      
      |- ∀f a b.
           a ≤ b ∧ (∀x. a ≤ x ∧ x ≤ b ⇒ f contl x) ⇒
           ∃M. (∀x. a ≤ x ∧ x ≤ b ⇒ f x ≤ M) ∧ ∃x. a ≤ x ∧ x ≤ b ∧ (f x = M)
   
   [CONT_ATTAINS2]  Theorem
      
      |- ∀f a b.
           a ≤ b ∧ (∀x. a ≤ x ∧ x ≤ b ⇒ f contl x) ⇒
           ∃M. (∀x. a ≤ x ∧ x ≤ b ⇒ M ≤ f x) ∧ ∃x. a ≤ x ∧ x ≤ b ∧ (f x = M)
   
   [CONT_ATTAINS_ALL]  Theorem
      
      |- ∀f a b.
           a ≤ b ∧ (∀x. a ≤ x ∧ x ≤ b ⇒ f contl x) ⇒
           ∃L M.
             L ≤ M ∧ (∀y. L ≤ y ∧ y ≤ M ⇒ ∃x. a ≤ x ∧ x ≤ b ∧ (f x = y)) ∧
             ∀x. a ≤ x ∧ x ≤ b ⇒ L ≤ f x ∧ f x ≤ M
   
   [CONT_BOUNDED]  Theorem
      
      |- ∀f a b.
           a ≤ b ∧ (∀x. a ≤ x ∧ x ≤ b ⇒ f contl x) ⇒ ∃M. ∀x. a ≤ x ∧ x ≤ b ⇒ f x ≤ M
   
   [CONT_COMPOSE]  Theorem
      
      |- ∀f g x. f contl x ∧ g contl f x ⇒ (λx. g (f x)) contl x
   
   [CONT_CONST]  Theorem
      
      |- ∀k x. (λx. k) contl x
   
   [CONT_DIV]  Theorem
      
      |- ∀f g x. f contl x ∧ g contl x ∧ g x ≠ 0 ⇒ (λx. f x / g x) contl x
   
   [CONT_HASSUP]  Theorem
      
      |- ∀f a b.
           a ≤ b ∧ (∀x. a ≤ x ∧ x ≤ b ⇒ f contl x) ⇒
           ∃M.
             (∀x. a ≤ x ∧ x ≤ b ⇒ f x ≤ M) ∧ ∀N. N < M ⇒ ∃x. a ≤ x ∧ x ≤ b ∧ N < f x
   
   [CONT_INJ_LEMMA]  Theorem
      
      |- ∀f g x d.
           0 < d ∧ (∀z. abs (z − x) ≤ d ⇒ (g (f z) = z)) ∧
           (∀z. abs (z − x) ≤ d ⇒ f contl z) ⇒
           ¬∀z. abs (z − x) ≤ d ⇒ f z ≤ f x
   
   [CONT_INJ_LEMMA2]  Theorem
      
      |- ∀f g x d.
           0 < d ∧ (∀z. abs (z − x) ≤ d ⇒ (g (f z) = z)) ∧
           (∀z. abs (z − x) ≤ d ⇒ f contl z) ⇒
           ¬∀z. abs (z − x) ≤ d ⇒ f x ≤ f z
   
   [CONT_INJ_RANGE]  Theorem
      
      |- ∀f g x d.
           0 < d ∧ (∀z. abs (z − x) ≤ d ⇒ (g (f z) = z)) ∧
           (∀z. abs (z − x) ≤ d ⇒ f contl z) ⇒
           ∃e. 0 < e ∧ ∀y. abs (y − f x) ≤ e ⇒ ∃z. abs (z − x) ≤ d ∧ (f z = y)
   
   [CONT_INV]  Theorem
      
      |- ∀f x. f contl x ∧ f x ≠ 0 ⇒ (λx. inv (f x)) contl x
   
   [CONT_INVERSE]  Theorem
      
      |- ∀f g x d.
           0 < d ∧ (∀z. abs (z − x) ≤ d ⇒ (g (f z) = z)) ∧
           (∀z. abs (z − x) ≤ d ⇒ f contl z) ⇒
           g contl f x
   
   [CONT_MUL]  Theorem
      
      |- ∀f g x. f contl x ∧ g contl x ⇒ (λx. f x * g x) contl x
   
   [CONT_NEG]  Theorem
      
      |- ∀f x. f contl x ⇒ (λx. -f x) contl x
   
   [CONT_SUB]  Theorem
      
      |- ∀f g x. f contl x ∧ g contl x ⇒ (λx. f x − g x) contl x
   
   [DIFF_ADD]  Theorem
      
      |- ∀f g l m x.
           (f diffl l) x ∧ (g diffl m) x ⇒ ((λx. f x + g x) diffl (l + m)) x
   
   [DIFF_CARAT]  Theorem
      
      |- ∀f l x.
           (f diffl l) x ⇔
           ∃g. (∀z. f z − f x = g z * (z − x)) ∧ g contl x ∧ (g x = l)
   
   [DIFF_CHAIN]  Theorem
      
      |- ∀f g l m x.
           (f diffl l) (g x) ∧ (g diffl m) x ⇒ ((λx. f (g x)) diffl (l * m)) x
   
   [DIFF_CMUL]  Theorem
      
      |- ∀f c l x. (f diffl l) x ⇒ ((λx. c * f x) diffl (c * l)) x
   
   [DIFF_CONST]  Theorem
      
      |- ∀k x. ((λx. k) diffl 0) x
   
   [DIFF_CONT]  Theorem
      
      |- ∀f l x. (f diffl l) x ⇒ f contl x
   
   [DIFF_DIV]  Theorem
      
      |- ∀f g l m x.
           (f diffl l) x ∧ (g diffl m) x ∧ g x ≠ 0 ⇒
           ((λx. f x / g x) diffl ((l * g x − m * f x) / g x pow 2)) x
   
   [DIFF_INV]  Theorem
      
      |- ∀f l x. (f diffl l) x ∧ f x ≠ 0 ⇒ ((λx. inv (f x)) diffl -(l / f x pow 2)) x
   
   [DIFF_INVERSE]  Theorem
      
      |- ∀f g l x d.
           0 < d ∧ (∀z. abs (z − x) ≤ d ⇒ (g (f z) = z)) ∧
           (∀z. abs (z − x) ≤ d ⇒ f contl z) ∧ (f diffl l) x ∧ l ≠ 0 ⇒
           (g diffl inv l) (f x)
   
   [DIFF_INVERSE_LT]  Theorem
      
      |- ∀f g l x d.
           0 < d ∧ (∀z. abs (z − x) < d ⇒ (g (f z) = z)) ∧
           (∀z. abs (z − x) < d ⇒ f contl z) ∧ (f diffl l) x ∧ l ≠ 0 ⇒
           (g diffl inv l) (f x)
   
   [DIFF_INVERSE_OPEN]  Theorem
      
      |- ∀f g l a x b.
           a < x ∧ x < b ∧ (∀z. a < z ∧ z < b ⇒ (g (f z) = z) ∧ f contl z) ∧
           (f diffl l) x ∧ l ≠ 0 ⇒
           (g diffl inv l) (f x)
   
   [DIFF_ISCONST]  Theorem
      
      |- ∀f a b.
           a < b ∧ (∀x. a ≤ x ∧ x ≤ b ⇒ f contl x) ∧
           (∀x. a < x ∧ x < b ⇒ (f diffl 0) x) ⇒
           ∀x. a ≤ x ∧ x ≤ b ⇒ (f x = f a)
   
   [DIFF_ISCONST_ALL]  Theorem
      
      |- ∀f. (∀x. (f diffl 0) x) ⇒ ∀x y. f x = f y
   
   [DIFF_ISCONST_END]  Theorem
      
      |- ∀f a b.
           a < b ∧ (∀x. a ≤ x ∧ x ≤ b ⇒ f contl x) ∧
           (∀x. a < x ∧ x < b ⇒ (f diffl 0) x) ⇒
           (f b = f a)
   
   [DIFF_LCONST]  Theorem
      
      |- ∀f x l.
           (f diffl l) x ∧ (∃d. 0 < d ∧ ∀y. abs (x − y) < d ⇒ (f y = f x)) ⇒ (l = 0)
   
   [DIFF_LDEC]  Theorem
      
      |- ∀f x l.
           (f diffl l) x ∧ l < 0 ⇒ ∃d. 0 < d ∧ ∀h. 0 < h ∧ h < d ⇒ f x < f (x − h)
   
   [DIFF_LINC]  Theorem
      
      |- ∀f x l.
           (f diffl l) x ∧ 0 < l ⇒ ∃d. 0 < d ∧ ∀h. 0 < h ∧ h < d ⇒ f x < f (x + h)
   
   [DIFF_LMAX]  Theorem
      
      |- ∀f x l.
           (f diffl l) x ∧ (∃d. 0 < d ∧ ∀y. abs (x − y) < d ⇒ f y ≤ f x) ⇒ (l = 0)
   
   [DIFF_LMIN]  Theorem
      
      |- ∀f x l.
           (f diffl l) x ∧ (∃d. 0 < d ∧ ∀y. abs (x − y) < d ⇒ f x ≤ f y) ⇒ (l = 0)
   
   [DIFF_MUL]  Theorem
      
      |- ∀f g l m x.
           (f diffl l) x ∧ (g diffl m) x ⇒
           ((λx. f x * g x) diffl (l * g x + m * f x)) x
   
   [DIFF_NEG]  Theorem
      
      |- ∀f l x. (f diffl l) x ⇒ ((λx. -f x) diffl -l) x
   
   [DIFF_POW]  Theorem
      
      |- ∀n x. ((λx. x pow n) diffl (&n * x pow (n − 1))) x
   
   [DIFF_SUB]  Theorem
      
      |- ∀f g l m x.
           (f diffl l) x ∧ (g diffl m) x ⇒ ((λx. f x − g x) diffl (l − m)) x
   
   [DIFF_SUM]  Theorem
      
      |- ∀f f' m n x.
           (∀r. m ≤ r ∧ r < m + n ⇒ ((λx. f r x) diffl f' r x) x) ⇒
           ((λx. sum (m,n) (λn. f n x)) diffl sum (m,n) (λr. f' r x)) x
   
   [DIFF_UNIQ]  Theorem
      
      |- ∀f l m x. (f diffl l) x ∧ (f diffl m) x ⇒ (l = m)
   
   [DIFF_X]  Theorem
      
      |- ∀x. ((λx. x) diffl 1) x
   
   [DIFF_XM1]  Theorem
      
      |- ∀x. x ≠ 0 ⇒ ((λx. inv x) diffl -(inv x pow 2)) x
   
   [INTERVAL_ABS]  Theorem
      
      |- ∀x z d. x − d ≤ z ∧ z ≤ x + d ⇔ abs (z − x) ≤ d
   
   [INTERVAL_CLEMMA]  Theorem
      
      |- ∀a b x. a < x ∧ x < b ⇒ ∃d. 0 < d ∧ ∀y. abs (y − x) ≤ d ⇒ a < y ∧ y < b
   
   [INTERVAL_LEMMA]  Theorem
      
      |- ∀a b x. a < x ∧ x < b ⇒ ∃d. 0 < d ∧ ∀y. abs (x − y) < d ⇒ a ≤ y ∧ y ≤ b
   
   [IVT]  Theorem
      
      |- ∀f a b y.
           a ≤ b ∧ (f a ≤ y ∧ y ≤ f b) ∧ (∀x. a ≤ x ∧ x ≤ b ⇒ f contl x) ⇒
           ∃x. a ≤ x ∧ x ≤ b ∧ (f x = y)
   
   [IVT2]  Theorem
      
      |- ∀f a b y.
           a ≤ b ∧ (f b ≤ y ∧ y ≤ f a) ∧ (∀x. a ≤ x ∧ x ≤ b ⇒ f contl x) ⇒
           ∃x. a ≤ x ∧ x ≤ b ∧ (f x = y)
   
   [LIM]  Theorem
      
      |- ∀f y0 x0.
           (f -> y0) x0 ⇔
           ∀e.
             0 < e ⇒
             ∃d. 0 < d ∧ ∀x. 0 < abs (x − x0) ∧ abs (x − x0) < d ⇒ abs (f x − y0) < e
   
   [LIM_ADD]  Theorem
      
      |- ∀f g l m x. (f -> l) x ∧ (g -> m) x ⇒ ((λx. f x + g x) -> l + m) x
   
   [LIM_CONST]  Theorem
      
      |- ∀k x. ((λx. k) -> k) x
   
   [LIM_DIV]  Theorem
      
      |- ∀f g l m x. (f -> l) x ∧ (g -> m) x ∧ m ≠ 0 ⇒ ((λx. f x / g x) -> l / m) x
   
   [LIM_EQUAL]  Theorem
      
      |- ∀f g l x0. (∀x. x ≠ x0 ⇒ (f x = g x)) ⇒ ((f -> l) x0 ⇔ (g -> l) x0)
   
   [LIM_INV]  Theorem
      
      |- ∀f l x. (f -> l) x ∧ l ≠ 0 ⇒ ((λx. inv (f x)) -> inv l) x
   
   [LIM_MUL]  Theorem
      
      |- ∀f g l m x. (f -> l) x ∧ (g -> m) x ⇒ ((λx. f x * g x) -> l * m) x
   
   [LIM_NEG]  Theorem
      
      |- ∀f l x. (f -> l) x ⇔ ((λx. -f x) -> -l) x
   
   [LIM_NULL]  Theorem
      
      |- ∀f l x. (f -> l) x ⇔ ((λx. f x − l) -> 0) x
   
   [LIM_SUB]  Theorem
      
      |- ∀f g l m x. (f -> l) x ∧ (g -> m) x ⇒ ((λx. f x − g x) -> l − m) x
   
   [LIM_TRANSFORM]  Theorem
      
      |- ∀f g x0 l. ((λx. f x − g x) -> 0) x0 ∧ (g -> l) x0 ⇒ (f -> l) x0
   
   [LIM_UNIQ]  Theorem
      
      |- ∀f l m x. (f -> l) x ∧ (f -> m) x ⇒ (l = m)
   
   [LIM_X]  Theorem
      
      |- ∀x0. ((λx. x) -> x0) x0
   
   [MVT]  Theorem
      
      |- ∀f a b.
           a < b ∧ (∀x. a ≤ x ∧ x ≤ b ⇒ f contl x) ∧
           (∀x. a < x ∧ x < b ⇒ f differentiable x) ⇒
           ∃l z. a < z ∧ z < b ∧ (f diffl l) z ∧ (f b − f a = (b − a) * l)
   
   [MVT_LEMMA]  Theorem
      
      |- ∀f a b.
           (λx. f x − (f b − f a) / (b − a) * x) a =
           (λx. f x − (f b − f a) / (b − a) * x) b
   
   [ROLLE]  Theorem
      
      |- ∀f a b.
           a < b ∧ (f a = f b) ∧ (∀x. a ≤ x ∧ x ≤ b ⇒ f contl x) ∧
           (∀x. a < x ∧ x < b ⇒ f differentiable x) ⇒
           ∃z. a < z ∧ z < b ∧ (f diffl 0) z
   
   
*)
end
