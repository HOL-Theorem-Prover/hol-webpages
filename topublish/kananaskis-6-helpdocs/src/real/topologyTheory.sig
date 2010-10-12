signature topologyTheory =
sig
  type thm = Thm.thm
  
  (*  Definitions  *)
    val ball : thm
    val closed : thm
    val ismet : thm
    val istopology : thm
    val limpt : thm
    val metric_TY_DEF : thm
    val metric_tybij : thm
    val mr1 : thm
    val mtop : thm
    val neigh : thm
    val re_Union : thm
    val re_compl : thm
    val re_intersect : thm
    val re_null : thm
    val re_subset : thm
    val re_union : thm
    val re_universe : thm
    val topology_TY_DEF : thm
    val topology_tybij : thm
  
  (*  Theorems  *)
    val BALL_NEIGH : thm
    val BALL_OPEN : thm
    val CLOSED_LIMPT : thm
    val COMPL_MEM : thm
    val ISMET_R1 : thm
    val METRIC_ISMET : thm
    val METRIC_NZ : thm
    val METRIC_POS : thm
    val METRIC_SAME : thm
    val METRIC_SYM : thm
    val METRIC_TRIANGLE : thm
    val METRIC_ZERO : thm
    val MR1_ADD : thm
    val MR1_ADD_LT : thm
    val MR1_ADD_POS : thm
    val MR1_BETWEEN1 : thm
    val MR1_DEF : thm
    val MR1_LIMPT : thm
    val MR1_SUB : thm
    val MR1_SUB_LE : thm
    val MR1_SUB_LT : thm
    val MTOP_LIMPT : thm
    val MTOP_OPEN : thm
    val OPEN_NEIGH : thm
    val OPEN_OWN_NEIGH : thm
    val OPEN_SUBOPEN : thm
    val OPEN_UNOPEN : thm
    val SUBSET_ANTISYM : thm
    val SUBSET_REFL : thm
    val SUBSET_TRANS : thm
    val TOPOLOGY : thm
    val TOPOLOGY_UNION : thm
    val mtop_istopology : thm
  
  val topology_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [real] Parent theory of "topology"
   
   [ball]  Definition
      
      |- ∀m x e. B m (x,e) = (λy. dist m (x,y) < e)
   
   [closed]  Definition
      
      |- ∀L S'. closed L S' ⇔ open L (re_compl S')
   
   [ismet]  Definition
      
      |- ∀m.
           ismet m ⇔
           (∀x y. (m (x,y) = 0) ⇔ (x = y)) ∧ ∀x y z. m (y,z) ≤ m (x,y) + m (x,z)
   
   [istopology]  Definition
      
      |- ∀L.
           istopology L ⇔
           L re_null ∧ L re_universe ∧ (∀a b. L a ∧ L b ⇒ L (a re_intersect b)) ∧
           ∀P. P re_subset L ⇒ L (re_Union P)
   
   [limpt]  Definition
      
      |- ∀top x S'. limpt top x S' ⇔ ∀N. neigh top (N,x) ⇒ ∃y. x ≠ y ∧ S' y ∧ N y
   
   [metric_TY_DEF]  Definition
      
      |- ∃rep. TYPE_DEFINITION ismet rep
   
   [metric_tybij]  Definition
      
      |- (∀a. metric (dist a) = a) ∧ ∀r. ismet r ⇔ (dist (metric r) = r)
   
   [mr1]  Definition
      
      |- mr1 = metric (λ(x,y). abs (y − x))
   
   [mtop]  Definition
      
      |- ∀m.
           mtop m =
           topology (λS'. ∀x. S' x ⇒ ∃e. 0 < e ∧ ∀y. dist m (x,y) < e ⇒ S' y)
   
   [neigh]  Definition
      
      |- ∀top N x. neigh top (N,x) ⇔ ∃P. open top P ∧ P re_subset N ∧ P x
   
   [re_Union]  Definition
      
      |- ∀P. re_Union P = (λx. ∃s. P s ∧ s x)
   
   [re_compl]  Definition
      
      |- ∀P. re_compl P = (λx. ¬P x)
   
   [re_intersect]  Definition
      
      |- ∀P Q. P re_intersect Q = (λx. P x ∧ Q x)
   
   [re_null]  Definition
      
      |- re_null = (λx. F)
   
   [re_subset]  Definition
      
      |- ∀P Q. P re_subset Q ⇔ ∀x. P x ⇒ Q x
   
   [re_union]  Definition
      
      |- ∀P Q. P re_union Q = (λx. P x ∨ Q x)
   
   [re_universe]  Definition
      
      |- re_universe = (λx. T)
   
   [topology_TY_DEF]  Definition
      
      |- ∃rep. TYPE_DEFINITION istopology rep
   
   [topology_tybij]  Definition
      
      |- (∀a. topology (open a) = a) ∧ ∀r. istopology r ⇔ (open (topology r) = r)
   
   [BALL_NEIGH]  Theorem
      
      |- ∀m x e. 0 < e ⇒ neigh (mtop m) (B m (x,e),x)
   
   [BALL_OPEN]  Theorem
      
      |- ∀m x e. 0 < e ⇒ open (mtop m) (B m (x,e))
   
   [CLOSED_LIMPT]  Theorem
      
      |- ∀top S'. closed top S' ⇔ ∀x. limpt top x S' ⇒ S' x
   
   [COMPL_MEM]  Theorem
      
      |- ∀P x. P x ⇔ ¬re_compl P x
   
   [ISMET_R1]  Theorem
      
      |- ismet (λ(x,y). abs (y − x))
   
   [METRIC_ISMET]  Theorem
      
      |- ∀m. ismet (dist m)
   
   [METRIC_NZ]  Theorem
      
      |- ∀m x y. x ≠ y ⇒ 0 < dist m (x,y)
   
   [METRIC_POS]  Theorem
      
      |- ∀m x y. 0 ≤ dist m (x,y)
   
   [METRIC_SAME]  Theorem
      
      |- ∀m x. dist m (x,x) = 0
   
   [METRIC_SYM]  Theorem
      
      |- ∀m x y. dist m (x,y) = dist m (y,x)
   
   [METRIC_TRIANGLE]  Theorem
      
      |- ∀m x y z. dist m (x,z) ≤ dist m (x,y) + dist m (y,z)
   
   [METRIC_ZERO]  Theorem
      
      |- ∀m x y. (dist m (x,y) = 0) ⇔ (x = y)
   
   [MR1_ADD]  Theorem
      
      |- ∀x d. dist mr1 (x,x + d) = abs d
   
   [MR1_ADD_LT]  Theorem
      
      |- ∀x d. 0 < d ⇒ (dist mr1 (x,x + d) = d)
   
   [MR1_ADD_POS]  Theorem
      
      |- ∀x d. 0 ≤ d ⇒ (dist mr1 (x,x + d) = d)
   
   [MR1_BETWEEN1]  Theorem
      
      |- ∀x y z. x < z ∧ dist mr1 (x,y) < z − x ⇒ y < z
   
   [MR1_DEF]  Theorem
      
      |- ∀x y. dist mr1 (x,y) = abs (y − x)
   
   [MR1_LIMPT]  Theorem
      
      |- ∀x. limpt (mtop mr1) x re_universe
   
   [MR1_SUB]  Theorem
      
      |- ∀x d. dist mr1 (x,x − d) = abs d
   
   [MR1_SUB_LE]  Theorem
      
      |- ∀x d. 0 ≤ d ⇒ (dist mr1 (x,x − d) = d)
   
   [MR1_SUB_LT]  Theorem
      
      |- ∀x d. 0 < d ⇒ (dist mr1 (x,x − d) = d)
   
   [MTOP_LIMPT]  Theorem
      
      |- ∀m x S'.
           limpt (mtop m) x S' ⇔ ∀e. 0 < e ⇒ ∃y. x ≠ y ∧ S' y ∧ dist m (x,y) < e
   
   [MTOP_OPEN]  Theorem
      
      |- ∀S' m. open (mtop m) S' ⇔ ∀x. S' x ⇒ ∃e. 0 < e ∧ ∀y. dist m (x,y) < e ⇒ S' y
   
   [OPEN_NEIGH]  Theorem
      
      |- ∀S' top. open top S' ⇔ ∀x. S' x ⇒ ∃N. neigh top (N,x) ∧ N re_subset S'
   
   [OPEN_OWN_NEIGH]  Theorem
      
      |- ∀S' top x. open top S' ∧ S' x ⇒ neigh top (S',x)
   
   [OPEN_SUBOPEN]  Theorem
      
      |- ∀S' top. open top S' ⇔ ∀x. S' x ⇒ ∃P. P x ∧ open top P ∧ P re_subset S'
   
   [OPEN_UNOPEN]  Theorem
      
      |- ∀S' top. open top S' ⇔ (re_Union (λP. open top P ∧ P re_subset S') = S')
   
   [SUBSET_ANTISYM]  Theorem
      
      |- ∀P Q. P re_subset Q ∧ Q re_subset P ⇔ (P = Q)
   
   [SUBSET_REFL]  Theorem
      
      |- ∀P. P re_subset P
   
   [SUBSET_TRANS]  Theorem
      
      |- ∀P Q R. P re_subset Q ∧ Q re_subset R ⇒ P re_subset R
   
   [TOPOLOGY]  Theorem
      
      |- ∀L.
           open L re_null ∧ open L re_universe ∧
           (∀x y. open L x ∧ open L y ⇒ open L (x re_intersect y)) ∧
           ∀P. P re_subset open L ⇒ open L (re_Union P)
   
   [TOPOLOGY_UNION]  Theorem
      
      |- ∀L P. P re_subset open L ⇒ open L (re_Union P)
   
   [mtop_istopology]  Theorem
      
      |- ∀m. istopology (λS'. ∀x. S' x ⇒ ∃e. 0 < e ∧ ∀y. dist m (x,y) < e ⇒ S' y)
   
   
*)
end
