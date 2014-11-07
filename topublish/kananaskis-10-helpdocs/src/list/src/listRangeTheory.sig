signature listRangeTheory =
sig
  type thm = Thm.thm

  (*  Definitions  *)
    val listRangeINC_def : thm
    val listRangeLHI_def : thm

  (*  Theorems  *)
    val EL_listRangeLHI : thm
    val LENGTH_listRangeLHI : thm
    val MEM_listRangeINC : thm
    val MEM_listRangeLHI : thm
    val listRangeINC_CONS : thm
    val listRangeINC_EMPTY : thm
    val listRangeINC_SING : thm
    val listRangeLHI_ALL_DISTINCT : thm
    val listRangeLHI_CONS : thm
    val listRangeLHI_EMPTY : thm
    val listRangeLHI_EQ : thm

  val listRange_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [list] Parent theory of "listRange"

   [listRangeINC_def]  Definition

      |- ∀m n. [m .. n] = GENLIST (λi. m + i) (n + 1 − m)

   [listRangeLHI_def]  Definition

      |- ∀m n. [m ..< n] = GENLIST (λi. m + i) (n − m)

   [EL_listRangeLHI]  Theorem

      |- lo + i < hi ⇒ (EL i [lo ..< hi] = lo + i)

   [LENGTH_listRangeLHI]  Theorem

      |- LENGTH [lo ..< hi] = hi − lo

   [MEM_listRangeINC]  Theorem

      |- MEM x [m .. n] ⇔ m ≤ x ∧ x ≤ n

   [MEM_listRangeLHI]  Theorem

      |- MEM x [m ..< n] ⇔ m ≤ x ∧ x < n

   [listRangeINC_CONS]  Theorem

      |- m ≤ n ⇒ ([m .. n] = m::[m + 1 .. n])

   [listRangeINC_EMPTY]  Theorem

      |- n < m ⇒ ([m .. n] = [])

   [listRangeINC_SING]  Theorem

      |- [m .. m] = [m]

   [listRangeLHI_ALL_DISTINCT]  Theorem

      |- ALL_DISTINCT [lo ..< hi]

   [listRangeLHI_CONS]  Theorem

      |- lo < hi ⇒ ([lo ..< hi] = lo::[lo + 1 ..< hi])

   [listRangeLHI_EMPTY]  Theorem

      |- hi ≤ lo ⇒ ([lo ..< hi] = [])

   [listRangeLHI_EQ]  Theorem

      |- [m ..< m] = []


*)
end
