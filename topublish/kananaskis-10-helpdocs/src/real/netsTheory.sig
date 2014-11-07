signature netsTheory =
sig
  type thm = Thm.thm

  (*  Definitions  *)
    val bounded : thm
    val dorder : thm
    val tends : thm
    val tendsto : thm

  (*  Theorems  *)
    val DORDER_LEMMA : thm
    val DORDER_NGE : thm
    val DORDER_TENDSTO : thm
    val LIM_TENDS : thm
    val LIM_TENDS2 : thm
    val MR1_BOUNDED : thm
    val MTOP_TENDS : thm
    val MTOP_TENDS_UNIQ : thm
    val NET_ABS : thm
    val NET_ADD : thm
    val NET_CONV_BOUNDED : thm
    val NET_CONV_IBOUNDED : thm
    val NET_CONV_NZ : thm
    val NET_DIV : thm
    val NET_INV : thm
    val NET_LE : thm
    val NET_MUL : thm
    val NET_NEG : thm
    val NET_NULL : thm
    val NET_NULL_ADD : thm
    val NET_NULL_CMUL : thm
    val NET_NULL_MUL : thm
    val NET_SUB : thm
    val SEQ_TENDS : thm

  val nets_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [topology] Parent theory of "nets"

   [bounded]  Definition

      |- ∀m g f.
           bounded (m,g) f ⇔ ∃k x N. g N N ∧ ∀n. g n N ⇒ dist m (f n,x) < k

   [dorder]  Definition

      |- ∀g.
           dorder g ⇔
           ∀x y. g x x ∧ g y y ⇒ ∃z. g z z ∧ ∀w. g w z ⇒ g w x ∧ g w y

   [tends]  Definition

      |- ∀s l top g.
           (s tends l) (top,g) ⇔
           ∀N. neigh top (N,l) ⇒ ∃n. g n n ∧ ∀m. g m n ⇒ N (s m)

   [tendsto]  Definition

      |- ∀m x y z.
           tendsto (m,x) y z ⇔
           0 < dist m (x,y) ∧ dist m (x,y) ≤ dist m (x,z)

   [DORDER_LEMMA]  Theorem

      |- ∀g.
           dorder g ⇒
           ∀P Q.
             (∃n. g n n ∧ ∀m. g m n ⇒ P m) ∧
             (∃n. g n n ∧ ∀m. g m n ⇒ Q m) ⇒
             ∃n. g n n ∧ ∀m. g m n ⇒ P m ∧ Q m

   [DORDER_NGE]  Theorem

      |- dorder $>=

   [DORDER_TENDSTO]  Theorem

      |- ∀m x. dorder (tendsto (m,x))

   [LIM_TENDS]  Theorem

      |- ∀m1 m2 f x0 y0.
           limpt (mtop m1) x0 𝕌(:α) ⇒
           ((f tends y0) (mtop m2,tendsto (m1,x0)) ⇔
            ∀e.
              0 < e ⇒
              ∃d.
                0 < d ∧
                ∀x.
                  0 < dist m1 (x,x0) ∧ dist m1 (x,x0) ≤ d ⇒
                  dist m2 (f x,y0) < e)

   [LIM_TENDS2]  Theorem

      |- ∀m1 m2 f x0 y0.
           limpt (mtop m1) x0 𝕌(:α) ⇒
           ((f tends y0) (mtop m2,tendsto (m1,x0)) ⇔
            ∀e.
              0 < e ⇒
              ∃d.
                0 < d ∧
                ∀x.
                  0 < dist m1 (x,x0) ∧ dist m1 (x,x0) < d ⇒
                  dist m2 (f x,y0) < e)

   [MR1_BOUNDED]  Theorem

      |- ∀g f. bounded (mr1,g) f ⇔ ∃k N. g N N ∧ ∀n. g n N ⇒ abs (f n) < k

   [MTOP_TENDS]  Theorem

      |- ∀d g x x0.
           (x tends x0) (mtop d,g) ⇔
           ∀e. 0 < e ⇒ ∃n. g n n ∧ ∀m. g m n ⇒ dist d (x m,x0) < e

   [MTOP_TENDS_UNIQ]  Theorem

      |- ∀g d.
           dorder g ⇒
           (x tends x0) (mtop d,g) ∧ (x tends x1) (mtop d,g) ⇒
           (x0 = x1)

   [NET_ABS]  Theorem

      |- ∀g x x0.
           (x tends x0) (mtop mr1,g) ⇒
           ((λn. abs (x n)) tends abs x0) (mtop mr1,g)

   [NET_ADD]  Theorem

      |- ∀g.
           dorder g ⇒
           ∀x x0 y y0.
             (x tends x0) (mtop mr1,g) ∧ (y tends y0) (mtop mr1,g) ⇒
             ((λn. x n + y n) tends (x0 + y0)) (mtop mr1,g)

   [NET_CONV_BOUNDED]  Theorem

      |- ∀g x x0. (x tends x0) (mtop mr1,g) ⇒ bounded (mr1,g) x

   [NET_CONV_IBOUNDED]  Theorem

      |- ∀g x x0.
           (x tends x0) (mtop mr1,g) ∧ x0 ≠ 0 ⇒
           bounded (mr1,g) (λn. inv (x n))

   [NET_CONV_NZ]  Theorem

      |- ∀g x x0.
           (x tends x0) (mtop mr1,g) ∧ x0 ≠ 0 ⇒
           ∃N. g N N ∧ ∀n. g n N ⇒ x n ≠ 0

   [NET_DIV]  Theorem

      |- ∀g.
           dorder g ⇒
           ∀x x0 y y0.
             (x tends x0) (mtop mr1,g) ∧ (y tends y0) (mtop mr1,g) ∧
             y0 ≠ 0 ⇒
             ((λn. x n / y n) tends (x0 / y0)) (mtop mr1,g)

   [NET_INV]  Theorem

      |- ∀g.
           dorder g ⇒
           ∀x x0.
             (x tends x0) (mtop mr1,g) ∧ x0 ≠ 0 ⇒
             ((λn. inv (x n)) tends inv x0) (mtop mr1,g)

   [NET_LE]  Theorem

      |- ∀g.
           dorder g ⇒
           ∀x x0 y y0.
             (x tends x0) (mtop mr1,g) ∧ (y tends y0) (mtop mr1,g) ∧
             (∃N. g N N ∧ ∀n. g n N ⇒ x n ≤ y n) ⇒
             x0 ≤ y0

   [NET_MUL]  Theorem

      |- ∀g.
           dorder g ⇒
           ∀x y x0 y0.
             (x tends x0) (mtop mr1,g) ∧ (y tends y0) (mtop mr1,g) ⇒
             ((λn. x n * y n) tends (x0 * y0)) (mtop mr1,g)

   [NET_NEG]  Theorem

      |- ∀g.
           dorder g ⇒
           ∀x x0.
             (x tends x0) (mtop mr1,g) ⇔
             ((λn. -x n) tends -x0) (mtop mr1,g)

   [NET_NULL]  Theorem

      |- ∀g x x0.
           (x tends x0) (mtop mr1,g) ⇔
           ((λn. x n − x0) tends 0) (mtop mr1,g)

   [NET_NULL_ADD]  Theorem

      |- ∀g.
           dorder g ⇒
           ∀x y.
             (x tends 0) (mtop mr1,g) ∧ (y tends 0) (mtop mr1,g) ⇒
             ((λn. x n + y n) tends 0) (mtop mr1,g)

   [NET_NULL_CMUL]  Theorem

      |- ∀g k x.
           (x tends 0) (mtop mr1,g) ⇒ ((λn. k * x n) tends 0) (mtop mr1,g)

   [NET_NULL_MUL]  Theorem

      |- ∀g.
           dorder g ⇒
           ∀x y.
             bounded (mr1,g) x ∧ (y tends 0) (mtop mr1,g) ⇒
             ((λn. x n * y n) tends 0) (mtop mr1,g)

   [NET_SUB]  Theorem

      |- ∀g.
           dorder g ⇒
           ∀x x0 y y0.
             (x tends x0) (mtop mr1,g) ∧ (y tends y0) (mtop mr1,g) ⇒
             ((λn. x n − y n) tends (x0 − y0)) (mtop mr1,g)

   [SEQ_TENDS]  Theorem

      |- ∀d x x0.
           (x tends x0) (mtop d,$>=) ⇔
           ∀e. 0 < e ⇒ ∃N. ∀n. n ≥ N ⇒ dist d (x n,x0) < e


*)
end
