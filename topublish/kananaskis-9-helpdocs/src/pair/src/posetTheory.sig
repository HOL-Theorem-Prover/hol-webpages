signature posetTheory =
sig
  type thm = Thm.thm

  (*  Definitions  *)
    val bottom_def : thm
    val carrier_def : thm
    val chain_def : thm
    val complete_def : thm
    val continuous_def : thm
    val down_continuous_def : thm
    val function_def : thm
    val gfp_def : thm
    val glb_def : thm
    val lfp_def : thm
    val lub_def : thm
    val monotonic_def : thm
    val pointwise_lift_def : thm
    val poset_def : thm
    val relation_def : thm
    val top_def : thm
    val up_continuous_def : thm

  (*  Theorems  *)
    val complete_bottom : thm
    val complete_down : thm
    val complete_pointwise : thm
    val complete_top : thm
    val complete_up : thm
    val gfp_unique : thm
    val glb_pred : thm
    val knaster_tarski : thm
    val knaster_tarski_gfp : thm
    val knaster_tarski_lfp : thm
    val lfp_unique : thm
    val lub_pred : thm
    val poset_antisym : thm
    val poset_nonempty : thm
    val poset_refl : thm
    val poset_trans : thm

  val poset_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [pair] Parent theory of "poset"

   [bottom_def]  Definition

      |- ∀s r x. bottom (s,r) x ⇔ s x ∧ ∀y. s y ⇒ r x y

   [carrier_def]  Definition

      |- ∀s r. carrier (s,r) = s

   [chain_def]  Definition

      |- ∀s r c.
           chain (s,r) c ⇔ ∀x y. s x ∧ s y ∧ c x ∧ c y ⇒ r x y ∨ r y x

   [complete_def]  Definition

      |- ∀p. complete p ⇔ ∀c. (∃x. lub p c x) ∧ ∃x. glb p c x

   [continuous_def]  Definition

      |- ∀p f. continuous p f ⇔ up_continuous p f ∧ down_continuous p f

   [down_continuous_def]  Definition

      |- ∀s r f.
           down_continuous (s,r) f ⇔
           ∀c x.
             chain (s,r) c ∧ glb (s,r) c x ⇒
             glb (s,r) (λy. ∃z. (s z ∧ c z) ∧ (y = f z)) (f x)

   [function_def]  Definition

      |- ∀a b f. function a b f ⇔ ∀x. a x ⇒ b (f x)

   [gfp_def]  Definition

      |- ∀s r f x.
           gfp (s,r) f x ⇔ s x ∧ (f x = x) ∧ ∀y. s y ∧ r y (f y) ⇒ r y x

   [glb_def]  Definition

      |- ∀s r p x.
           glb (s,r) p x ⇔
           s x ∧ (∀y. s y ∧ p y ⇒ r x y) ∧
           ∀z. s z ∧ (∀y. s y ∧ p y ⇒ r z y) ⇒ r z x

   [lfp_def]  Definition

      |- ∀s r f x.
           lfp (s,r) f x ⇔ s x ∧ (f x = x) ∧ ∀y. s y ∧ r (f y) y ⇒ r x y

   [lub_def]  Definition

      |- ∀s r p x.
           lub (s,r) p x ⇔
           s x ∧ (∀y. s y ∧ p y ⇒ r y x) ∧
           ∀z. s z ∧ (∀y. s y ∧ p y ⇒ r y z) ⇒ r x z

   [monotonic_def]  Definition

      |- ∀s r f.
           monotonic (s,r) f ⇔ ∀x y. s x ∧ s y ∧ r x y ⇒ r (f x) (f y)

   [pointwise_lift_def]  Definition

      |- ∀t s r.
           pointwise_lift t (s,r) =
           (function t s,(λf g. ∀x. t x ⇒ r (f x) (g x)))

   [poset_def]  Definition

      |- ∀s r.
           poset (s,r) ⇔
           (∃x. s x) ∧ (∀x. s x ⇒ r x x) ∧
           (∀x y. s x ∧ s y ∧ r x y ∧ r y x ⇒ (x = y)) ∧
           ∀x y z. s x ∧ s y ∧ s z ∧ r x y ∧ r y z ⇒ r x z

   [relation_def]  Definition

      |- ∀s r. relation (s,r) = r

   [top_def]  Definition

      |- ∀s r x. top (s,r) x ⇔ s x ∧ ∀y. s y ⇒ r y x

   [up_continuous_def]  Definition

      |- ∀s r f.
           up_continuous (s,r) f ⇔
           ∀c x.
             chain (s,r) c ∧ lub (s,r) c x ⇒
             lub (s,r) (λy. ∃z. (s z ∧ c z) ∧ (y = f z)) (f x)

   [complete_bottom]  Theorem

      |- ∀p. poset p ∧ complete p ⇒ ∃x. bottom p x

   [complete_down]  Theorem

      |- ∀p c. complete p ⇒ ∃x. glb p c x

   [complete_pointwise]  Theorem

      |- ∀p t. complete p ⇒ complete (pointwise_lift t p)

   [complete_top]  Theorem

      |- ∀p. poset p ∧ complete p ⇒ ∃x. top p x

   [complete_up]  Theorem

      |- ∀p c. complete p ⇒ ∃x. lub p c x

   [gfp_unique]  Theorem

      |- ∀p f x x'. poset p ∧ gfp p f x ∧ gfp p f x' ⇒ (x = x')

   [glb_pred]  Theorem

      |- ∀s r p x. glb (s,r) (λj. s j ∧ p j) x ⇔ glb (s,r) p x

   [knaster_tarski]  Theorem

      |- ∀p f.
           poset p ∧ complete p ∧ function (carrier p) (carrier p) f ∧
           monotonic p f ⇒
           (∃x. lfp p f x) ∧ ∃x. gfp p f x

   [knaster_tarski_gfp]  Theorem

      |- ∀p f.
           poset p ∧ complete p ∧ function (carrier p) (carrier p) f ∧
           monotonic p f ⇒
           ∃x. gfp p f x

   [knaster_tarski_lfp]  Theorem

      |- ∀p f.
           poset p ∧ complete p ∧ function (carrier p) (carrier p) f ∧
           monotonic p f ⇒
           ∃x. lfp p f x

   [lfp_unique]  Theorem

      |- ∀p f x x'. poset p ∧ lfp p f x ∧ lfp p f x' ⇒ (x = x')

   [lub_pred]  Theorem

      |- ∀s r p x. lub (s,r) (λj. s j ∧ p j) x ⇔ lub (s,r) p x

   [poset_antisym]  Theorem

      |- ∀s r x y. poset (s,r) ∧ s x ∧ s y ∧ r x y ∧ r y x ⇒ (x = y)

   [poset_nonempty]  Theorem

      |- ∀s r. poset (s,r) ⇒ ∃x. s x

   [poset_refl]  Theorem

      |- ∀s r x. poset (s,r) ∧ s x ⇒ r x x

   [poset_trans]  Theorem

      |- ∀s r x y z. poset (s,r) ∧ s x ∧ s y ∧ s z ∧ r x y ∧ r y z ⇒ r x z


*)
end
