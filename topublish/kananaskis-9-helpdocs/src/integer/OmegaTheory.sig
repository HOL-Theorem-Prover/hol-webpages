signature OmegaTheory =
sig
  type thm = Thm.thm

  (*  Definitions  *)
    val MAP2_curried_def : thm
    val MAP2_tupled_primitive_def : thm
    val calc_nightmare_curried_def : thm
    val calc_nightmare_tupled_primitive_def : thm
    val dark_shadow_cond_row_curried_def : thm
    val dark_shadow_cond_row_tupled_primitive_def : thm
    val dark_shadow_condition_curried_def : thm
    val dark_shadow_condition_tupled_primitive_def : thm
    val dark_shadow_curried_def : thm
    val dark_shadow_row_curried_def : thm
    val dark_shadow_row_tupled_primitive_def : thm
    val dark_shadow_tupled_primitive_def : thm
    val evallower_curried_def : thm
    val evallower_tupled_primitive_def : thm
    val evalupper_curried_def : thm
    val evalupper_tupled_primitive_def : thm
    val fst1_def : thm
    val fst_nzero_def : thm
    val modhat_def : thm
    val nightmare_curried_def : thm
    val nightmare_tupled_primitive_def : thm
    val real_shadow_def : thm
    val rshadow_row_curried_def : thm
    val rshadow_row_tupled_primitive_def : thm
    val sumc_curried_def : thm
    val sumc_tupled_primitive_def : thm

  (*  Theorems  *)
    val MAP2_def : thm
    val MAP2_ind : thm
    val MAP2_zero_ADD : thm
    val alternative_equivalence : thm
    val basic_shadow_equivalence : thm
    val bigger_satisfies_lowers : thm
    val calc_nightmare_def : thm
    val calc_nightmare_ind : thm
    val calculational_nightmare : thm
    val dark_implies_real : thm
    val dark_shadow_FORALL : thm
    val dark_shadow_cond_row_def : thm
    val dark_shadow_cond_row_ind : thm
    val dark_shadow_condition_def : thm
    val dark_shadow_condition_ind : thm
    val dark_shadow_def : thm
    val dark_shadow_ind : thm
    val dark_shadow_row_def : thm
    val dark_shadow_row_ind : thm
    val darkrow_implies_realrow : thm
    val equality_removal : thm
    val eval_base : thm
    val eval_step_extra1 : thm
    val eval_step_extra2 : thm
    val eval_step_extra3 : thm
    val eval_step_extra4 : thm
    val eval_step_lower1 : thm
    val eval_step_lower2 : thm
    val eval_step_upper1 : thm
    val eval_step_upper2 : thm
    val evallower_FORALL : thm
    val evallower_def : thm
    val evallower_ind : thm
    val evalupper_FORALL : thm
    val evalupper_def : thm
    val evalupper_ind : thm
    val exact_shadow_case : thm
    val final_equivalence : thm
    val nightmare_EXISTS : thm
    val nightmare_def : thm
    val nightmare_implies_LHS : thm
    val nightmare_ind : thm
    val onlylowers_satisfiable : thm
    val onlyuppers_satisfiable : thm
    val real_shadow_FORALL : thm
    val real_shadow_always_implied : thm
    val real_shadow_revimp_lowers1 : thm
    val real_shadow_revimp_uppers1 : thm
    val rshadow_row_def : thm
    val rshadow_row_ind : thm
    val singleton_real_shadow : thm
    val smaller_satisfies_uppers : thm
    val sumc_ADD : thm
    val sumc_MULT : thm
    val sumc_def : thm
    val sumc_ind : thm
    val sumc_nonsingle : thm
    val sumc_singleton : thm
    val sumc_thm : thm

  val Omega_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [integer] Parent theory of "Omega"

   [MAP2_curried_def]  Definition

      |- ∀x x1 x2 x3. MAP2 x x1 x2 x3 = MAP2_tupled (x,x1,x2,x3)

   [MAP2_tupled_primitive_def]  Definition

      |- MAP2_tupled =
         WFREC
           (@R.
              WF R ∧ (∀y ys f pad. R (pad,f,[],ys) (pad,f,[],y::ys)) ∧
              (∀x xs f pad. R (pad,f,xs,[]) (pad,f,x::xs,[])) ∧
              ∀y x ys xs f pad. R (pad,f,xs,ys) (pad,f,x::xs,y::ys))
           (λMAP2_tupled a.
              case a of
                (pad,f,[],[]) => I []
              | (pad,f,[],y::ys) => I (f pad y::MAP2_tupled (pad,f,[],ys))
              | (pad,f,x::xs,[]) => I (f x pad::MAP2_tupled (pad,f,xs,[]))
              | (pad,f,x::xs,y'::ys') =>
                  I (f x y'::MAP2_tupled (pad,f,xs,ys')))

   [calc_nightmare_curried_def]  Definition

      |- ∀x x1 x2. calc_nightmare x x1 x2 ⇔ calc_nightmare_tupled (x,x1,x2)

   [calc_nightmare_tupled_primitive_def]  Definition

      |- calc_nightmare_tupled =
         WFREC (@R'. WF R' ∧ ∀R d rs c x. R' (x,c,rs) (x,c,(d,R)::rs))
           (λcalc_nightmare_tupled a.
              case a of
                (x,c,[]) => I F
              | (x,c,(d,R)::rs) =>
                  I
                    ((∃i.
                        (0 ≤ i ∧ i ≤ (&c * &d − &c − &d) / &c) ∧
                        (&d * x = R + i)) ∨
                     calc_nightmare_tupled (x,c,rs)))

   [dark_shadow_cond_row_curried_def]  Definition

      |- ∀x x1.
           dark_shadow_cond_row x x1 ⇔ dark_shadow_cond_row_tupled (x,x1)

   [dark_shadow_cond_row_tupled_primitive_def]  Definition

      |- dark_shadow_cond_row_tupled =
         WFREC (@R'. WF R' ∧ ∀R d t L c. R' ((c,L),t) ((c,L),(d,R)::t))
           (λdark_shadow_cond_row_tupled a.
              case a of
                (v,[]) => I T
              | ((c,L),(d,R)::t) =>
                  I
                    (¬(∃i.
                         &c * &d * i < &c * R ∧ &c * R ≤ &d * L ∧
                         &d * L < &c * &d * (i + 1)) ∧
                     dark_shadow_cond_row_tupled ((c,L),t)))

   [dark_shadow_condition_curried_def]  Definition

      |- ∀x x1.
           dark_shadow_condition x x1 ⇔ dark_shadow_condition_tupled (x,x1)

   [dark_shadow_condition_tupled_primitive_def]  Definition

      |- dark_shadow_condition_tupled =
         WFREC
           (@R.
              WF R ∧
              ∀L c lowers uppers. R (uppers,lowers) ((c,L)::uppers,lowers))
           (λdark_shadow_condition_tupled a.
              case a of
                ([],lowers) => I T
              | ((c,L)::uppers,lowers) =>
                  I
                    (dark_shadow_cond_row (c,L) lowers ∧
                     dark_shadow_condition_tupled (uppers,lowers)))

   [dark_shadow_curried_def]  Definition

      |- ∀x x1. dark_shadow x x1 ⇔ dark_shadow_tupled (x,x1)

   [dark_shadow_row_curried_def]  Definition

      |- ∀x x1 x2.
           dark_shadow_row x x1 x2 ⇔ dark_shadow_row_tupled (x,x1,x2)

   [dark_shadow_row_tupled_primitive_def]  Definition

      |- dark_shadow_row_tupled =
         WFREC (@R'. WF R' ∧ ∀R d rs L c. R' (c,L,rs) (c,L,(d,R)::rs))
           (λdark_shadow_row_tupled a.
              case a of
                (c,L,[]) => I T
              | (c,L,(d,R)::rs) =>
                  I
                    (&d * L − &c * R ≥ (&c − 1) * (&d − 1) ∧
                     dark_shadow_row_tupled (c,L,rs)))

   [dark_shadow_tupled_primitive_def]  Definition

      |- dark_shadow_tupled =
         WFREC
           (@R.
              WF R ∧
              ∀L c lowers uppers. R (uppers,lowers) ((c,L)::uppers,lowers))
           (λdark_shadow_tupled a.
              case a of
                ([],lowers) => I T
              | ((c,L)::uppers,lowers) =>
                  I
                    (dark_shadow_row c L lowers ∧
                     dark_shadow_tupled (uppers,lowers)))

   [evallower_curried_def]  Definition

      |- ∀x x1. evallower x x1 ⇔ evallower_tupled (x,x1)

   [evallower_tupled_primitive_def]  Definition

      |- evallower_tupled =
         WFREC (@R. WF R ∧ ∀y c cs x. R (x,cs) (x,(c,y)::cs))
           (λevallower_tupled a.
              case a of
                (x,[]) => I T
              | (x,(c,y)::cs) => I (y ≤ &c * x ∧ evallower_tupled (x,cs)))

   [evalupper_curried_def]  Definition

      |- ∀x x1. evalupper x x1 ⇔ evalupper_tupled (x,x1)

   [evalupper_tupled_primitive_def]  Definition

      |- evalupper_tupled =
         WFREC (@R. WF R ∧ ∀y c cs x. R (x,cs) (x,(c,y)::cs))
           (λevalupper_tupled a.
              case a of
                (x,[]) => I T
              | (x,(c,y)::cs) => I (&c * x ≤ y ∧ evalupper_tupled (x,cs)))

   [fst1_def]  Definition

      |- ∀x. fst1 x ⇔ (FST x = 1)

   [fst_nzero_def]  Definition

      |- ∀x. fst_nzero x ⇔ 0 < FST x

   [modhat_def]  Definition

      |- ∀x y. modhat x y = x − y * ((2 * x + y) / (2 * y))

   [nightmare_curried_def]  Definition

      |- ∀x x1 x2 x3 x4.
           nightmare x x1 x2 x3 x4 ⇔ nightmare_tupled (x,x1,x2,x3,x4)

   [nightmare_tupled_primitive_def]  Definition

      |- nightmare_tupled =
         WFREC
           (@R'.
              WF R' ∧
              ∀R d rs lowers uppers c x.
                R' (x,c,uppers,lowers,rs) (x,c,uppers,lowers,(d,R)::rs))
           (λnightmare_tupled a.
              case a of
                (x,c,uppers,lowers,[]) => I F
              | (x,c,uppers,lowers,(d,R)::rs) =>
                  I
                    ((∃i.
                        (0 ≤ i ∧ i ≤ (&c * &d − &c − &d) / &c) ∧
                        (&d * x = R + i) ∧ evalupper x uppers ∧
                        evallower x lowers) ∨
                     nightmare_tupled (x,c,uppers,lowers,rs)))

   [real_shadow_def]  Definition

      |- (∀lowers. real_shadow [] lowers ⇔ T) ∧
         ∀upper ls lowers.
           real_shadow (upper::ls) lowers ⇔
           rshadow_row upper lowers ∧ real_shadow ls lowers

   [rshadow_row_curried_def]  Definition

      |- ∀x x1. rshadow_row x x1 ⇔ rshadow_row_tupled (x,x1)

   [rshadow_row_tupled_primitive_def]  Definition

      |- rshadow_row_tupled =
         WFREC
           (@R.
              WF R ∧
              ∀lowery lowerc rs uppery upperc.
                R ((upperc,uppery),rs)
                  ((upperc,uppery),(lowerc,lowery)::rs))
           (λrshadow_row_tupled a.
              case a of
                (v,[]) => I T
              | ((upperc,uppery),(lowerc,lowery)::rs) =>
                  I
                    (&upperc * lowery ≤ &lowerc * uppery ∧
                     rshadow_row_tupled ((upperc,uppery),rs)))

   [sumc_curried_def]  Definition

      |- ∀x x1. sumc x x1 = sumc_tupled (x,x1)

   [sumc_tupled_primitive_def]  Definition

      |- sumc_tupled =
         WFREC (@R. WF R ∧ ∀v c vs cs. R (cs,vs) (c::cs,v::vs))
           (λsumc_tupled a.
              case a of
                (v0,[]) => I 0
              | ([],v::vs) => I 0
              | (c::cs,v::vs) => I (c * v + sumc_tupled (cs,vs)))

   [MAP2_def]  Theorem

      |- (∀pad f. MAP2 pad f [] [] = []) ∧
         (∀ys y pad f. MAP2 pad f [] (y::ys) = f pad y::MAP2 pad f [] ys) ∧
         (∀xs x pad f. MAP2 pad f (x::xs) [] = f x pad::MAP2 pad f xs []) ∧
         ∀ys y xs x pad f.
           MAP2 pad f (x::xs) (y::ys) = f x y::MAP2 pad f xs ys

   [MAP2_ind]  Theorem

      |- ∀P.
           (∀pad f. P pad f [] []) ∧
           (∀pad f y ys. P pad f [] ys ⇒ P pad f [] (y::ys)) ∧
           (∀pad f x xs. P pad f xs [] ⇒ P pad f (x::xs) []) ∧
           (∀pad f x xs y ys. P pad f xs ys ⇒ P pad f (x::xs) (y::ys)) ⇒
           ∀v v1 v2 v3. P v v1 v2 v3

   [MAP2_zero_ADD]  Theorem

      |- ∀xs. (MAP2 0 $+ [] xs = xs) ∧ (MAP2 0 $+ xs [] = xs)

   [alternative_equivalence]  Theorem

      |- ∀uppers lowers m.
           EVERY fst_nzero uppers ∧ EVERY fst_nzero lowers ∧
           EVERY (λp. FST p ≤ m) uppers ⇒
           ((∃x. evalupper x uppers ∧ evallower x lowers) ⇔
            dark_shadow uppers lowers ∨
            ∃x. nightmare x m uppers lowers lowers)

   [basic_shadow_equivalence]  Theorem

      |- ∀uppers lowers.
           EVERY fst_nzero uppers ∧ EVERY fst_nzero lowers ⇒
           ((∃x. evalupper x uppers ∧ evallower x lowers) ⇔
            real_shadow uppers lowers ∧
            dark_shadow_condition uppers lowers)

   [bigger_satisfies_lowers]  Theorem

      |- ∀lowers x y. evallower x lowers ∧ x < y ⇒ evallower y lowers

   [calc_nightmare_def]  Theorem

      |- (∀x c. calc_nightmare x c [] ⇔ F) ∧
         ∀x rs d c R.
           calc_nightmare x c ((d,R)::rs) ⇔
           (∃i.
              (0 ≤ i ∧ i ≤ (&c * &d − &c − &d) / &c) ∧ (&d * x = R + i)) ∨
           calc_nightmare x c rs

   [calc_nightmare_ind]  Theorem

      |- ∀P.
           (∀x c. P x c []) ∧ (∀x c d R rs. P x c rs ⇒ P x c ((d,R)::rs)) ⇒
           ∀v v1 v2. P v v1 v2

   [calculational_nightmare]  Theorem

      |- ∀rs.
           nightmare x c uppers lowers rs ⇔
           calc_nightmare x c rs ∧ evalupper x uppers ∧ evallower x lowers

   [dark_implies_real]  Theorem

      |- ∀uppers lowers.
           EVERY fst_nzero uppers ∧ EVERY fst_nzero lowers ∧
           dark_shadow uppers lowers ⇒
           real_shadow uppers lowers

   [dark_shadow_FORALL]  Theorem

      |- ∀uppers lowers.
           dark_shadow uppers lowers ⇔
           ∀c d L R.
             MEM (c,L) uppers ∧ MEM (d,R) lowers ⇒
             &d * L − &c * R ≥ (&c − 1) * (&d − 1)

   [dark_shadow_cond_row_def]  Theorem

      |- (∀c L. dark_shadow_cond_row (c,L) [] ⇔ T) ∧
         ∀t d c R L.
           dark_shadow_cond_row (c,L) ((d,R)::t) ⇔
           ¬(∃i.
               &c * &d * i < &c * R ∧ &c * R ≤ &d * L ∧
               &d * L < &c * &d * (i + 1)) ∧ dark_shadow_cond_row (c,L) t

   [dark_shadow_cond_row_ind]  Theorem

      |- ∀P.
           (∀c L. P (c,L) []) ∧
           (∀c L d R t. P (c,L) t ⇒ P (c,L) ((d,R)::t)) ⇒
           ∀v v1 v2. P (v,v1) v2

   [dark_shadow_condition_def]  Theorem

      |- (∀lowers. dark_shadow_condition [] lowers ⇔ T) ∧
         ∀uppers lowers c L.
           dark_shadow_condition ((c,L)::uppers) lowers ⇔
           dark_shadow_cond_row (c,L) lowers ∧
           dark_shadow_condition uppers lowers

   [dark_shadow_condition_ind]  Theorem

      |- ∀P.
           (∀lowers. P [] lowers) ∧
           (∀c L uppers lowers.
              P uppers lowers ⇒ P ((c,L)::uppers) lowers) ⇒
           ∀v v1. P v v1

   [dark_shadow_def]  Theorem

      |- (∀lowers. dark_shadow [] lowers ⇔ T) ∧
         ∀uppers lowers c L.
           dark_shadow ((c,L)::uppers) lowers ⇔
           dark_shadow_row c L lowers ∧ dark_shadow uppers lowers

   [dark_shadow_ind]  Theorem

      |- ∀P.
           (∀lowers. P [] lowers) ∧
           (∀c L uppers lowers.
              P uppers lowers ⇒ P ((c,L)::uppers) lowers) ⇒
           ∀v v1. P v v1

   [dark_shadow_row_def]  Theorem

      |- (∀c L. dark_shadow_row c L [] ⇔ T) ∧
         ∀rs d c R L.
           dark_shadow_row c L ((d,R)::rs) ⇔
           &d * L − &c * R ≥ (&c − 1) * (&d − 1) ∧ dark_shadow_row c L rs

   [dark_shadow_row_ind]  Theorem

      |- ∀P.
           (∀c L. P c L []) ∧ (∀c L d R rs. P c L rs ⇒ P c L ((d,R)::rs)) ⇒
           ∀v v1 v2. P v v1 v2

   [darkrow_implies_realrow]  Theorem

      |- ∀lowers c L.
           0 < c ∧ EVERY fst_nzero lowers ∧ dark_shadow_row c L lowers ⇒
           rshadow_row (c,L) lowers

   [equality_removal]  Theorem

      |- ∀c x cs vs.
           0 < c ⇒
           ((0 = c * x + sumc cs vs) ⇔
            ∃s.
              (x =
               -(c + 1) * s + sumc (MAP (λx. modhat x (c + 1)) cs) vs) ∧
              (0 = c * x + sumc cs vs))

   [eval_base]  Theorem

      |- p ⇔ ((evalupper x [] ∧ evallower x []) ∧ T) ∧ p

   [eval_step_extra1]  Theorem

      |- ((evalupper x ups ∧ evallower x lows) ∧ T) ∧ ex' ⇔
         (evalupper x ups ∧ evallower x lows) ∧ ex'

   [eval_step_extra2]  Theorem

      |- ((evalupper x ups ∧ evallower x lows) ∧ ex) ∧ ex' ⇔
         (evalupper x ups ∧ evallower x lows) ∧ ex ∧ ex'

   [eval_step_extra3]  Theorem

      |- ((evalupper x ups ∧ evallower x lows) ∧ T) ∧ ex' ∧ p ⇔
         ((evalupper x ups ∧ evallower x lows) ∧ ex') ∧ p

   [eval_step_extra4]  Theorem

      |- ((evalupper x ups ∧ evallower x lows) ∧ ex) ∧ ex' ∧ p ⇔
         ((evalupper x ups ∧ evallower x lows) ∧ ex ∧ ex') ∧ p

   [eval_step_lower1]  Theorem

      |- ((evalupper x ups ∧ evallower x lows) ∧ ex) ∧ r ≤ &c * x ⇔
         (evalupper x ups ∧ evallower x ((c,r)::lows)) ∧ ex

   [eval_step_lower2]  Theorem

      |- ((evalupper x ups ∧ evallower x lows) ∧ ex) ∧ r ≤ &c * x ∧ p ⇔
         ((evalupper x ups ∧ evallower x ((c,r)::lows)) ∧ ex) ∧ p

   [eval_step_upper1]  Theorem

      |- ((evalupper x ups ∧ evallower x lows) ∧ ex) ∧ &c * x ≤ r ⇔
         (evalupper x ((c,r)::ups) ∧ evallower x lows) ∧ ex

   [eval_step_upper2]  Theorem

      |- ((evalupper x ups ∧ evallower x lows) ∧ ex) ∧ &c * x ≤ r ∧ p ⇔
         ((evalupper x ((c,r)::ups) ∧ evallower x lows) ∧ ex) ∧ p

   [evallower_FORALL]  Theorem

      |- ∀lowers x.
           evallower x lowers ⇔ ∀d R. MEM (d,R) lowers ⇒ R ≤ &d * x

   [evallower_def]  Theorem

      |- (∀x. evallower x [] ⇔ T) ∧
         ∀y x cs c. evallower x ((c,y)::cs) ⇔ y ≤ &c * x ∧ evallower x cs

   [evallower_ind]  Theorem

      |- ∀P.
           (∀x. P x []) ∧ (∀x c y cs. P x cs ⇒ P x ((c,y)::cs)) ⇒
           ∀v v1. P v v1

   [evalupper_FORALL]  Theorem

      |- ∀uppers x.
           evalupper x uppers ⇔ ∀c L. MEM (c,L) uppers ⇒ &c * x ≤ L

   [evalupper_def]  Theorem

      |- (∀x. evalupper x [] ⇔ T) ∧
         ∀y x cs c. evalupper x ((c,y)::cs) ⇔ &c * x ≤ y ∧ evalupper x cs

   [evalupper_ind]  Theorem

      |- ∀P.
           (∀x. P x []) ∧ (∀x c y cs. P x cs ⇒ P x ((c,y)::cs)) ⇒
           ∀v v1. P v v1

   [exact_shadow_case]  Theorem

      |- ∀uppers lowers.
           EVERY fst_nzero uppers ∧ EVERY fst_nzero lowers ⇒
           EVERY fst1 uppers ∨ EVERY fst1 lowers ⇒
           ((∃x. evalupper x uppers ∧ evallower x lowers) ⇔
            real_shadow uppers lowers)

   [final_equivalence]  Theorem

      |- ∀uppers lowers m.
           EVERY fst_nzero uppers ∧ EVERY fst_nzero lowers ∧
           EVERY (λp. FST p ≤ m) uppers ⇒
           ((∃x. evalupper x uppers ∧ evallower x lowers) ⇔
            real_shadow uppers lowers ∧
            (dark_shadow uppers lowers ∨
             ∃x. nightmare x m uppers lowers lowers))

   [nightmare_EXISTS]  Theorem

      |- ∀rs x c uppers lowers.
           nightmare x c uppers lowers rs ⇔
           ∃i d R.
             0 ≤ i ∧ i ≤ (&d * &c − &c − &d) / &c ∧ MEM (d,R) rs ∧
             evalupper x uppers ∧ evallower x lowers ∧ (&d * x = R + i)

   [nightmare_def]  Theorem

      |- (∀x uppers lowers c. nightmare x c uppers lowers [] ⇔ F) ∧
         ∀x uppers rs lowers d c R.
           nightmare x c uppers lowers ((d,R)::rs) ⇔
           (∃i.
              (0 ≤ i ∧ i ≤ (&c * &d − &c − &d) / &c) ∧ (&d * x = R + i) ∧
              evalupper x uppers ∧ evallower x lowers) ∨
           nightmare x c uppers lowers rs

   [nightmare_implies_LHS]  Theorem

      |- ∀rs x uppers lowers c.
           nightmare x c uppers lowers rs ⇒
           evalupper x uppers ∧ evallower x lowers

   [nightmare_ind]  Theorem

      |- ∀P.
           (∀x c uppers lowers. P x c uppers lowers []) ∧
           (∀x c uppers lowers d R rs.
              P x c uppers lowers rs ⇒ P x c uppers lowers ((d,R)::rs)) ⇒
           ∀v v1 v2 v3 v4. P v v1 v2 v3 v4

   [onlylowers_satisfiable]  Theorem

      |- ∀lowers. EVERY fst_nzero lowers ⇒ ∃x. evallower x lowers

   [onlyuppers_satisfiable]  Theorem

      |- ∀uppers. EVERY fst_nzero uppers ⇒ ∃x. evalupper x uppers

   [real_shadow_FORALL]  Theorem

      |- ∀uppers lowers.
           real_shadow uppers lowers ⇔
           ∀c d L R. MEM (c,L) uppers ∧ MEM (d,R) lowers ⇒ &c * R ≤ &d * L

   [real_shadow_always_implied]  Theorem

      |- ∀uppers lowers x.
           evalupper x uppers ∧ evallower x lowers ∧
           EVERY fst_nzero uppers ∧ EVERY fst_nzero lowers ⇒
           real_shadow uppers lowers

   [real_shadow_revimp_lowers1]  Theorem

      |- ∀uppers lowers c L x.
           0 < c ∧ rshadow_row (c,L) lowers ∧ evalupper x uppers ∧
           evallower x lowers ∧ EVERY fst_nzero uppers ∧
           EVERY fst1 lowers ⇒
           ∃x. &c * x ≤ L ∧ evalupper x uppers ∧ evallower x lowers

   [real_shadow_revimp_uppers1]  Theorem

      |- ∀uppers lowers L x.
           rshadow_row (1,L) lowers ∧ evallower x lowers ∧
           evalupper x uppers ∧ EVERY fst_nzero lowers ∧
           EVERY fst1 uppers ⇒
           ∃x. x ≤ L ∧ evalupper x uppers ∧ evallower x lowers

   [rshadow_row_def]  Theorem

      |- (∀uppery upperc. rshadow_row (upperc,uppery) [] ⇔ T) ∧
         ∀uppery upperc rs lowery lowerc.
           rshadow_row (upperc,uppery) ((lowerc,lowery)::rs) ⇔
           &upperc * lowery ≤ &lowerc * uppery ∧
           rshadow_row (upperc,uppery) rs

   [rshadow_row_ind]  Theorem

      |- ∀P.
           (∀upperc uppery. P (upperc,uppery) []) ∧
           (∀upperc uppery lowerc lowery rs.
              P (upperc,uppery) rs ⇒
              P (upperc,uppery) ((lowerc,lowery)::rs)) ⇒
           ∀v v1 v2. P (v,v1) v2

   [singleton_real_shadow]  Theorem

      |- ∀c L x.
           &c * x ≤ L ∧ 0 < c ⇒
           ∀lowers.
             EVERY fst_nzero lowers ∧ evallower x lowers ⇒
             rshadow_row (c,L) lowers

   [smaller_satisfies_uppers]  Theorem

      |- ∀uppers x y. evalupper x uppers ∧ y < x ⇒ evalupper y uppers

   [sumc_ADD]  Theorem

      |- ∀cs vs ds. sumc cs vs + sumc ds vs = sumc (MAP2 0 $+ cs ds) vs

   [sumc_MULT]  Theorem

      |- ∀cs vs f. f * sumc cs vs = sumc (MAP (λx. f * x) cs) vs

   [sumc_def]  Theorem

      |- (∀v0. sumc v0 [] = 0) ∧ (∀v5 v4. sumc [] (v4::v5) = 0) ∧
         ∀vs v cs c. sumc (c::cs) (v::vs) = c * v + sumc cs vs

   [sumc_ind]  Theorem

      |- ∀P.
           (∀v0. P v0 []) ∧ (∀v4 v5. P [] (v4::v5)) ∧
           (∀c cs v vs. P cs vs ⇒ P (c::cs) (v::vs)) ⇒
           ∀v v1. P v v1

   [sumc_nonsingle]  Theorem

      |- ∀f cs c v vs.
           sumc (MAP f (c::cs)) (v::vs) = f c * v + sumc (MAP f cs) vs

   [sumc_singleton]  Theorem

      |- ∀f c. sumc (MAP f [c]) [1] = f c

   [sumc_thm]  Theorem

      |- ∀cs vs c v.
           (sumc [] vs = 0) ∧ (sumc cs [] = 0) ∧
           (sumc (c::cs) (v::vs) = c * v + sumc cs vs)


*)
end
