signature numeral_bitTheory =
sig
  type thm = Thm.thm

  (*  Definitions  *)
    val BIT_MODF_def : thm
    val BIT_REV_def : thm
    val FDUB_def : thm
    val SFUNPOW_def : thm
    val iBITWISE_def : thm
    val iDIV2 : thm
    val iLOG2_def : thm
    val iMOD_2EXP : thm
    val iSUC : thm

  (*  Theorems  *)
    val BIT_MODIFY_EVAL : thm
    val BIT_REVERSE_EVAL : thm
    val DIV_2EXP : thm
    val FDUB_FDUB : thm
    val FDUB_iDIV2 : thm
    val FDUB_iDUB : thm
    val LOG_compute : thm
    val LOWEST_SET_BIT : thm
    val LOWEST_SET_BIT_compute : thm
    val MOD_2EXP : thm
    val MOD_2EXP_EQ : thm
    val MOD_2EXP_MAX : thm
    val NUMERAL_BITWISE : thm
    val NUMERAL_BIT_MODF : thm
    val NUMERAL_BIT_MODIFY : thm
    val NUMERAL_BIT_REV : thm
    val NUMERAL_BIT_REVERSE : thm
    val NUMERAL_DIV_2EXP : thm
    val NUMERAL_SFUNPOW_FDUB : thm
    val NUMERAL_SFUNPOW_iDIV2 : thm
    val NUMERAL_SFUNPOW_iDUB : thm
    val NUMERAL_TIMES_2EXP : thm
    val NUMERAL_iDIV2 : thm
    val iBITWISE : thm
    val iDUB_NUMERAL : thm
    val numeral_ilog2 : thm
    val numeral_imod_2exp : thm
    val numeral_log2 : thm
    val numeral_mod2 : thm

  val numeral_bit_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [bit] Parent theory of "numeral_bit"

   [BIT_MODF_def]  Definition

      |- (∀f x b e y. BIT_MODF 0 f x b e y = y) ∧
         ∀n f x b e y.
           BIT_MODF (SUC n) f x b e y =
           BIT_MODF n f (x DIV 2) (b + 1) (2 * e)
             (if f b (ODD x) then e + y else y)

   [BIT_REV_def]  Definition

      |- (∀x y. BIT_REV 0 x y = y) ∧
         ∀n x y.
           BIT_REV (SUC n) x y =
           BIT_REV n (x DIV 2) (2 * y + SBIT (ODD x) 0)

   [FDUB_def]  Definition

      |- (∀f. FDUB f 0 = 0) ∧ ∀f n. FDUB f (SUC n) = f (f (SUC n))

   [SFUNPOW_def]  Definition

      |- (∀f x. SFUNPOW f 0 x = x) ∧
         ∀f n x.
           SFUNPOW f (SUC n) x = if x = 0 then 0 else SFUNPOW f n (f x)

   [iBITWISE_def]  Definition

      |- numeral_bit$iBITWISE = BITWISE

   [iDIV2]  Definition

      |- numeral_bit$iDIV2 = DIV2

   [iLOG2_def]  Definition

      |- ∀n. numeral_bit$iLOG2 n = LOG2 (n + 1)

   [iMOD_2EXP]  Definition

      |- numeral_bit$iMOD_2EXP = MOD_2EXP

   [iSUC]  Definition

      |- numeral_bit$iSUC = SUC

   [BIT_MODIFY_EVAL]  Theorem

      |- ∀m f n. BIT_MODIFY m f n = BIT_MODF m f n 0 1 0

   [BIT_REVERSE_EVAL]  Theorem

      |- ∀m n. BIT_REVERSE m n = BIT_REV m n 0

   [DIV_2EXP]  Theorem

      |- ∀n x. DIV_2EXP n x = FUNPOW DIV2 n x

   [FDUB_FDUB]  Theorem

      |- (FDUB (FDUB f) ZERO = ZERO) ∧
         (∀x.
            FDUB (FDUB f) (numeral_bit$iSUC x) =
            FDUB f (FDUB f (numeral_bit$iSUC x))) ∧
         (∀x. FDUB (FDUB f) (BIT1 x) = FDUB f (FDUB f (BIT1 x))) ∧
         ∀x. FDUB (FDUB f) (BIT2 x) = FDUB f (FDUB f (BIT2 x))

   [FDUB_iDIV2]  Theorem

      |- ∀x.
           FDUB numeral_bit$iDIV2 x =
           numeral_bit$iDIV2 (numeral_bit$iDIV2 x)

   [FDUB_iDUB]  Theorem

      |- ∀x. FDUB numeral$iDUB x = numeral$iDUB (numeral$iDUB x)

   [LOG_compute]  Theorem

      |- ∀m n.
           LOG m n =
           if m < 2 ∨ (n = 0) then FAIL LOG base < 2 or n = 0 m n
           else if n < m then 0
           else SUC (LOG m (n DIV m))

   [LOWEST_SET_BIT]  Theorem

      |- ∀n.
           n ≠ 0 ⇒
           (LOWEST_SET_BIT n =
            if ODD n then 0 else 1 + LOWEST_SET_BIT (DIV2 n))

   [LOWEST_SET_BIT_compute]  Theorem

      |- (∀n.
            LOWEST_SET_BIT (NUMERAL (BIT2 n)) =
            SUC (LOWEST_SET_BIT (NUMERAL (SUC n)))) ∧
         ∀n. LOWEST_SET_BIT (NUMERAL (BIT1 n)) = 0

   [MOD_2EXP]  Theorem

      |- (∀x. MOD_2EXP x 0 = 0) ∧
         ∀x n. MOD_2EXP x (NUMERAL n) = NUMERAL (numeral_bit$iMOD_2EXP x n)

   [MOD_2EXP_EQ]  Theorem

      |- (∀a b. MOD_2EXP_EQ 0 a b ⇔ T) ∧
         (∀n a b.
            MOD_2EXP_EQ (SUC n) a b ⇔
            (ODD a ⇔ ODD b) ∧ MOD_2EXP_EQ n (DIV2 a) (DIV2 b)) ∧
         ∀n a. MOD_2EXP_EQ n a a ⇔ T

   [MOD_2EXP_MAX]  Theorem

      |- (∀a. MOD_2EXP_MAX 0 a ⇔ T) ∧
         ∀n a. MOD_2EXP_MAX (SUC n) a ⇔ ODD a ∧ MOD_2EXP_MAX n (DIV2 a)

   [NUMERAL_BITWISE]  Theorem

      |- (∀x f a.
            BITWISE x f 0 0 = NUMERAL (numeral_bit$iBITWISE x f 0 0)) ∧
         (∀x f a.
            BITWISE x f (NUMERAL a) 0 =
            NUMERAL (numeral_bit$iBITWISE x f (NUMERAL a) 0)) ∧
         (∀x f b.
            BITWISE x f 0 (NUMERAL b) =
            NUMERAL (numeral_bit$iBITWISE x f 0 (NUMERAL b))) ∧
         ∀x f a b.
           BITWISE x f (NUMERAL a) (NUMERAL b) =
           NUMERAL (numeral_bit$iBITWISE x f (NUMERAL a) (NUMERAL b))

   [NUMERAL_BIT_MODF]  Theorem

      |- (∀f x b e y. BIT_MODF 0 f x b e y = y) ∧
         (∀n f b e y.
            BIT_MODF (NUMERAL (BIT1 n)) f 0 b (NUMERAL e) y =
            BIT_MODF (NUMERAL (BIT1 n) − 1) f 0 (b + 1)
              (NUMERAL (numeral$iDUB e))
              (if f b F then NUMERAL e + y else y)) ∧
         (∀n f b e y.
            BIT_MODF (NUMERAL (BIT2 n)) f 0 b (NUMERAL e) y =
            BIT_MODF (NUMERAL (BIT1 n)) f 0 (b + 1)
              (NUMERAL (numeral$iDUB e))
              (if f b F then NUMERAL e + y else y)) ∧
         (∀n f x b e y.
            BIT_MODF (NUMERAL (BIT1 n)) f (NUMERAL x) b (NUMERAL e) y =
            BIT_MODF (NUMERAL (BIT1 n) − 1) f (DIV2 (NUMERAL x)) (b + 1)
              (NUMERAL (numeral$iDUB e))
              (if f b (ODD x) then NUMERAL e + y else y)) ∧
         ∀n f x b e y.
           BIT_MODF (NUMERAL (BIT2 n)) f (NUMERAL x) b (NUMERAL e) y =
           BIT_MODF (NUMERAL (BIT1 n)) f (DIV2 (NUMERAL x)) (b + 1)
             (NUMERAL (numeral$iDUB e))
             (if f b (ODD x) then NUMERAL e + y else y)

   [NUMERAL_BIT_MODIFY]  Theorem

      |- (∀m f.
            BIT_MODIFY (NUMERAL m) f 0 = BIT_MODF (NUMERAL m) f 0 0 1 0) ∧
         ∀m f n.
           BIT_MODIFY (NUMERAL m) f (NUMERAL n) =
           BIT_MODF (NUMERAL m) f (NUMERAL n) 0 1 0

   [NUMERAL_BIT_REV]  Theorem

      |- (∀x y. BIT_REV 0 x y = y) ∧
         (∀n y.
            BIT_REV (NUMERAL (BIT1 n)) 0 y =
            BIT_REV (NUMERAL (BIT1 n) − 1) 0 (numeral$iDUB y)) ∧
         (∀n y.
            BIT_REV (NUMERAL (BIT2 n)) 0 y =
            BIT_REV (NUMERAL (BIT1 n)) 0 (numeral$iDUB y)) ∧
         (∀n x y.
            BIT_REV (NUMERAL (BIT1 n)) (NUMERAL x) y =
            BIT_REV (NUMERAL (BIT1 n) − 1) (DIV2 (NUMERAL x))
              (if ODD x then BIT1 y else numeral$iDUB y)) ∧
         ∀n x y.
           BIT_REV (NUMERAL (BIT2 n)) (NUMERAL x) y =
           BIT_REV (NUMERAL (BIT1 n)) (DIV2 (NUMERAL x))
             (if ODD x then BIT1 y else numeral$iDUB y)

   [NUMERAL_BIT_REVERSE]  Theorem

      |- (∀m.
            BIT_REVERSE (NUMERAL m) 0 =
            NUMERAL (BIT_REV (NUMERAL m) 0 ZERO)) ∧
         ∀n m.
           BIT_REVERSE (NUMERAL m) (NUMERAL n) =
           NUMERAL (BIT_REV (NUMERAL m) (NUMERAL n) ZERO)

   [NUMERAL_DIV_2EXP]  Theorem

      |- (∀n. DIV_2EXP n 0 = 0) ∧
         ∀n x.
           DIV_2EXP n (NUMERAL x) = NUMERAL (SFUNPOW numeral_bit$iDIV2 n x)

   [NUMERAL_SFUNPOW_FDUB]  Theorem

      |- ∀f.
           (∀x. SFUNPOW (FDUB f) 0 x = x) ∧
           (∀y. SFUNPOW (FDUB f) y 0 = 0) ∧
           (∀n x.
              SFUNPOW (FDUB f) (NUMERAL (BIT1 n)) x =
              SFUNPOW (FDUB (FDUB f)) (NUMERAL n) (FDUB f x)) ∧
           ∀n x.
             SFUNPOW (FDUB f) (NUMERAL (BIT2 n)) x =
             SFUNPOW (FDUB (FDUB f)) (NUMERAL n) (FDUB f (FDUB f x))

   [NUMERAL_SFUNPOW_iDIV2]  Theorem

      |- (∀x. SFUNPOW numeral_bit$iDIV2 0 x = x) ∧
         (∀y. SFUNPOW numeral_bit$iDIV2 y 0 = 0) ∧
         (∀n x.
            SFUNPOW numeral_bit$iDIV2 (NUMERAL (BIT1 n)) x =
            SFUNPOW (FDUB numeral_bit$iDIV2) (NUMERAL n)
              (numeral_bit$iDIV2 x)) ∧
         ∀n x.
           SFUNPOW numeral_bit$iDIV2 (NUMERAL (BIT2 n)) x =
           SFUNPOW (FDUB numeral_bit$iDIV2) (NUMERAL n)
             (numeral_bit$iDIV2 (numeral_bit$iDIV2 x))

   [NUMERAL_SFUNPOW_iDUB]  Theorem

      |- (∀x. SFUNPOW numeral$iDUB 0 x = x) ∧
         (∀y. SFUNPOW numeral$iDUB y 0 = 0) ∧
         (∀n x.
            SFUNPOW numeral$iDUB (NUMERAL (BIT1 n)) x =
            SFUNPOW (FDUB numeral$iDUB) (NUMERAL n) (numeral$iDUB x)) ∧
         ∀n x.
           SFUNPOW numeral$iDUB (NUMERAL (BIT2 n)) x =
           SFUNPOW (FDUB numeral$iDUB) (NUMERAL n)
             (numeral$iDUB (numeral$iDUB x))

   [NUMERAL_TIMES_2EXP]  Theorem

      |- (∀n. TIMES_2EXP n 0 = 0) ∧
         ∀n x.
           TIMES_2EXP n (NUMERAL x) = NUMERAL (SFUNPOW numeral$iDUB n x)

   [NUMERAL_iDIV2]  Theorem

      |- (numeral_bit$iDIV2 ZERO = ZERO) ∧
         (numeral_bit$iDIV2 (numeral_bit$iSUC ZERO) = ZERO) ∧
         (numeral_bit$iDIV2 (BIT1 n) = n) ∧
         (numeral_bit$iDIV2 (numeral_bit$iSUC (BIT1 n)) =
          numeral_bit$iSUC n) ∧
         (numeral_bit$iDIV2 (BIT2 n) = numeral_bit$iSUC n) ∧
         (numeral_bit$iDIV2 (numeral_bit$iSUC (BIT2 n)) =
          numeral_bit$iSUC n) ∧
         (NUMERAL (numeral_bit$iSUC n) = NUMERAL (SUC n))

   [iBITWISE]  Theorem

      |- (∀opr a b. numeral_bit$iBITWISE 0 opr a b = ZERO) ∧
         (∀x opr a b.
            numeral_bit$iBITWISE (NUMERAL (BIT1 x)) opr a b =
            (let w =
                   numeral_bit$iBITWISE (NUMERAL (BIT1 x) − 1) opr (DIV2 a)
                     (DIV2 b)
             in
               if opr (ODD a) (ODD b) then BIT1 w else numeral$iDUB w)) ∧
         ∀x opr a b.
           numeral_bit$iBITWISE (NUMERAL (BIT2 x)) opr a b =
           (let w =
                  numeral_bit$iBITWISE (NUMERAL (BIT1 x)) opr (DIV2 a)
                    (DIV2 b)
            in
              if opr (ODD a) (ODD b) then BIT1 w else numeral$iDUB w)

   [iDUB_NUMERAL]  Theorem

      |- numeral$iDUB (NUMERAL i) = NUMERAL (numeral$iDUB i)

   [numeral_ilog2]  Theorem

      |- (numeral_bit$iLOG2 ZERO = 0) ∧
         (∀n. numeral_bit$iLOG2 (BIT1 n) = 1 + numeral_bit$iLOG2 n) ∧
         ∀n. numeral_bit$iLOG2 (BIT2 n) = 1 + numeral_bit$iLOG2 n

   [numeral_imod_2exp]  Theorem

      |- (∀n. numeral_bit$iMOD_2EXP 0 n = ZERO) ∧
         (∀x n. numeral_bit$iMOD_2EXP x ZERO = ZERO) ∧
         (∀x n.
            numeral_bit$iMOD_2EXP (NUMERAL (BIT1 x)) (BIT1 n) =
            BIT1 (numeral_bit$iMOD_2EXP (NUMERAL (BIT1 x) − 1) n)) ∧
         (∀x n.
            numeral_bit$iMOD_2EXP (NUMERAL (BIT2 x)) (BIT1 n) =
            BIT1 (numeral_bit$iMOD_2EXP (NUMERAL (BIT1 x)) n)) ∧
         (∀x n.
            numeral_bit$iMOD_2EXP (NUMERAL (BIT1 x)) (BIT2 n) =
            numeral$iDUB
              (numeral_bit$iMOD_2EXP (NUMERAL (BIT1 x) − 1) (SUC n))) ∧
         ∀x n.
           numeral_bit$iMOD_2EXP (NUMERAL (BIT2 x)) (BIT2 n) =
           numeral$iDUB (numeral_bit$iMOD_2EXP (NUMERAL (BIT1 x)) (SUC n))

   [numeral_log2]  Theorem

      |- (∀n.
            LOG2 (NUMERAL (BIT1 n)) = numeral_bit$iLOG2 (numeral$iDUB n)) ∧
         ∀n. LOG2 (NUMERAL (BIT2 n)) = numeral_bit$iLOG2 (BIT1 n)

   [numeral_mod2]  Theorem

      |- (0 MOD 2 = 0) ∧ (∀n. NUMERAL (BIT1 n) MOD 2 = 1) ∧
         ∀n. NUMERAL (BIT2 n) MOD 2 = 0


*)
end
