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
    val iSUC : thm
  
  (*  Theorems  *)
    val BIT_MODIFY_EVAL : thm
    val BIT_REVERSE_EVAL : thm
    val FDUB_FDUB : thm
    val FDUB_iDIV2 : thm
    val FDUB_iDUB : thm
    val LOG_compute : thm
    val LOWEST_SET_BIT : thm
    val LOWEST_SET_BIT_compute : thm
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
    val l2n_pow2_compute : thm
    val n2l_pow2_compute : thm
    val numeral_ilog2 : thm
    val numeral_log2 : thm
  
  val numeral_bit_grammars : type_grammar.grammar * term_grammar.grammar
  
  
(*
   [bit] Parent theory of "numeral_bit"
   
   [BIT_MODF_def]  Definition
      
      |- (!f x b e y. BIT_MODF 0 f x b e y = y) /\
         !n f x b e y.
           BIT_MODF (SUC n) f x b e y =
           BIT_MODF n f (x DIV 2) (b + 1) (2 * e)
             (if f b (ODD x) then e + y else y)
   
   [BIT_REV_def]  Definition
      
      |- (!x y. BIT_REV 0 x y = y) /\
         !n x y.
           BIT_REV (SUC n) x y =
           BIT_REV n (x DIV 2) (2 * y + SBIT (ODD x) 0)
   
   [FDUB_def]  Definition
      
      |- (!f. FDUB f 0 = 0) /\ !f n. FDUB f (SUC n) = f (f (SUC n))
   
   [SFUNPOW_def]  Definition
      
      |- (!f x. SFUNPOW f 0 x = x) /\
         !f n x.
           SFUNPOW f (SUC n) x = if x = 0 then 0 else SFUNPOW f n (f x)
   
   [iBITWISE_def]  Definition
      
      |- iBITWISE = BITWISE
   
   [iDIV2]  Definition
      
      |- iDIV2 = DIV2
   
   [iLOG2_def]  Definition
      
      |- !n. iLOG2 n = LOG2 (n + 1)
   
   [iSUC]  Definition
      
      |- iSUC = SUC
   
   [BIT_MODIFY_EVAL]  Theorem
      
      |- !m f n. BIT_MODIFY m f n = BIT_MODF m f n 0 1 0
   
   [BIT_REVERSE_EVAL]  Theorem
      
      |- !m n. BIT_REVERSE m n = BIT_REV m n 0
   
   [FDUB_FDUB]  Theorem
      
      |- (FDUB (FDUB f) ZERO = ZERO) /\
         (!x. FDUB (FDUB f) (iSUC x) = FDUB f (FDUB f (iSUC x))) /\
         (!x. FDUB (FDUB f) (BIT1 x) = FDUB f (FDUB f (BIT1 x))) /\
         !x. FDUB (FDUB f) (BIT2 x) = FDUB f (FDUB f (BIT2 x))
   
   [FDUB_iDIV2]  Theorem
      
      |- !x. FDUB iDIV2 x = iDIV2 (iDIV2 x)
   
   [FDUB_iDUB]  Theorem
      
      |- !x. FDUB numeral$iDUB x = numeral$iDUB (numeral$iDUB x)
   
   [LOG_compute]  Theorem
      
      |- !m n.
           LOG m n =
           if m < 2 \/ (n = 0) then
             FAIL LOG base < 2 or n = 0 m n
           else
             if n < m then 0 else SUC (LOG m (n DIV m))
   
   [LOWEST_SET_BIT]  Theorem
      
      |- !n.
           n <> 0 ==>
           (LOWEST_SET_BIT n =
            if ODD n then 0 else 1 + LOWEST_SET_BIT (DIV2 n))
   
   [LOWEST_SET_BIT_compute]  Theorem
      
      |- (!n.
            LOWEST_SET_BIT (NUMERAL (BIT2 n)) =
            SUC (LOWEST_SET_BIT (NUMERAL (SUC n)))) /\
         !n. LOWEST_SET_BIT (NUMERAL (BIT1 n)) = 0
   
   [MOD_2EXP_EQ]  Theorem
      
      |- (!a b. MOD_2EXP_EQ 0 a b <=> T) /\
         (!n a b.
            MOD_2EXP_EQ (SUC n) a b <=>
            (ODD a <=> ODD b) /\ MOD_2EXP_EQ n (DIV2 a) (DIV2 b)) /\
         !n a. MOD_2EXP_EQ n a a <=> T
   
   [MOD_2EXP_MAX]  Theorem
      
      |- (!a. MOD_2EXP_MAX 0 a <=> T) /\
         !n a. MOD_2EXP_MAX (SUC n) a <=> ODD a /\ MOD_2EXP_MAX n (DIV2 a)
   
   [NUMERAL_BITWISE]  Theorem
      
      |- (!x f a. BITWISE x f 0 0 = NUMERAL (iBITWISE x f 0 0)) /\
         (!x f a.
            BITWISE x f (NUMERAL a) 0 =
            NUMERAL (iBITWISE x f (NUMERAL a) 0)) /\
         (!x f b.
            BITWISE x f 0 (NUMERAL b) =
            NUMERAL (iBITWISE x f 0 (NUMERAL b))) /\
         !x f a b.
           BITWISE x f (NUMERAL a) (NUMERAL b) =
           NUMERAL (iBITWISE x f (NUMERAL a) (NUMERAL b))
   
   [NUMERAL_BIT_MODF]  Theorem
      
      |- (!f x b e y. BIT_MODF 0 f x b e y = y) /\
         (!n f b e y.
            BIT_MODF (NUMERAL (BIT1 n)) f 0 b (NUMERAL e) y =
            BIT_MODF (NUMERAL (BIT1 n) - 1) f 0 (b + 1)
              (NUMERAL (numeral$iDUB e))
              (if f b F then NUMERAL e + y else y)) /\
         (!n f b e y.
            BIT_MODF (NUMERAL (BIT2 n)) f 0 b (NUMERAL e) y =
            BIT_MODF (NUMERAL (BIT1 n)) f 0 (b + 1)
              (NUMERAL (numeral$iDUB e))
              (if f b F then NUMERAL e + y else y)) /\
         (!n f x b e y.
            BIT_MODF (NUMERAL (BIT1 n)) f (NUMERAL x) b (NUMERAL e) y =
            BIT_MODF (NUMERAL (BIT1 n) - 1) f (DIV2 (NUMERAL x)) (b + 1)
              (NUMERAL (numeral$iDUB e))
              (if f b (ODD x) then NUMERAL e + y else y)) /\
         !n f x b e y.
           BIT_MODF (NUMERAL (BIT2 n)) f (NUMERAL x) b (NUMERAL e) y =
           BIT_MODF (NUMERAL (BIT1 n)) f (DIV2 (NUMERAL x)) (b + 1)
             (NUMERAL (numeral$iDUB e))
             (if f b (ODD x) then NUMERAL e + y else y)
   
   [NUMERAL_BIT_MODIFY]  Theorem
      
      |- (!m f.
            BIT_MODIFY (NUMERAL m) f 0 = BIT_MODF (NUMERAL m) f 0 0 1 0) /\
         !m f n.
           BIT_MODIFY (NUMERAL m) f (NUMERAL n) =
           BIT_MODF (NUMERAL m) f (NUMERAL n) 0 1 0
   
   [NUMERAL_BIT_REV]  Theorem
      
      |- (!x y. BIT_REV 0 x y = y) /\
         (!n y.
            BIT_REV (NUMERAL (BIT1 n)) 0 y =
            BIT_REV (NUMERAL (BIT1 n) - 1) 0 (numeral$iDUB y)) /\
         (!n y.
            BIT_REV (NUMERAL (BIT2 n)) 0 y =
            BIT_REV (NUMERAL (BIT1 n)) 0 (numeral$iDUB y)) /\
         (!n x y.
            BIT_REV (NUMERAL (BIT1 n)) (NUMERAL x) y =
            BIT_REV (NUMERAL (BIT1 n) - 1) (DIV2 (NUMERAL x))
              (if ODD x then BIT1 y else numeral$iDUB y)) /\
         !n x y.
           BIT_REV (NUMERAL (BIT2 n)) (NUMERAL x) y =
           BIT_REV (NUMERAL (BIT1 n)) (DIV2 (NUMERAL x))
             (if ODD x then BIT1 y else numeral$iDUB y)
   
   [NUMERAL_BIT_REVERSE]  Theorem
      
      |- (!m.
            BIT_REVERSE (NUMERAL m) 0 =
            NUMERAL (BIT_REV (NUMERAL m) 0 ZERO)) /\
         !n m.
           BIT_REVERSE (NUMERAL m) (NUMERAL n) =
           NUMERAL (BIT_REV (NUMERAL m) (NUMERAL n) ZERO)
   
   [NUMERAL_DIV_2EXP]  Theorem
      
      |- (!n. DIV_2EXP n 0 = 0) /\
         !n x. DIV_2EXP n (NUMERAL x) = NUMERAL (SFUNPOW iDIV2 n x)
   
   [NUMERAL_SFUNPOW_FDUB]  Theorem
      
      |- !f.
           (!x. SFUNPOW (FDUB f) 0 x = x) /\
           (!y. SFUNPOW (FDUB f) y 0 = 0) /\
           (!n x.
              SFUNPOW (FDUB f) (NUMERAL (BIT1 n)) x =
              SFUNPOW (FDUB (FDUB f)) (NUMERAL n) (FDUB f x)) /\
           !n x.
             SFUNPOW (FDUB f) (NUMERAL (BIT2 n)) x =
             SFUNPOW (FDUB (FDUB f)) (NUMERAL n) (FDUB f (FDUB f x))
   
   [NUMERAL_SFUNPOW_iDIV2]  Theorem
      
      |- (!x. SFUNPOW iDIV2 0 x = x) /\ (!y. SFUNPOW iDIV2 y 0 = 0) /\
         (!n x.
            SFUNPOW iDIV2 (NUMERAL (BIT1 n)) x =
            SFUNPOW (FDUB iDIV2) (NUMERAL n) (iDIV2 x)) /\
         !n x.
           SFUNPOW iDIV2 (NUMERAL (BIT2 n)) x =
           SFUNPOW (FDUB iDIV2) (NUMERAL n) (iDIV2 (iDIV2 x))
   
   [NUMERAL_SFUNPOW_iDUB]  Theorem
      
      |- (!x. SFUNPOW numeral$iDUB 0 x = x) /\
         (!y. SFUNPOW numeral$iDUB y 0 = 0) /\
         (!n x.
            SFUNPOW numeral$iDUB (NUMERAL (BIT1 n)) x =
            SFUNPOW (FDUB numeral$iDUB) (NUMERAL n) (numeral$iDUB x)) /\
         !n x.
           SFUNPOW numeral$iDUB (NUMERAL (BIT2 n)) x =
           SFUNPOW (FDUB numeral$iDUB) (NUMERAL n)
             (numeral$iDUB (numeral$iDUB x))
   
   [NUMERAL_TIMES_2EXP]  Theorem
      
      |- (!n. TIMES_2EXP n 0 = 0) /\
         !n x.
           TIMES_2EXP n (NUMERAL x) = NUMERAL (SFUNPOW numeral$iDUB n x)
   
   [NUMERAL_iDIV2]  Theorem
      
      |- (iDIV2 ZERO = ZERO) /\ (iDIV2 (iSUC ZERO) = ZERO) /\
         (iDIV2 (BIT1 n) = n) /\ (iDIV2 (iSUC (BIT1 n)) = iSUC n) /\
         (iDIV2 (BIT2 n) = iSUC n) /\ (iDIV2 (iSUC (BIT2 n)) = iSUC n) /\
         (NUMERAL (iSUC n) = NUMERAL (SUC n))
   
   [iBITWISE]  Theorem
      
      |- (!opr a b. iBITWISE 0 opr a b = ZERO) /\
         (!x opr a b.
            iBITWISE (NUMERAL (BIT1 x)) opr a b =
            (let w = iBITWISE (NUMERAL (BIT1 x) - 1) opr (DIV2 a) (DIV2 b)
             in
               if opr (ODD a) (ODD b) then BIT1 w else numeral$iDUB w)) /\
         !x opr a b.
           iBITWISE (NUMERAL (BIT2 x)) opr a b =
           (let w = iBITWISE (NUMERAL (BIT1 x)) opr (DIV2 a) (DIV2 b) in
              if opr (ODD a) (ODD b) then BIT1 w else numeral$iDUB w)
   
   [iDUB_NUMERAL]  Theorem
      
      |- numeral$iDUB (NUMERAL i) = NUMERAL (numeral$iDUB i)
   
   [l2n_pow2_compute]  Theorem
      
      |- (!p. l2n (2 ** p) [] = 0) /\
         !p h t.
           l2n (2 ** p) (h::t) =
           MOD_2EXP p h + TIMES_2EXP p (l2n (2 ** p) t)
   
   [n2l_pow2_compute]  Theorem
      
      |- !p n.
           0 < p ==>
           (n2l (2 ** p) n =
            (let (q,r) = DIVMOD_2EXP p n in
               if q = 0 then [r] else r::n2l (2 ** p) q))
   
   [numeral_ilog2]  Theorem
      
      |- (iLOG2 ZERO = 0) /\ (!n. iLOG2 (BIT1 n) = 1 + iLOG2 n) /\
         !n. iLOG2 (BIT2 n) = 1 + iLOG2 n
   
   [numeral_log2]  Theorem
      
      |- (!n. LOG2 (NUMERAL (BIT1 n)) = iLOG2 (numeral$iDUB n)) /\
         !n. LOG2 (NUMERAL (BIT2 n)) = iLOG2 (BIT1 n)
   
   
*)
end
