signature ieeeTheory =
sig
  type thm = Thm.thm
  
  (*  Definitions  *)
    val Eq : thm
    val Exponent : thm
    val Finite : thm
    val Float : thm
    val Fraction : thm
    val Gt : thm
    val Infinity : thm
    val Isdenormal : thm
    val Isintegral : thm
    val Isnan : thm
    val Isnormal : thm
    val Iszero : thm
    val Lt : thm
    val Minus_infinity : thm
    val Minus_zero : thm
    val Plus_infinity : thm
    val Plus_zero : thm
    val ROUNDFLOAT : thm
    val Sign : thm
    val To_nearest : thm
    val To_ninfinity : thm
    val To_pinfinity : thm
    val Ulp : thm
    val Un : thm
    val Val : thm
    val bias : thm
    val bottomfloat : thm
    val ccode_BIJ : thm
    val ccode_TY_DEF : thm
    val ccode_case : thm
    val ccode_size_def : thm
    val closest : thm
    val emax : thm
    val encoding : thm
    val exponent : thm
    val expwidth : thm
    val fadd : thm
    val fcompare : thm
    val fdiv : thm
    val feq : thm
    val fge : thm
    val fgt : thm
    val fintrnd : thm
    val fle : thm
    val float_TY_DEF : thm
    val float_To_zero : thm
    val float_abs : thm
    val float_add : thm
    val float_div : thm
    val float_eq : thm
    val float_format : thm
    val float_ge : thm
    val float_gt : thm
    val float_le : thm
    val float_lt : thm
    val float_mul : thm
    val float_neg : thm
    val float_rem : thm
    val float_sqrt : thm
    val float_sub : thm
    val float_tybij : thm
    val flt : thm
    val fmul : thm
    val fneg : thm
    val fraction : thm
    val fracwidth : thm
    val frem : thm
    val fsqrt : thm
    val fsub : thm
    val intround_def : thm
    val is_closest : thm
    val is_denormal : thm
    val is_double : thm
    val is_double_extended : thm
    val is_finite : thm
    val is_infinity : thm
    val is_integral : thm
    val is_nan : thm
    val is_normal : thm
    val is_single : thm
    val is_single_extended : thm
    val is_valid : thm
    val is_zero : thm
    val largest : thm
    val minus : thm
    val minus_infinity : thm
    val minus_zero : thm
    val plus_infinity : thm
    val plus_zero : thm
    val rem : thm
    val round_def : thm
    val roundmode_BIJ : thm
    val roundmode_TY_DEF : thm
    val roundmode_case : thm
    val roundmode_size_def : thm
    val sign : thm
    val some_nan : thm
    val threshold : thm
    val topfloat : thm
    val ulp : thm
    val valof : thm
    val wordlength : thm
    val zerosign : thm
  
  (*  Theorems  *)
    val ccode2num_11 : thm
    val ccode2num_ONTO : thm
    val ccode2num_num2ccode : thm
    val ccode2num_thm : thm
    val ccode_Axiom : thm
    val ccode_EQ_ccode : thm
    val ccode_case_cong : thm
    val ccode_case_def : thm
    val ccode_distinct : thm
    val ccode_induction : thm
    val ccode_nchotomy : thm
    val datatype_ccode : thm
    val datatype_roundmode : thm
    val num2ccode_11 : thm
    val num2ccode_ONTO : thm
    val num2ccode_ccode2num : thm
    val num2ccode_thm : thm
    val num2roundmode_11 : thm
    val num2roundmode_ONTO : thm
    val num2roundmode_roundmode2num : thm
    val num2roundmode_thm : thm
    val roundmode2num_11 : thm
    val roundmode2num_ONTO : thm
    val roundmode2num_num2roundmode : thm
    val roundmode2num_thm : thm
    val roundmode_Axiom : thm
    val roundmode_EQ_roundmode : thm
    val roundmode_case_cong : thm
    val roundmode_case_def : thm
    val roundmode_distinct : thm
    val roundmode_induction : thm
    val roundmode_nchotomy : thm
  
  val ieee_grammars : type_grammar.grammar * term_grammar.grammar
  
  
(*
   [transc] Parent theory of "ieee"
   
   [Eq]  Definition
      
      |- Eq = num2ccode 2
   
   [Exponent]  Definition
      
      |- !a. Exponent a = exponent (defloat a)
   
   [Finite]  Definition
      
      |- !a. Finite a <=> Isnormal a \/ Isdenormal a \/ Iszero a
   
   [Float]  Definition
      
      |- !x. Float x = float (round float_format To_nearest x)
   
   [Fraction]  Definition
      
      |- !a. Fraction a = fraction (defloat a)
   
   [Gt]  Definition
      
      |- Gt = num2ccode 0
   
   [Infinity]  Definition
      
      |- !a. Infinity a <=> is_infinity float_format (defloat a)
   
   [Isdenormal]  Definition
      
      |- !a. Isdenormal a <=> is_denormal float_format (defloat a)
   
   [Isintegral]  Definition
      
      |- !a. Isintegral a <=> is_integral float_format (defloat a)
   
   [Isnan]  Definition
      
      |- !a. Isnan a <=> is_nan float_format (defloat a)
   
   [Isnormal]  Definition
      
      |- !a. Isnormal a <=> is_normal float_format (defloat a)
   
   [Iszero]  Definition
      
      |- !a. Iszero a <=> is_zero float_format (defloat a)
   
   [Lt]  Definition
      
      |- Lt = num2ccode 1
   
   [Minus_infinity]  Definition
      
      |- Minus_infinity = float (minus_infinity float_format)
   
   [Minus_zero]  Definition
      
      |- Minus_zero = float (minus_zero float_format)
   
   [Plus_infinity]  Definition
      
      |- Plus_infinity = float (plus_infinity float_format)
   
   [Plus_zero]  Definition
      
      |- Plus_zero = float (plus_zero float_format)
   
   [ROUNDFLOAT]  Definition
      
      |- !a.
           ROUNDFLOAT a =
           float (fintrnd float_format To_nearest (defloat a))
   
   [Sign]  Definition
      
      |- !a. Sign a = sign (defloat a)
   
   [To_nearest]  Definition
      
      |- To_nearest = num2roundmode 0
   
   [To_ninfinity]  Definition
      
      |- To_ninfinity = num2roundmode 3
   
   [To_pinfinity]  Definition
      
      |- To_pinfinity = num2roundmode 2
   
   [Ulp]  Definition
      
      |- !a. Ulp a = ulp float_format (defloat a)
   
   [Un]  Definition
      
      |- Un = num2ccode 3
   
   [Val]  Definition
      
      |- !a. Val a = valof float_format (defloat a)
   
   [bias]  Definition
      
      |- !X. bias X = 2 ** (expwidth X - 1) - 1
   
   [bottomfloat]  Definition
      
      |- !X. bottomfloat X = (1,emax X - 1,2 ** fracwidth X - 1)
   
   [ccode_BIJ]  Definition
      
      |- (!a. num2ccode (ccode2num a) = a) /\
         !r. (\n. n < 4) r <=> (ccode2num (num2ccode r) = r)
   
   [ccode_TY_DEF]  Definition
      
      |- ?rep. TYPE_DEFINITION (\n. n < 4) rep
   
   [ccode_case]  Definition
      
      |- !v0 v1 v2 v3 x.
           (case x of Gt -> v0 || Lt -> v1 || Eq -> v2 || Un -> v3) =
           (\m.
              if m < 1 then
                v0
              else
                if m < 2 then v1 else if m = 2 then v2 else v3)
             (ccode2num x)
   
   [ccode_size_def]  Definition
      
      |- !x. ccode_size x = 0
   
   [closest]  Definition
      
      |- !v p s x.
           closest v p s x =
           @a.
             is_closest v s x a /\
             ((?b. is_closest v s x b /\ p b) ==> p a)
   
   [emax]  Definition
      
      |- !X. emax X = 2 ** expwidth X - 1
   
   [encoding]  Definition
      
      |- !X s e f.
           encoding X (s,e,f) =
           s * 2 ** (wordlength X - 1) + e * 2 ** fracwidth X + f
   
   [exponent]  Definition
      
      |- !s e f. exponent (s,e,f) = e
   
   [expwidth]  Definition
      
      |- !ew fw. expwidth (ew,fw) = ew
   
   [fadd]  Definition
      
      |- !X m a b.
           fadd X m a b =
           if
             is_nan X a \/ is_nan X b \/
             is_infinity X a /\ is_infinity X b /\ sign a <> sign b
           then
             some_nan X
           else
             if is_infinity X a then
               a
             else
               if is_infinity X b then
                 b
               else
                 zerosign X
                   (if is_zero X a /\ is_zero X b /\ (sign a = sign b) then
                      sign a
                    else
                      if m = To_ninfinity then 1 else 0)
                   (round X m (valof X a + valof X b))
   
   [fcompare]  Definition
      
      |- !X a b.
           fcompare X a b =
           if is_nan X a \/ is_nan X b then
             Un
           else
             if is_infinity X a /\ (sign a = 1) then
               if is_infinity X b /\ (sign b = 1) then Eq else Lt
             else
               if is_infinity X a /\ (sign a = 0) then
                 if is_infinity X b /\ (sign b = 0) then Eq else Gt
               else
                 if is_infinity X b /\ (sign b = 1) then
                   Gt
                 else
                   if is_infinity X b /\ (sign b = 0) then
                     Lt
                   else
                     if valof X a < valof X b then
                       Lt
                     else
                       if valof X a = valof X b then Eq else Gt
   
   [fdiv]  Definition
      
      |- !X m a b.
           fdiv X m a b =
           if
             is_nan X a \/ is_nan X b \/ is_zero X a /\ is_zero X b \/
             is_infinity X a /\ is_infinity X b
           then
             some_nan X
           else
             if is_infinity X a \/ is_zero X b then
               if sign a = sign b then
                 plus_infinity X
               else
                 minus_infinity X
             else
               if is_infinity X b then
                 if sign a = sign b then plus_zero X else minus_zero X
               else
                 zerosign X (if sign a = sign b then 0 else 1)
                   (round X m (valof X a / valof X b))
   
   [feq]  Definition
      
      |- !X a b. feq X a b <=> (fcompare X a b = Eq)
   
   [fge]  Definition
      
      |- !X a b.
           fge X a b <=> (fcompare X a b = Gt) \/ (fcompare X a b = Eq)
   
   [fgt]  Definition
      
      |- !X a b. fgt X a b <=> (fcompare X a b = Gt)
   
   [fintrnd]  Definition
      
      |- !X m a.
           fintrnd X m a =
           if is_nan X a then
             some_nan X
           else
             if is_infinity X a then
               a
             else
               zerosign X (sign a) (intround X m (valof X a))
   
   [fle]  Definition
      
      |- !X a b.
           fle X a b <=> (fcompare X a b = Lt) \/ (fcompare X a b = Eq)
   
   [float_TY_DEF]  Definition
      
      |- ?rep. TYPE_DEFINITION (is_valid float_format) rep
   
   [float_To_zero]  Definition
      
      |- float_To_zero = num2roundmode 1
   
   [float_abs]  Definition
      
      |- !a. float_abs a = if a >= Plus_zero then a else ~a
   
   [float_add]  Definition
      
      |- !a b.
           a + b =
           float (fadd float_format To_nearest (defloat a) (defloat b))
   
   [float_div]  Definition
      
      |- !a b.
           a / b =
           float (fdiv float_format To_nearest (defloat a) (defloat b))
   
   [float_eq]  Definition
      
      |- !a b. a == b <=> feq float_format (defloat a) (defloat b)
   
   [float_format]  Definition
      
      |- float_format = (8,23)
   
   [float_ge]  Definition
      
      |- !a b. a >= b <=> fge float_format (defloat a) (defloat b)
   
   [float_gt]  Definition
      
      |- !a b. a > b <=> fgt float_format (defloat a) (defloat b)
   
   [float_le]  Definition
      
      |- !a b. a <= b <=> fle float_format (defloat a) (defloat b)
   
   [float_lt]  Definition
      
      |- !a b. a < b <=> flt float_format (defloat a) (defloat b)
   
   [float_mul]  Definition
      
      |- !a b.
           a * b =
           float (fmul float_format To_nearest (defloat a) (defloat b))
   
   [float_neg]  Definition
      
      |- !a. ~a = float (fneg float_format To_nearest (defloat a))
   
   [float_rem]  Definition
      
      |- !a b.
           a float_rem b =
           float (frem float_format To_nearest (defloat a) (defloat b))
   
   [float_sqrt]  Definition
      
      |- !a.
           float_sqrt a = float (fsqrt float_format To_nearest (defloat a))
   
   [float_sub]  Definition
      
      |- !a b.
           a - b =
           float (fsub float_format To_nearest (defloat a) (defloat b))
   
   [float_tybij]  Definition
      
      |- (!a. float (defloat a) = a) /\
         !r. is_valid float_format r <=> (defloat (float r) = r)
   
   [flt]  Definition
      
      |- !X a b. flt X a b <=> (fcompare X a b = Lt)
   
   [fmul]  Definition
      
      |- !X m a b.
           fmul X m a b =
           if
             is_nan X a \/ is_nan X b \/ is_zero X a /\ is_infinity X b \/
             is_infinity X a /\ is_zero X b
           then
             some_nan X
           else
             if is_infinity X a \/ is_infinity X b then
               if sign a = sign b then
                 plus_infinity X
               else
                 minus_infinity X
             else
               zerosign X (if sign a = sign b then 0 else 1)
                 (round X m (valof X a * valof X b))
   
   [fneg]  Definition
      
      |- !X m a. fneg X m a = (1 - sign a,exponent a,fraction a)
   
   [fraction]  Definition
      
      |- !s e f. fraction (s,e,f) = f
   
   [fracwidth]  Definition
      
      |- !ew fw. fracwidth (ew,fw) = fw
   
   [frem]  Definition
      
      |- !X m a b.
           frem X m a b =
           if
             is_nan X a \/ is_nan X b \/ is_infinity X a \/ is_zero X b
           then
             some_nan X
           else
             if is_infinity X b then
               a
             else
               zerosign X (sign a) (round X m (valof X a rem valof X b))
   
   [fsqrt]  Definition
      
      |- !X m a.
           fsqrt X m a =
           if is_nan X a then
             some_nan X
           else
             if is_zero X a \/ is_infinity X a /\ (sign a = 0) then
               a
             else
               if sign a = 1 then
                 some_nan X
               else
                 zerosign X (sign a) (round X m (sqrt (valof X a)))
   
   [fsub]  Definition
      
      |- !X m a b.
           fsub X m a b =
           if
             is_nan X a \/ is_nan X b \/
             is_infinity X a /\ is_infinity X b /\ (sign a = sign b)
           then
             some_nan X
           else
             if is_infinity X a then
               a
             else
               if is_infinity X b then
                 minus X b
               else
                 zerosign X
                   (if is_zero X a /\ is_zero X b /\ sign a <> sign b then
                      sign a
                    else
                      if m = To_ninfinity then 1 else 0)
                   (round X m (valof X a - valof X b))
   
   [intround_def]  Definition
      
      |- (!X x.
            intround X To_nearest x =
            if x <= -threshold X then
              minus_infinity X
            else
              if x >= threshold X then
                plus_infinity X
              else
                closest (valof X)
                  (\a. ?n. EVEN n /\ (abs (valof X a) = &n))
                  {a | is_integral X a} x) /\
         (!X x.
            intround X float_To_zero x =
            if x < -largest X then
              bottomfloat X
            else
              if x > largest X then
                topfloat X
              else
                closest (valof X) (\x. T)
                  {a | is_integral X a /\ abs (valof X a) <= abs x} x) /\
         (!X x.
            intround X To_pinfinity x =
            if x < -largest X then
              bottomfloat X
            else
              if x > largest X then
                plus_infinity X
              else
                closest (valof X) (\x. T)
                  {a | is_integral X a /\ valof X a >= x} x) /\
         !X x.
           intround X To_ninfinity x =
           if x < -largest X then
             minus_infinity X
           else
             if x > largest X then
               topfloat X
             else
               closest (valof X) (\x. T)
                 {a | is_integral X a /\ valof X a <= x} x
   
   [is_closest]  Definition
      
      |- !v s x a.
           is_closest v s x a <=>
           a IN s /\ !b. b IN s ==> abs (v a - x) <= abs (v b - x)
   
   [is_denormal]  Definition
      
      |- !X a. is_denormal X a <=> (exponent a = 0) /\ fraction a <> 0
   
   [is_double]  Definition
      
      |- !X. is_double X <=> (expwidth X = 11) /\ (wordlength X = 64)
   
   [is_double_extended]  Definition
      
      |- !X.
           is_double_extended X <=> expwidth X >= 15 /\ wordlength X >= 79
   
   [is_finite]  Definition
      
      |- !X a.
           is_finite X a <=>
           is_valid X a /\
           (is_normal X a \/ is_denormal X a \/ is_zero X a)
   
   [is_infinity]  Definition
      
      |- !X a.
           is_infinity X a <=> (exponent a = emax X) /\ (fraction a = 0)
   
   [is_integral]  Definition
      
      |- !X a.
           is_integral X a <=> is_finite X a /\ ?n. abs (valof X a) = &n
   
   [is_nan]  Definition
      
      |- !X a. is_nan X a <=> (exponent a = emax X) /\ fraction a <> 0
   
   [is_normal]  Definition
      
      |- !X a. is_normal X a <=> 0 < exponent a /\ exponent a < emax X
   
   [is_single]  Definition
      
      |- !X. is_single X <=> (expwidth X = 8) /\ (wordlength X = 32)
   
   [is_single_extended]  Definition
      
      |- !X.
           is_single_extended X <=> expwidth X >= 11 /\ wordlength X >= 43
   
   [is_valid]  Definition
      
      |- !X s e f.
           is_valid X (s,e,f) <=>
           s < SUC (SUC 0) /\ e < 2 ** expwidth X /\ f < 2 ** fracwidth X
   
   [is_zero]  Definition
      
      |- !X a. is_zero X a <=> (exponent a = 0) /\ (fraction a = 0)
   
   [largest]  Definition
      
      |- !X.
           largest X =
           2 pow (emax X - 1) / 2 pow bias X *
           (2 - inv (2 pow fracwidth X))
   
   [minus]  Definition
      
      |- !X a. minus X a = (1 - sign a,exponent a,fraction a)
   
   [minus_infinity]  Definition
      
      |- !X. minus_infinity X = (1,emax X,0)
   
   [minus_zero]  Definition
      
      |- !X. minus_zero X = (1,0,0)
   
   [plus_infinity]  Definition
      
      |- !X. plus_infinity X = (0,emax X,0)
   
   [plus_zero]  Definition
      
      |- !X. plus_zero X = (0,0,0)
   
   [rem]  Definition
      
      |- !x y.
           x rem y =
           (let n =
                  closest I (\x. ?n. EVEN n /\ (abs x = &n))
                    {x | ?n. abs x = &n} (x / y)
            in
              x - n * y)
   
   [round_def]  Definition
      
      |- (!X x.
            round X To_nearest x =
            if x <= -threshold X then
              minus_infinity X
            else
              if x >= threshold X then
                plus_infinity X
              else
                closest (valof X) (\a. EVEN (fraction a))
                  {a | is_finite X a} x) /\
         (!X x.
            round X float_To_zero x =
            if x < -largest X then
              bottomfloat X
            else
              if x > largest X then
                topfloat X
              else
                closest (valof X) (\x. T)
                  {a | is_finite X a /\ abs (valof X a) <= abs x} x) /\
         (!X x.
            round X To_pinfinity x =
            if x < -largest X then
              bottomfloat X
            else
              if x > largest X then
                plus_infinity X
              else
                closest (valof X) (\x. T)
                  {a | is_finite X a /\ valof X a >= x} x) /\
         !X x.
           round X To_ninfinity x =
           if x < -largest X then
             minus_infinity X
           else
             if x > largest X then
               topfloat X
             else
               closest (valof X) (\x. T)
                 {a | is_finite X a /\ valof X a <= x} x
   
   [roundmode_BIJ]  Definition
      
      |- (!a. num2roundmode (roundmode2num a) = a) /\
         !r. (\n. n < 4) r <=> (roundmode2num (num2roundmode r) = r)
   
   [roundmode_TY_DEF]  Definition
      
      |- ?rep. TYPE_DEFINITION (\n. n < 4) rep
   
   [roundmode_case]  Definition
      
      |- !v0 v1 v2 v3 x.
           (case x of
               To_nearest -> v0
            || float_To_zero -> v1
            || To_pinfinity -> v2
            || To_ninfinity -> v3) =
           (\m.
              if m < 1 then
                v0
              else
                if m < 2 then v1 else if m = 2 then v2 else v3)
             (roundmode2num x)
   
   [roundmode_size_def]  Definition
      
      |- !x. roundmode_size x = 0
   
   [sign]  Definition
      
      |- !s e f. sign (s,e,f) = s
   
   [some_nan]  Definition
      
      |- !X. some_nan X = @a. is_nan X a
   
   [threshold]  Definition
      
      |- !X.
           threshold X =
           2 pow (emax X - 1) / 2 pow bias X *
           (2 - inv (2 pow SUC (fracwidth X)))
   
   [topfloat]  Definition
      
      |- !X. topfloat X = (0,emax X - 1,2 ** fracwidth X - 1)
   
   [ulp]  Definition
      
      |- !X a.
           ulp X a = valof X (0,exponent a,1) - valof X (0,exponent a,0)
   
   [valof]  Definition
      
      |- !X s e f.
           valof X (s,e,f) =
           if e = 0 then
             -1 pow s * (2 / 2 pow bias X) * (&f / 2 pow fracwidth X)
           else
             -1 pow s * (2 pow e / 2 pow bias X) *
             (1 + &f / 2 pow fracwidth X)
   
   [wordlength]  Definition
      
      |- !X. wordlength X = expwidth X + fracwidth X + 1
   
   [zerosign]  Definition
      
      |- !X s a.
           zerosign X s a =
           if is_zero X a then
             if s = 0 then plus_zero X else minus_zero X
           else
             a
   
   [ccode2num_11]  Theorem
      
      |- !a a'. (ccode2num a = ccode2num a') <=> (a = a')
   
   [ccode2num_ONTO]  Theorem
      
      |- !r. r < 4 <=> ?a. r = ccode2num a
   
   [ccode2num_num2ccode]  Theorem
      
      |- !r. r < 4 <=> (ccode2num (num2ccode r) = r)
   
   [ccode2num_thm]  Theorem
      
      |- (ccode2num Gt = 0) /\ (ccode2num Lt = 1) /\ (ccode2num Eq = 2) /\
         (ccode2num Un = 3)
   
   [ccode_Axiom]  Theorem
      
      |- !x0 x1 x2 x3.
           ?f. (f Gt = x0) /\ (f Lt = x1) /\ (f Eq = x2) /\ (f Un = x3)
   
   [ccode_EQ_ccode]  Theorem
      
      |- !a a'. (a = a') <=> (ccode2num a = ccode2num a')
   
   [ccode_case_cong]  Theorem
      
      |- !M M' v0 v1 v2 v3.
           (M = M') /\ ((M' = Gt) ==> (v0 = v0')) /\
           ((M' = Lt) ==> (v1 = v1')) /\ ((M' = Eq) ==> (v2 = v2')) /\
           ((M' = Un) ==> (v3 = v3')) ==>
           ((case M of Gt -> v0 || Lt -> v1 || Eq -> v2 || Un -> v3) =
            case M' of Gt -> v0' || Lt -> v1' || Eq -> v2' || Un -> v3')
   
   [ccode_case_def]  Theorem
      
      |- (!v0 v1 v2 v3.
            (case Gt of Gt -> v0 || Lt -> v1 || Eq -> v2 || Un -> v3) =
            v0) /\
         (!v0 v1 v2 v3.
            (case Lt of Gt -> v0 || Lt -> v1 || Eq -> v2 || Un -> v3) =
            v1) /\
         (!v0 v1 v2 v3.
            (case Eq of Gt -> v0 || Lt -> v1 || Eq -> v2 || Un -> v3) =
            v2) /\
         !v0 v1 v2 v3.
           (case Un of Gt -> v0 || Lt -> v1 || Eq -> v2 || Un -> v3) = v3
   
   [ccode_distinct]  Theorem
      
      |- Gt <> Lt /\ Gt <> Eq /\ Gt <> Un /\ Lt <> Eq /\ Lt <> Un /\
         Eq <> Un
   
   [ccode_induction]  Theorem
      
      |- !P. P Eq /\ P Gt /\ P Lt /\ P Un ==> !a. P a
   
   [ccode_nchotomy]  Theorem
      
      |- !a. (a = Gt) \/ (a = Lt) \/ (a = Eq) \/ (a = Un)
   
   [datatype_ccode]  Theorem
      
      |- DATATYPE (ccode Gt Lt Eq Un)
   
   [datatype_roundmode]  Theorem
      
      |- DATATYPE
           (roundmode To_nearest float_To_zero To_pinfinity To_ninfinity)
   
   [num2ccode_11]  Theorem
      
      |- !r r'.
           r < 4 ==> r' < 4 ==> ((num2ccode r = num2ccode r') <=> (r = r'))
   
   [num2ccode_ONTO]  Theorem
      
      |- !a. ?r. (a = num2ccode r) /\ r < 4
   
   [num2ccode_ccode2num]  Theorem
      
      |- !a. num2ccode (ccode2num a) = a
   
   [num2ccode_thm]  Theorem
      
      |- (num2ccode 0 = Gt) /\ (num2ccode 1 = Lt) /\ (num2ccode 2 = Eq) /\
         (num2ccode 3 = Un)
   
   [num2roundmode_11]  Theorem
      
      |- !r r'.
           r < 4 ==>
           r' < 4 ==>
           ((num2roundmode r = num2roundmode r') <=> (r = r'))
   
   [num2roundmode_ONTO]  Theorem
      
      |- !a. ?r. (a = num2roundmode r) /\ r < 4
   
   [num2roundmode_roundmode2num]  Theorem
      
      |- !a. num2roundmode (roundmode2num a) = a
   
   [num2roundmode_thm]  Theorem
      
      |- (num2roundmode 0 = To_nearest) /\
         (num2roundmode 1 = float_To_zero) /\
         (num2roundmode 2 = To_pinfinity) /\
         (num2roundmode 3 = To_ninfinity)
   
   [roundmode2num_11]  Theorem
      
      |- !a a'. (roundmode2num a = roundmode2num a') <=> (a = a')
   
   [roundmode2num_ONTO]  Theorem
      
      |- !r. r < 4 <=> ?a. r = roundmode2num a
   
   [roundmode2num_num2roundmode]  Theorem
      
      |- !r. r < 4 <=> (roundmode2num (num2roundmode r) = r)
   
   [roundmode2num_thm]  Theorem
      
      |- (roundmode2num To_nearest = 0) /\
         (roundmode2num float_To_zero = 1) /\
         (roundmode2num To_pinfinity = 2) /\
         (roundmode2num To_ninfinity = 3)
   
   [roundmode_Axiom]  Theorem
      
      |- !x0 x1 x2 x3.
           ?f.
             (f To_nearest = x0) /\ (f float_To_zero = x1) /\
             (f To_pinfinity = x2) /\ (f To_ninfinity = x3)
   
   [roundmode_EQ_roundmode]  Theorem
      
      |- !a a'. (a = a') <=> (roundmode2num a = roundmode2num a')
   
   [roundmode_case_cong]  Theorem
      
      |- !M M' v0 v1 v2 v3.
           (M = M') /\ ((M' = To_nearest) ==> (v0 = v0')) /\
           ((M' = float_To_zero) ==> (v1 = v1')) /\
           ((M' = To_pinfinity) ==> (v2 = v2')) /\
           ((M' = To_ninfinity) ==> (v3 = v3')) ==>
           ((case M of
                To_nearest -> v0
             || float_To_zero -> v1
             || To_pinfinity -> v2
             || To_ninfinity -> v3) =
            case M' of
               To_nearest -> v0'
            || float_To_zero -> v1'
            || To_pinfinity -> v2'
            || To_ninfinity -> v3')
   
   [roundmode_case_def]  Theorem
      
      |- (!v0 v1 v2 v3.
            (case To_nearest of
                To_nearest -> v0
             || float_To_zero -> v1
             || To_pinfinity -> v2
             || To_ninfinity -> v3) =
            v0) /\
         (!v0 v1 v2 v3.
            (case float_To_zero of
                To_nearest -> v0
             || float_To_zero -> v1
             || To_pinfinity -> v2
             || To_ninfinity -> v3) =
            v1) /\
         (!v0 v1 v2 v3.
            (case To_pinfinity of
                To_nearest -> v0
             || float_To_zero -> v1
             || To_pinfinity -> v2
             || To_ninfinity -> v3) =
            v2) /\
         !v0 v1 v2 v3.
           (case To_ninfinity of
               To_nearest -> v0
            || float_To_zero -> v1
            || To_pinfinity -> v2
            || To_ninfinity -> v3) =
           v3
   
   [roundmode_distinct]  Theorem
      
      |- To_nearest <> float_To_zero /\ To_nearest <> To_pinfinity /\
         To_nearest <> To_ninfinity /\ float_To_zero <> To_pinfinity /\
         float_To_zero <> To_ninfinity /\ To_pinfinity <> To_ninfinity
   
   [roundmode_induction]  Theorem
      
      |- !P.
           P To_nearest /\ P To_ninfinity /\ P To_pinfinity /\
           P float_To_zero ==>
           !a. P a
   
   [roundmode_nchotomy]  Theorem
      
      |- !a.
           (a = To_nearest) \/ (a = float_To_zero) \/ (a = To_pinfinity) \/
           (a = To_ninfinity)
   
   
*)
end
