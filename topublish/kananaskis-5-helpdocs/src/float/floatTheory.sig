signature floatTheory =
sig
  type thm = Thm.thm
  
  (*  Definitions  *)
    val error_def : thm
    val normalizes : thm
  
  (*  Theorems  *)
    val ADD_SUB2 : thm
    val BOUND_AT_WORST_LEMMA : thm
    val CLOSEST_IN_SET : thm
    val CLOSEST_IS_CLOSEST : thm
    val CLOSEST_IS_EVERYTHING : thm
    val DEFLOAT_FLOAT_ROUND : thm
    val DEFLOAT_FLOAT_ZEROSIGN_ROUND : thm
    val DEFLOAT_FLOAT_ZEROSIGN_ROUND_FINITE : thm
    val ERROR_AT_WORST_LEMMA : thm
    val ERROR_BOUND_BIG : thm
    val ERROR_BOUND_BIG1 : thm
    val ERROR_BOUND_LEMMA1 : thm
    val ERROR_BOUND_LEMMA2 : thm
    val ERROR_BOUND_LEMMA3 : thm
    val ERROR_BOUND_LEMMA4 : thm
    val ERROR_BOUND_LEMMA5 : thm
    val ERROR_BOUND_LEMMA6 : thm
    val ERROR_BOUND_LEMMA7 : thm
    val ERROR_BOUND_LEMMA8 : thm
    val ERROR_BOUND_NORM_STRONG : thm
    val ERROR_BOUND_NORM_STRONG_NORMALIZE : thm
    val ERROR_BOUND_SMALL : thm
    val ERROR_BOUND_SMALL1 : thm
    val ERROR_BOUND_TINY : thm
    val ERROR_IS_ZERO : thm
    val EXPONENT : thm
    val EXP_GT_ZERO : thm
    val EXP_LT_0 : thm
    val FINITE_R3 : thm
    val FLOAT_ADD : thm
    val FLOAT_ADD_RELATIVE : thm
    val FLOAT_CASES : thm
    val FLOAT_CASES_FINITE : thm
    val FLOAT_COUNTINDUCT : thm
    val FLOAT_DISTINCT : thm
    val FLOAT_DISTINCT_FINITE : thm
    val FLOAT_DIV : thm
    val FLOAT_DIV_RELATIVE : thm
    val FLOAT_EQ : thm
    val FLOAT_EQ_REFL : thm
    val FLOAT_FINITECOUNT : thm
    val FLOAT_FIRSTCROSS : thm
    val FLOAT_FIRSTCROSS1 : thm
    val FLOAT_FIRSTCROSS2 : thm
    val FLOAT_FIRSTCROSS3 : thm
    val FLOAT_GE : thm
    val FLOAT_GT : thm
    val FLOAT_INFINITES_DISTINCT : thm
    val FLOAT_INFINITIES : thm
    val FLOAT_INFINITIES_SIGNED : thm
    val FLOAT_IS_FINITE_SUBSET : thm
    val FLOAT_LE : thm
    val FLOAT_LT : thm
    val FLOAT_MUL : thm
    val FLOAT_MUL_FINITE : thm
    val FLOAT_MUL_RELATIVE : thm
    val FLOAT_SUB : thm
    val FLOAT_SUB_FINITE : thm
    val FLOAT_SUB_RELATIVE : thm
    val FLOAT_THRESHOLD_EXPLICIT : thm
    val FRACTION : thm
    val INFINITY_IS_INFINITY : thm
    val INFINITY_NOT_NAN : thm
    val ISFINITE : thm
    val ISFINITE_LEMMA : thm
    val IS_CLOSEST_EXISTS : thm
    val IS_FINITE_ALT : thm
    val IS_FINITE_ALT1 : thm
    val IS_FINITE_CLOSEST : thm
    val IS_FINITE_EXPLICIT : thm
    val IS_FINITE_FINITE : thm
    val IS_FINITE_NONEMPTY : thm
    val IS_VALID : thm
    val IS_VALID_CLOSEST : thm
    val IS_VALID_DEFLOAT : thm
    val IS_VALID_FINITE : thm
    val IS_VALID_NONEMPTY : thm
    val IS_VALID_ROUND : thm
    val IS_VALID_SPECIAL : thm
    val LT_SUC_LE : thm
    val LT_THRESHOLD_LT_POW_INV : thm
    val MATCH_FLOAT_FINITE : thm
    val REAL_ABS_DIV : thm
    val REAL_ABS_INV : thm
    val REAL_ABS_NUM : thm
    val REAL_ABS_POW : thm
    val REAL_IN_BINADE : thm
    val REAL_LE_INV2 : thm
    val REAL_LE_LCANCEL_IMP : thm
    val REAL_LE_RCANCEL_IMP : thm
    val REAL_LT_LCANCEL_IMP : thm
    val REAL_LT_RCANCEL_IMP : thm
    val REAL_MUL_AC : thm
    val REAL_NEG_IN_BINADE : thm
    val REAL_OF_NUM_LT : thm
    val REAL_OF_NUM_POW : thm
    val REAL_OF_NUM_SUB : thm
    val REAL_POS_IN_BINADE : thm
    val REAL_POW_EQ_0 : thm
    val REAL_POW_LE_1 : thm
    val REAL_POW_MONO : thm
    val RELATIVE_ERROR : thm
    val RELATIVE_ERROR_NEG : thm
    val RELATIVE_ERROR_POS : thm
    val RELATIVE_ERROR_ZERO : thm
    val RRRC1 : thm
    val RRRC10 : thm
    val RRRC11 : thm
    val RRRC2 : thm
    val RRRC3 : thm
    val RRRC4 : thm
    val RRRC5 : thm
    val RRRC6 : thm
    val RRRC7 : thm
    val RRRC8 : thm
    val RRRC9 : thm
    val SIGN : thm
    val THRESHOLD_LT_POW_INV : thm
    val THRESHOLD_MUL_LT : thm
    val TWO_EXP_GE_1 : thm
    val VALOF : thm
    val VALOF_DEFLOAT_FLOAT_ZEROSIGN_ROUND : thm
    val VALOF_SCALE_DOWN : thm
    val VALOF_SCALE_UP : thm
    val VAL_FINITE : thm
    val VAL_THRESHOLD : thm
    val Val_FLOAT_ROUND_VALOF : thm
    val ZERO_IS_ZERO : thm
    val ZERO_NOT_NAN : thm
    val egt1 : thm
    val egtff : thm
    val ftt : thm
    val inv23gt0 : thm
    val lt1eqmul : thm
    val not2eqz : thm
    val noteteeszegtz : thm
    val sucminmullt : thm
    val temonz : thm
    val tfflttfs : thm
    val tittfittt : thm
    val tpetfs : thm
    val tptteteesze : thm
    val tteettto : thm
    val ttpinv : thm
    val twogz : thm
    val v127not0 : thm
    val v23not0 : thm
  
  val float_grammars : type_grammar.grammar * term_grammar.grammar
  
  
(*
   [ieee] Parent theory of "float"
   
   [error_def]  Definition
      
      |- !x. error x = Val (float (round float_format To_nearest x)) - x
   
   [normalizes]  Definition
      
      |- !x.
           normalizes x <=>
           inv (2 pow (bias float_format - 1)) <= abs x /\
           abs x < threshold float_format
   
   [ADD_SUB2]  Theorem
      
      |- !m n. m + n - m = n
   
   [BOUND_AT_WORST_LEMMA]  Theorem
      
      |- !a x.
           abs x < threshold float_format /\ is_finite float_format a ==>
           abs
             (valof float_format (round float_format To_nearest x) - x) <=
           abs (valof float_format a - x)
   
   [CLOSEST_IN_SET]  Theorem
      
      |- !v p x s. FINITE s ==> s <> {} ==> closest v p s x IN s
   
   [CLOSEST_IS_CLOSEST]  Theorem
      
      |- !v p x s.
           FINITE s ==> s <> {} ==> is_closest v s x (closest v p s x)
   
   [CLOSEST_IS_EVERYTHING]  Theorem
      
      |- !v p s x.
           FINITE s ==>
           s <> {} ==>
           is_closest v s x (closest v p s x) /\
           ((?b. is_closest v s x b /\ p b) ==> p (closest v p s x))
   
   [DEFLOAT_FLOAT_ROUND]  Theorem
      
      |- !X x.
           defloat (float (round float_format To_nearest x)) =
           round float_format To_nearest x
   
   [DEFLOAT_FLOAT_ZEROSIGN_ROUND]  Theorem
      
      |- !x b.
           defloat
             (float
                (zerosign float_format b
                   (round float_format To_nearest x))) =
           zerosign float_format b (round float_format To_nearest x)
   
   [DEFLOAT_FLOAT_ZEROSIGN_ROUND_FINITE]  Theorem
      
      |- !b x.
           abs x < threshold float_format ==>
           is_finite float_format
             (defloat
                (float
                   (zerosign float_format b
                      (round float_format To_nearest x))))
   
   [ERROR_AT_WORST_LEMMA]  Theorem
      
      |- !a x.
           abs x < threshold float_format /\ Finite a ==>
           abs (error x) <= abs (Val a - x)
   
   [ERROR_BOUND_BIG]  Theorem
      
      |- !k x.
           2 pow k <= abs x /\ abs x < 2 pow SUC k /\
           abs x < threshold float_format ==>
           abs (error x) <= 2 pow k / 2 pow 24
   
   [ERROR_BOUND_BIG1]  Theorem
      
      |- !x k.
           2 pow k <= abs x /\ abs x < 2 pow SUC k /\
           abs x < threshold float_format ==>
           ?a. Finite a /\ abs (Val a - x) <= 2 pow k / 2 pow 24
   
   [ERROR_BOUND_LEMMA1]  Theorem
      
      |- !x.
           0 <= x /\ x < 1 ==>
           ?n. n < 2 ** 23 /\ &n / 2 pow 23 <= x /\ x < &SUC n / 2 pow 23
   
   [ERROR_BOUND_LEMMA2]  Theorem
      
      |- !x.
           0 <= x /\ x < 1 ==>
           ?n. n <= 2 ** 23 /\ abs (x - &n / 2 pow 23) <= inv (2 pow 24)
   
   [ERROR_BOUND_LEMMA3]  Theorem
      
      |- !x.
           1 <= x /\ x < 2 ==>
           ?n.
             n <= 2 ** 23 /\ abs (1 + &n / 2 pow 23 - x) <= inv (2 pow 24)
   
   [ERROR_BOUND_LEMMA4]  Theorem
      
      |- !x.
           1 <= x /\ x < 2 ==>
           ?e f.
             abs (Val (float (0,e,f)) - x) <= inv (2 pow 24) /\
             f < 2 ** 23 /\
             ((e = bias float_format) \/
              (e = SUC (bias float_format)) /\ (f = 0))
   
   [ERROR_BOUND_LEMMA5]  Theorem
      
      |- !x.
           1 <= abs x /\ abs x < 2 ==>
           ?s e f.
             abs (Val (float (s,e,f)) - x) <= inv (2 pow 24) /\ s < 2 /\
             f < 2 ** 23 /\
             ((e = bias float_format) \/
              (e = SUC (bias float_format)) /\ (f = 0))
   
   [ERROR_BOUND_LEMMA6]  Theorem
      
      |- !x.
           0 <= x /\ x < inv (2 pow 126) ==>
           ?n.
             n <= 2 ** 23 /\
             abs (x - 2 / 2 pow 127 * &n / 2 pow 23) <= inv (2 pow 150)
   
   [ERROR_BOUND_LEMMA7]  Theorem
      
      |- !x.
           0 <= x /\ x < inv (2 pow 126) ==>
           ?e f.
             abs (Val (float (0,e,f)) - x) <= inv (2 pow 150) /\
             f < 2 ** 23 /\ ((e = 0) \/ (e = 1) /\ (f = 0))
   
   [ERROR_BOUND_LEMMA8]  Theorem
      
      |- !x.
           abs x < inv (2 pow 126) ==>
           ?s e f.
             abs (Val (float (s,e,f)) - x) <= inv (2 pow 150) /\ s < 2 /\
             f < 2 ** 23 /\ ((e = 0) \/ (e = 1) /\ (f = 0))
   
   [ERROR_BOUND_NORM_STRONG]  Theorem
      
      |- !x j.
           abs x < threshold float_format /\
           abs x < 2 pow SUC j / 2 pow 126 ==>
           abs (error x) <= 2 pow j / 2 pow 150
   
   [ERROR_BOUND_NORM_STRONG_NORMALIZE]  Theorem
      
      |- !x. normalizes x ==> ?j. abs (error x) <= 2 pow j / 2 pow 150
   
   [ERROR_BOUND_SMALL]  Theorem
      
      |- !k x.
           inv (2 pow SUC k) <= abs x /\ abs x < inv (2 pow k) /\
           k < 126 ==>
           abs (error x) <= inv (2 pow SUC k * 2 pow 24)
   
   [ERROR_BOUND_SMALL1]  Theorem
      
      |- !x k.
           inv (2 pow SUC k) <= abs x /\ abs x < inv (2 pow k) /\
           k < 126 ==>
           ?a. Finite a /\ abs (Val a - x) <= inv (2 pow SUC k * 2 pow 24)
   
   [ERROR_BOUND_TINY]  Theorem
      
      |- !x. abs x < inv (2 pow 126) ==> abs (error x) <= inv (2 pow 150)
   
   [ERROR_IS_ZERO]  Theorem
      
      |- !a x. Finite a /\ (Val a = x) ==> (error x = 0)
   
   [EXPONENT]  Theorem
      
      |- !a. exponent a = FST (SND a)
   
   [EXP_GT_ZERO]  Theorem
      
      |- !n. 0 < 2 ** n
   
   [EXP_LT_0]  Theorem
      
      |- !n x. 0 < x ** n <=> x <> 0 \/ (n = 0)
   
   [FINITE_R3]  Theorem
      
      |- !m n p.
           FINITE {a | FST a < m /\ FST (SND a) < n /\ SND (SND a) < p}
   
   [FLOAT_ADD]  Theorem
      
      |- !a b.
           Finite a /\ Finite b /\
           abs (Val a + Val b) < threshold float_format ==>
           Finite (a + b)
   
   [FLOAT_ADD_RELATIVE]  Theorem
      
      |- !a b.
           Finite a /\ Finite b /\ normalizes (Val a + Val b) ==>
           Finite (a + b) /\
           ?e.
             abs e <= 1 / 2 pow 24 /\
             (Val (a + b) = (Val a + Val b) * (1 + e))
   
   [FLOAT_CASES]  Theorem
      
      |- !a.
           Isnan a \/ Infinity a \/ Isnormal a \/ Isdenormal a \/ Iszero a
   
   [FLOAT_CASES_FINITE]  Theorem
      
      |- !a. Isnan a \/ Infinity a \/ Finite a
   
   [FLOAT_COUNTINDUCT]  Theorem
      
      |- !n. ({x | x < 0} = {}) /\ ({x | x < SUC n} = n INSERT {x | x < n})
   
   [FLOAT_DISTINCT]  Theorem
      
      |- !a.
           ~(Isnan a /\ Infinity a) /\ ~(Isnan a /\ Isnormal a) /\
           ~(Isnan a /\ Isdenormal a) /\ ~(Isnan a /\ Iszero a) /\
           ~(Infinity a /\ Isnormal a) /\ ~(Infinity a /\ Isdenormal a) /\
           ~(Infinity a /\ Iszero a) /\ ~(Isnormal a /\ Isdenormal a) /\
           ~(Isnormal a /\ Iszero a) /\ ~(Isdenormal a /\ Iszero a)
   
   [FLOAT_DISTINCT_FINITE]  Theorem
      
      |- !a.
           ~(Isnan a /\ Infinity a) /\ ~(Isnan a /\ Finite a) /\
           ~(Infinity a /\ Finite a)
   
   [FLOAT_DIV]  Theorem
      
      |- !a b.
           Finite a /\ Finite b /\ ~Iszero b /\
           abs (Val a / Val b) < threshold float_format ==>
           Finite (a / b) /\
           (Val (a / b) = Val a / Val b + error (Val a / Val b))
   
   [FLOAT_DIV_RELATIVE]  Theorem
      
      |- !a b.
           Finite a /\ Finite b /\ ~Iszero b /\
           normalizes (Val a / Val b) ==>
           Finite (a / b) /\
           ?e.
             abs e <= 1 / 2 pow 24 /\
             (Val (a / b) = Val a / Val b * (1 + e))
   
   [FLOAT_EQ]  Theorem
      
      |- !a b. Finite a /\ Finite b ==> (a == b <=> (Val a = Val b))
   
   [FLOAT_EQ_REFL]  Theorem
      
      |- !a. a == a <=> ~Isnan a
   
   [FLOAT_FINITECOUNT]  Theorem
      
      |- !n. FINITE {x | x < n}
   
   [FLOAT_FIRSTCROSS]  Theorem
      
      |- !m n p.
           {a | FST a < m /\ FST (SND a) < n /\ SND (SND a) < p} =
           IMAGE (\(x,y,z). (x,y,z))
             ({x | x < m} CROSS ({y | y < n} CROSS {z | z < p}))
   
   [FLOAT_FIRSTCROSS1]  Theorem
      
      |- !x m n p.
           (?x'.
              (x = (\(x,y,z). (x,y,z)) x') /\ FST x' < m /\
              FST (SND x') < n /\ SND (SND x') < p) ==>
           FST x < m /\ FST (SND x) < n /\ SND (SND x) < p
   
   [FLOAT_FIRSTCROSS2]  Theorem
      
      |- !x m n p.
           FST x < m /\ FST (SND x) < n /\ SND (SND x) < p ==>
           ?x'.
             (x = (\(x,y,z). (x,y,z)) x') /\ FST x' < m /\
             FST (SND x') < n /\ SND (SND x') < p
   
   [FLOAT_FIRSTCROSS3]  Theorem
      
      |- !x m n p.
           FST x < m /\ FST (SND x) < n /\ SND (SND x) < p <=>
           ?x'.
             (x = (\(x,y,z). (x,y,z)) x') /\ FST x' < m /\
             FST (SND x') < n /\ SND (SND x') < p
   
   [FLOAT_GE]  Theorem
      
      |- !a b. Finite a /\ Finite b ==> (a >= b <=> Val a >= Val b)
   
   [FLOAT_GT]  Theorem
      
      |- !a b. Finite a /\ Finite b ==> (a > b <=> Val a > Val b)
   
   [FLOAT_INFINITES_DISTINCT]  Theorem
      
      |- !a. ~(a == Plus_infinity /\ a == Minus_infinity)
   
   [FLOAT_INFINITIES]  Theorem
      
      |- !a. Infinity a <=> a == Plus_infinity \/ a == Minus_infinity
   
   [FLOAT_INFINITIES_SIGNED]  Theorem
      
      |- (sign (defloat Plus_infinity) = 0) /\
         (sign (defloat Minus_infinity) = 1)
   
   [FLOAT_IS_FINITE_SUBSET]  Theorem
      
      |- !X. {a | is_finite X a} SUBSET {a | is_valid X a}
   
   [FLOAT_LE]  Theorem
      
      |- !a b. Finite a /\ Finite b ==> (a <= b <=> Val a <= Val b)
   
   [FLOAT_LT]  Theorem
      
      |- !a b. Finite a /\ Finite b ==> (a < b <=> Val a < Val b)
   
   [FLOAT_MUL]  Theorem
      
      |- !a b.
           Finite a /\ Finite b /\
           abs (Val a * Val b) < threshold float_format ==>
           Finite (a * b) /\
           (Val (a * b) = Val a * Val b + error (Val a * Val b))
   
   [FLOAT_MUL_FINITE]  Theorem
      
      |- !a b.
           Finite a /\ Finite b /\
           abs (Val a * Val b) < threshold float_format ==>
           Finite (a * b)
   
   [FLOAT_MUL_RELATIVE]  Theorem
      
      |- !a b.
           Finite a /\ Finite b /\ normalizes (Val a * Val b) ==>
           Finite (a * b) /\
           ?e.
             abs e <= 1 / 2 pow 24 /\
             (Val (a * b) = Val a * Val b * (1 + e))
   
   [FLOAT_SUB]  Theorem
      
      |- !a b.
           Finite a /\ Finite b /\
           abs (Val a - Val b) < threshold float_format ==>
           Finite (a - b) /\
           (Val (a - b) = Val a - Val b + error (Val a - Val b))
   
   [FLOAT_SUB_FINITE]  Theorem
      
      |- !a b.
           Finite a /\ Finite b /\
           abs (Val a - Val b) < threshold float_format ==>
           Finite (a - b)
   
   [FLOAT_SUB_RELATIVE]  Theorem
      
      |- !a b.
           Finite a /\ Finite b /\ normalizes (Val a - Val b) ==>
           Finite (a - b) /\
           ?e.
             abs e <= 1 / 2 pow 24 /\
             (Val (a - b) = (Val a - Val b) * (1 + e))
   
   [FLOAT_THRESHOLD_EXPLICIT]  Theorem
      
      |- threshold float_format = 340282356779733661637539395458142568448
   
   [FRACTION]  Theorem
      
      |- !a. fraction a = SND (SND a)
   
   [INFINITY_IS_INFINITY]  Theorem
      
      |- Infinity Plus_infinity /\ Infinity Minus_infinity
   
   [INFINITY_NOT_NAN]  Theorem
      
      |- ~Isnan Plus_infinity /\ ~Isnan Minus_infinity
   
   [ISFINITE]  Theorem
      
      |- !a. Finite a <=> is_finite float_format (defloat a)
   
   [ISFINITE_LEMMA]  Theorem
      
      |- !s e f.
           s < 2 /\ e < 255 /\ f < 2 ** 23 ==>
           Finite (float (s,e,f)) /\ is_valid float_format (s,e,f)
   
   [IS_CLOSEST_EXISTS]  Theorem
      
      |- !v x s. FINITE s ==> s <> {} ==> ?a. is_closest v s x a
   
   [IS_FINITE_ALT]  Theorem
      
      |- !a.
           is_finite float_format a <=>
           is_valid float_format a /\ exponent a < 255
   
   [IS_FINITE_ALT1]  Theorem
      
      |- !a.
           is_normal float_format a \/ is_denormal float_format a \/
           is_zero float_format a <=> exponent a < 255
   
   [IS_FINITE_CLOSEST]  Theorem
      
      |- !X v p x. is_finite X (closest v p {a | is_finite X a} x)
   
   [IS_FINITE_EXPLICIT]  Theorem
      
      |- !a.
           is_finite float_format a <=>
           sign a < 2 /\ exponent a < 255 /\ fraction a < 8388608
   
   [IS_FINITE_FINITE]  Theorem
      
      |- !X. FINITE {a | is_finite X a}
   
   [IS_FINITE_NONEMPTY]  Theorem
      
      |- {a | is_finite X a} <> {}
   
   [IS_VALID]  Theorem
      
      |- !X a.
           is_valid X a <=>
           sign a < 2 /\ exponent a < 2 ** expwidth X /\
           fraction a < 2 ** fracwidth X
   
   [IS_VALID_CLOSEST]  Theorem
      
      |- !X v p x. is_valid X (closest v p {a | is_finite X a} x)
   
   [IS_VALID_DEFLOAT]  Theorem
      
      |- !a. is_valid float_format (defloat a)
   
   [IS_VALID_FINITE]  Theorem
      
      |- FINITE {a | is_valid X a}
   
   [IS_VALID_NONEMPTY]  Theorem
      
      |- {a | is_valid X a} <> {}
   
   [IS_VALID_ROUND]  Theorem
      
      |- !X x. is_valid X (round X To_nearest x)
   
   [IS_VALID_SPECIAL]  Theorem
      
      |- !X.
           is_valid X (minus_infinity X) /\ is_valid X (plus_infinity X) /\
           is_valid X (topfloat X) /\ is_valid X (bottomfloat X) /\
           is_valid X (plus_zero X) /\ is_valid X (minus_zero X)
   
   [LT_SUC_LE]  Theorem
      
      |- !m n. m < SUC n <=> m <= n
   
   [LT_THRESHOLD_LT_POW_INV]  Theorem
      
      |- !x.
           x < threshold (8,23) ==> x < 2 pow (emax (8,23) - 1) / 2 pow 126
   
   [MATCH_FLOAT_FINITE]  Theorem
      
      |- !X.
           {a | is_finite X a} SUBSET {a | is_valid X a} ==>
           FINITE {a | is_finite X a}
   
   [REAL_ABS_DIV]  Theorem
      
      |- !x y. abs (x / y) = abs x / abs y
   
   [REAL_ABS_INV]  Theorem
      
      |- !x. abs (inv x) = inv (abs x)
   
   [REAL_ABS_NUM]  Theorem
      
      |- abs (&n) = &n
   
   [REAL_ABS_POW]  Theorem
      
      |- !x n. abs (x pow n) = abs x pow n
   
   [REAL_IN_BINADE]  Theorem
      
      |- !x.
           normalizes x ==>
           ?j.
             j <= emax float_format - 2 /\ 2 pow j / 2 pow 126 <= abs x /\
             abs x < 2 pow SUC j / 2 pow 126
   
   [REAL_LE_INV2]  Theorem
      
      |- !x y. 0 < x /\ x <= y ==> inv y <= inv x
   
   [REAL_LE_LCANCEL_IMP]  Theorem
      
      |- !x y z. 0 < x /\ x * y <= x * z ==> y <= z
   
   [REAL_LE_RCANCEL_IMP]  Theorem
      
      |- !x y z. 0 < z /\ x * z <= y * z ==> x <= y
   
   [REAL_LT_LCANCEL_IMP]  Theorem
      
      |- !x y z. 0 < x /\ x * y < x * z ==> y < z
   
   [REAL_LT_RCANCEL_IMP]  Theorem
      
      |- !x y z. 0 < z /\ x * z < y * z ==> x < y
   
   [REAL_MUL_AC]  Theorem
      
      |- (m * n = n * m) /\ (m * n * p = m * (n * p)) /\
         (m * (n * p) = n * (m * p))
   
   [REAL_NEG_IN_BINADE]  Theorem
      
      |- !x.
           normalizes x /\ 0 <= -x ==>
           ?j.
             j <= emax float_format - 2 /\ 2 pow j / 2 pow 126 <= -x /\
             -x < 2 pow SUC j / 2 pow 126
   
   [REAL_OF_NUM_LT]  Theorem
      
      |- !m n. &m < &n <=> m < n
   
   [REAL_OF_NUM_POW]  Theorem
      
      |- !x n. &x pow n = &(x ** n)
   
   [REAL_OF_NUM_SUB]  Theorem
      
      |- !m n. m <= n ==> (&n - &m = &(n - m))
   
   [REAL_POS_IN_BINADE]  Theorem
      
      |- !x.
           normalizes x /\ 0 <= x ==>
           ?j.
             j <= emax float_format - 2 /\ 2 pow j / 2 pow 126 <= x /\
             x < 2 pow SUC j / 2 pow 126
   
   [REAL_POW_EQ_0]  Theorem
      
      |- !x n. (x pow n = 0) <=> (x = 0) /\ n <> 0
   
   [REAL_POW_LE_1]  Theorem
      
      |- !n x. 1 <= x ==> 1 <= x pow n
   
   [REAL_POW_MONO]  Theorem
      
      |- !m n x. 1 <= x /\ m <= n ==> x pow m <= x pow n
   
   [RELATIVE_ERROR]  Theorem
      
      |- !x.
           normalizes x ==>
           ?e.
             abs e <= 1 / 2 pow 24 /\
             (Val (float (round float_format To_nearest x)) = x * (1 + e))
   
   [RELATIVE_ERROR_NEG]  Theorem
      
      |- !x.
           normalizes x /\ x < 0 ==>
           ?e.
             abs e <= 1 / 2 pow 24 /\
             (Val (float (round float_format To_nearest x)) = x * (1 + e))
   
   [RELATIVE_ERROR_POS]  Theorem
      
      |- !x.
           normalizes x /\ 0 < x ==>
           ?e.
             abs e <= 1 / 2 pow 24 /\
             (Val (float (round float_format To_nearest x)) = x * (1 + e))
   
   [RELATIVE_ERROR_ZERO]  Theorem
      
      |- !x.
           normalizes x /\ (x = 0) ==>
           ?e.
             abs e <= 1 / 2 pow 24 /\
             (Val (float (round float_format To_nearest x)) = x * (1 + e))
   
   [RRRC1]  Theorem
      
      |- 2 * 8388608 <= 2 pow 254 * (2 * 8388608 - 1)
   
   [RRRC10]  Theorem
      
      |- 1 < 2 pow 254 - 2 pow 229
   
   [RRRC11]  Theorem
      
      |- 340282356779733661637539395458142568448 * 2 pow 126 < 2 pow 254
   
   [RRRC2]  Theorem
      
      |- 2 pow 103 * (2 pow 24 * 2) - 2 pow 103 <= 2 pow 128
   
   [RRRC3]  Theorem
      
      |- 340282356779733661637539395458142568448 <= 2 pow 128
   
   [RRRC4]  Theorem
      
      |- 2 pow 128 - 2 pow 103 = 340282356779733661637539395458142568448
   
   [RRRC5]  Theorem
      
      |- inv 1 < 2 pow 103 * (2 pow 24 * 2) - 2 pow 103
   
   [RRRC6]  Theorem
      
      |- 0 < 2 pow 150
   
   [RRRC7]  Theorem
      
      |- 2 pow 254 - 2 pow 229 < 2 pow 254
   
   [RRRC8]  Theorem
      
      |- 2 pow 103 * (2 pow 24 * 2) - 2 pow 103 =
         340282356779733661637539395458142568448
   
   [RRRC9]  Theorem
      
      |- 2 pow 127 * 2 - 2 pow 104 <
         340282356779733661637539395458142568448
   
   [SIGN]  Theorem
      
      |- !a. sign a = FST a
   
   [THRESHOLD_LT_POW_INV]  Theorem
      
      |- 340282356779733661637539395458142568448 <
         2 pow 254 * inv (2 pow 126)
   
   [THRESHOLD_MUL_LT]  Theorem
      
      |- threshold float_format * 2 pow 126 < 2 pow 2 ** 126
   
   [TWO_EXP_GE_1]  Theorem
      
      |- !n. 1 <= 2 ** n
   
   [VALOF]  Theorem
      
      |- !X a.
           valof X a =
           if exponent a = 0 then
             -1 pow sign a * (2 / 2 pow bias X) *
             (&fraction a / 2 pow fracwidth X)
           else
             -1 pow sign a * (2 pow exponent a / 2 pow bias X) *
             (1 + &fraction a / 2 pow fracwidth X)
   
   [VALOF_DEFLOAT_FLOAT_ZEROSIGN_ROUND]  Theorem
      
      |- !x b.
           valof float_format
             (defloat
                (float
                   (zerosign float_format b
                      (round float_format To_nearest x)))) =
           valof float_format (round float_format To_nearest x)
   
   [VALOF_SCALE_DOWN]  Theorem
      
      |- !s e k f.
           k < e ==>
           (valof float_format (s,e - k,f) =
            inv (2 pow k) * valof float_format (s,e,f))
   
   [VALOF_SCALE_UP]  Theorem
      
      |- !s e k f.
           e <> 0 ==>
           (valof float_format (s,e + k,f) =
            2 pow k * valof float_format (s,e,f))
   
   [VAL_FINITE]  Theorem
      
      |- !a. Finite a ==> abs (Val a) <= largest float_format
   
   [VAL_THRESHOLD]  Theorem
      
      |- !a. Finite a ==> abs (Val a) < threshold float_format
   
   [Val_FLOAT_ROUND_VALOF]  Theorem
      
      |- !x.
           Val (float (round float_format To_nearest x)) =
           valof float_format (round float_format To_nearest x)
   
   [ZERO_IS_ZERO]  Theorem
      
      |- Iszero Plus_zero /\ Iszero Minus_zero
   
   [ZERO_NOT_NAN]  Theorem
      
      |- ~Isnan Plus_zero /\ ~Isnan Minus_zero
   
   [egt1]  Theorem
      
      |- 1 < 8
   
   [egtff]  Theorem
      
      |- 8 = 4 + 4
   
   [ftt]  Theorem
      
      |- 4 = 2 + 2
   
   [inv23gt0]  Theorem
      
      |- 0 < inv (2 pow 23)
   
   [lt1eqmul]  Theorem
      
      |- x < 1 <=> x * 8388608 < 8388608
   
   [not2eqz]  Theorem
      
      |- 2 <> 0
   
   [noteteeszegtz]  Theorem
      
      |- 0 < 8388608
   
   [sucminmullt]  Theorem
      
      |- (2 pow SUC 127 - 2 pow 103) * 2 pow 126 < 2 pow 255
   
   [temonz]  Theorem
      
      |- 2 ** 8 - 1 <> 0
   
   [tfflttfs]  Theorem
      
      |- 255 < 256
   
   [tittfittt]  Theorem
      
      |- 2 * inv (2 pow 24) = inv (2 pow 23)
   
   [tpetfs]  Theorem
      
      |- 2 pow 8 = 256
   
   [tptteteesze]  Theorem
      
      |- 2 pow 23 = 8388608
   
   [tteettto]  Theorem
      
      |- 23 = 8 + 8 + 2 + 2 + 2 + 1
   
   [ttpinv]  Theorem
      
      |- 2 * 2 pow 127 * inv (2 pow 127) = 2
   
   [twogz]  Theorem
      
      |- !n. 0 < 2 pow n
   
   [v127not0]  Theorem
      
      |- 2 pow 127 <> 0
   
   [v23not0]  Theorem
      
      |- 2 pow 23 <> 0
   
   
*)
end
