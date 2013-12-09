structure intML :> intML =
struct
  nonfix w2i i2w_itself UINT_MAX INT_MIN INT_MAX int_rem int_quot
         int_mod int_div int_exp int_mul int_sub int_add ABS int_ge
         int_gt int_le int_lt Num int_neg neg_int_of_num int_of_num * /
         div mod + - ^ @ <> > < >= <= := o before;

  open numML
  open wordsML

  datatype int = int_of_num of num | neg_int_of_num of num
  fun fromString s =
    let val s = String.extract(s,0,SOME (Int.-(String.size s,1))) in
      if String.sub(s,0) = #"-" then
        let val s = String.extract(s,1,NONE) in
          neg_int_of_num (numML.PRE (numML.fromString s))
        end
      else
        int_of_num (numML.fromString s)
    end

  fun fromInt i =
    fromString (String.map (fn c => if c = #"~" then #"-" else c)
      (String.^(Int.toString i,"i")))

  fun toInt (int_of_num n) = numML.toInt n
    | toInt (neg_int_of_num n) =
         case numML.toInt n of
           SOME v => SOME (Int.-(Int.~ v,1))
         | NONE => NONE

  fun int_neg (int_of_num n) =
        (if n = ZERO then
           (fromString"0i")
         else neg_int_of_num (- n ONE))
    | int_neg (neg_int_of_num n) = int_of_num (+ n ONE)

  fun Num (int_of_num n) = n
    | Num (neg_int_of_num n) = raise (Fail "Num: negative")

  fun int_lt (int_of_num m) (int_of_num n) = < m n
    | int_lt (neg_int_of_num m) (int_of_num n) = true
    | int_lt (int_of_num m) (neg_int_of_num n) = false
    | int_lt (neg_int_of_num m) (neg_int_of_num n) = < n m

  fun int_le x y = int_lt x y orelse (x = y)

  fun int_gt x y = int_lt y x

  fun int_ge x y = int_le y x

  fun ABS n = if int_lt n (fromString"0i") then int_neg n else n

  fun int_add (int_of_num m) (int_of_num n) = int_of_num (+ m n)
    | int_add (neg_int_of_num m) (int_of_num n) =
        (if <= (+ m ONE) n then
           int_of_num (- n (+ m ONE))
         else neg_int_of_num (- m n))
    | int_add (int_of_num m) (neg_int_of_num n) =
        (if <= (+ n ONE) m then
           int_of_num (- m (+ n ONE))
         else neg_int_of_num (- n m))
    | int_add (neg_int_of_num m) (neg_int_of_num n) =
        neg_int_of_num (+ (+ m n) ONE)

  fun int_sub (int_of_num m) (int_of_num n) =
        int_add (int_of_num m) (int_neg (int_of_num n))
    | int_sub (neg_int_of_num m) (int_of_num n) =
        int_add (neg_int_of_num m) (int_neg (int_of_num n))
    | int_sub (int_of_num m) (neg_int_of_num n) =
        int_add (int_of_num m) (int_of_num (+ n ONE))
    | int_sub (neg_int_of_num m) (neg_int_of_num n) =
        int_add (neg_int_of_num m) (int_of_num (+ n ONE))

  fun int_mul (int_of_num m) (int_of_num n) = int_of_num ( *  m n)
    | int_mul (neg_int_of_num m) (int_of_num n) =
        int_neg (int_of_num ( *  (+ m ONE) n))
    | int_mul (int_of_num m) (neg_int_of_num n) =
        int_neg (int_of_num ( *  m (+ n ONE)))
    | int_mul (neg_int_of_num m) (neg_int_of_num n) =
        int_of_num ( *  (+ m ONE) (+ n ONE))

  fun int_exp (int_of_num n) m = int_of_num (EXP n m)
    | int_exp (neg_int_of_num m) n =
        (if EVEN n then
           int_of_num (EXP (+ m ONE) n)
         else int_neg (int_of_num (EXP (+ m ONE) n)))

  fun int_div i j =
        if j = (fromString"0i") then
          raise (Fail "int_div: zero denominator")
        else
          if int_lt (fromString"0i") j then
          (if int_le (fromString"0i") i then
             int_of_num (DIV (Num i) (Num j))
           else
             int_add
               (int_neg (int_of_num (DIV (Num (int_neg i)) (Num j))))
               (if MOD (Num (int_neg i)) (Num j) = ZERO then
                  (fromString"0i")
                else int_neg (int_of_num ONE)))
        else
          if int_le (fromString"0i") i then
          int_add (int_neg (int_of_num (DIV (Num i) (Num (int_neg j)))))
            (if MOD (Num i) (Num (int_neg j)) = ZERO then
               (fromString"0i")
             else int_neg (int_of_num ONE))
        else int_of_num (DIV (Num (int_neg i)) (Num (int_neg j)))

  fun int_mod i j =
        if j = (fromString"0i") then
          raise (Fail "int_mod: zero denominator")
        else int_sub i (int_mul (int_div i j) j)

  fun int_quot i j =
        if j = (fromString"0i") then
          raise (Fail "int_quot: zero denominator")
        else
          if int_lt (fromString"0i") j then
          (if int_le (fromString"0i") i then
             int_of_num (DIV (Num i) (Num j))
           else int_neg (int_of_num (DIV (Num (int_neg i)) (Num j))))
        else
          if int_le (fromString"0i") i then
          int_neg (int_of_num (DIV (Num i) (Num (int_neg j))))
        else int_of_num (DIV (Num (int_neg i)) (Num (int_neg j)))

  fun int_rem i j =
        if j = (fromString"0i") then
          raise (Fail "int_rem: zero denominator")
        else int_sub i (int_mul (int_quot i j) j)

  fun INT_MAX a = int_sub (int_of_num (INT_MIN a)) (int_of_num ONE)

  fun INT_MIN a = int_sub (int_neg (INT_MAX a)) (int_of_num ONE)

  fun UINT_MAX a = int_sub (int_of_num (dimword a)) (int_of_num ONE)

  fun i2w_itself (i,a) =
        if int_lt i (fromString"0i") then
          word_2comp (n2w_itself (Num (int_neg i),a))
        else n2w_itself (Num i,a)

  fun w2i w =
        if word_msb w then int_neg (int_of_num (w2n (word_2comp w)))
        else int_of_num (w2n w)

end
