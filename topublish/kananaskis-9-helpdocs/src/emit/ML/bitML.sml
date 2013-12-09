structure bitML :> bitML =
struct
  nonfix BOOLIFY SIGN_EXTEND SLICE BIT BITV MOD_2EXP_EQ BITS SBIT
         DIVMOD_2EXP LOG2 BIT_REVERSE BIT_REV BIT_MODIFY BIT_MODF
         num_to_hex_string num_to_dec_string num_to_oct_string
         num_to_bin_string num_from_hex_string num_from_dec_string
         num_from_oct_string num_from_bin_string num_to_hex_list
         num_to_dec_list num_to_oct_list num_to_bin_list
         num_from_hex_list num_from_dec_list num_from_oct_list
         num_from_bin_list UNHEX HEX n2s s2n n2l l2n LOWEST_SET_BIT LOG
         BITWISE TIMES_2EXP * / div mod + - ^ @ <> > < >= <= := o
         before;

  open numML

  fun TIMES_2EXP n x =
        if x = ZERO then ZERO else  *  x (FUNPOW iDUB n ONE)

  fun BITWISE n opr a b =
        if n = ZERO then ZERO
        else
          + ( *  TWO (BITWISE (PRE n) opr (DIV2 a) (DIV2 b)))
            (if opr (ODD a) (ODD b) then ONE else ZERO)

  fun LOG m n =
        if < m TWO orelse (n = ZERO) then
          raise (Fail "LOG: base < 2 or n = 0")
        else if < n m then ZERO else SUC (LOG m (DIV n m))

  fun LOWEST_SET_BIT n =
        if n = ZERO then raise (Fail "LOWEST_SET_BIT: zero value")
        else if ODD n then ZERO else + ONE (LOWEST_SET_BIT (DIV2 n))

  fun l2n b [] = ZERO
    | l2n b (h::t) = + (MOD h b) ( *  b (l2n b t))

  fun n2l b n =
        if < n b orelse < b TWO then [MOD n b]
        else MOD n b::n2l b (DIV n b)

  fun s2n b f s =
        l2n b (listML.MAP f (listML.REVERSE (stringML.EXPLODE s)))

  fun n2s b f n =
        stringML.IMPLODE (listML.REVERSE (listML.MAP f (n2l b n)))

  fun HEX n =
        if n = ZERO then stringML.CHR (fromString "48")
        else
          if n = ONE then
          stringML.CHR (fromString "49")
        else
          if n = TWO then
          stringML.CHR (fromString "50")
        else
          if n = (fromString "3") then
          stringML.CHR (fromString "51")
        else
          if n = (fromString "4") then
          stringML.CHR (fromString "52")
        else
          if n = (fromString "5") then
          stringML.CHR (fromString "53")
        else
          if n = (fromString "6") then
          stringML.CHR (fromString "54")
        else
          if n = (fromString "7") then
          stringML.CHR (fromString "55")
        else
          if n = (fromString "8") then
          stringML.CHR (fromString "56")
        else
          if n = (fromString "9") then
          stringML.CHR (fromString "57")
        else
          if n = (fromString "10") then
          stringML.CHR (fromString "65")
        else
          if n = (fromString "11") then
          stringML.CHR (fromString "66")
        else
          if n = (fromString "12") then
          stringML.CHR (fromString "67")
        else
          if n = (fromString "13") then
          stringML.CHR (fromString "68")
        else
          if n = (fromString "14") then
          stringML.CHR (fromString "69")
        else
          if n = (fromString "15") then
          stringML.CHR (fromString "70")
        else raise (Fail "HEX: not a hex digit")

  fun UNHEX c =
        if c = stringML.CHR (fromString "48") then ZERO
        else
          if c = stringML.CHR (fromString "49") then
          ONE
        else
          if c = stringML.CHR (fromString "50") then
          TWO
        else
          if c = stringML.CHR (fromString "51") then
          (fromString "3")
        else
          if c = stringML.CHR (fromString "52") then
          (fromString "4")
        else
          if c = stringML.CHR (fromString "53") then
          (fromString "5")
        else
          if c = stringML.CHR (fromString "54") then
          (fromString "6")
        else
          if c = stringML.CHR (fromString "55") then
          (fromString "7")
        else
          if c = stringML.CHR (fromString "56") then
          (fromString "8")
        else
          if c = stringML.CHR (fromString "57") then
          (fromString "9")
        else
          if c = stringML.CHR (fromString "65") then
          (fromString "10")
        else
          if c = stringML.CHR (fromString "66") then
          (fromString "11")
        else
          if c = stringML.CHR (fromString "67") then
          (fromString "12")
        else
          if c = stringML.CHR (fromString "68") then
          (fromString "13")
        else
          if c = stringML.CHR (fromString "69") then
          (fromString "14")
        else
          if c = stringML.CHR (fromString "70") then
          (fromString "15")
        else raise (Fail "UNHEX: not a hex digit")

  val num_from_bin_list = l2n TWO

  val num_from_oct_list = l2n (fromString "8")

  val num_from_dec_list = l2n (fromString "10")

  val num_from_hex_list = l2n (fromString "16")

  val num_to_bin_list = n2l TWO

  val num_to_oct_list = n2l (fromString "8")

  val num_to_dec_list = n2l (fromString "10")

  val num_to_hex_list = n2l (fromString "16")

  val num_from_bin_string = s2n TWO UNHEX

  val num_from_oct_string = s2n (fromString "8") UNHEX

  val num_from_dec_string = s2n (fromString "10") UNHEX

  val num_from_hex_string = s2n (fromString "16") UNHEX

  val num_to_bin_string = n2s TWO HEX

  val num_to_oct_string = n2s (fromString "8") HEX

  val num_to_dec_string = n2s (fromString "10") HEX

  val num_to_hex_string = n2s (fromString "16") HEX

  fun BIT_MODF n f x b e y =
        if n = ZERO then y
        else
          BIT_MODF (PRE n) f (DIV2 x) (+ b ONE) ( *  TWO e)
            (if f b (ODD x) then + e y else y)

  fun BIT_MODIFY m f n = BIT_MODF m f n ZERO ONE ZERO

  fun BIT_REV n x y =
        if n = ZERO then y
        else
          BIT_REV (PRE n) (DIV2 x)
            (+ ( *  TWO y) (if ODD x then ONE else ZERO))

  fun BIT_REVERSE m n = BIT_REV m n ZERO

  fun LOG2 n =
        if n = ZERO then raise (Fail "LOG2: undefined")
        else if n = ONE then ZERO else + ONE (LOG2 (DIV2 n))

  fun DIVMOD_2EXP x n = (DIV_2EXP x n,MOD_2EXP x n)

  fun SBIT b n = if b then TIMES_2EXP n ONE else ZERO

  fun BITS h l n = MOD_2EXP (- (SUC h) l) (DIV_2EXP l n)

  fun MOD_2EXP_EQ n a b =
        if n = ZERO then true
        else
          (ODD a = ODD b) andalso
          MOD_2EXP_EQ (- n ONE) (DIV2 a) (DIV2 b)

  fun BITV n b = BITS b b n

  fun BIT b n = BITS b b n = ONE

  fun SLICE h l n = - (MOD_2EXP (SUC h) n) (MOD_2EXP l n)

  fun SIGN_EXTEND l h n =
        let val m = MOD n (TIMES_2EXP l ONE)
        in
           if BIT (- l ONE) n then
          + (- (TIMES_2EXP h ONE) (TIMES_2EXP l ONE)) m
        else m
        end

  fun BOOLIFY n m a =
        if n = ZERO then a else BOOLIFY (PRE n) (DIV2 m) (ODD m::a)

end
