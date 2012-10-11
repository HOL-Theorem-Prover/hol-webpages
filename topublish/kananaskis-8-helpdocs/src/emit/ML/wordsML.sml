structure wordsML :> wordsML =
struct
  nonfix word_to_hex_string word_to_dec_string word_to_oct_string
         word_to_bin_string word_to_hex_list word_to_dec_list
         word_to_oct_list word_to_bin_list word_sign_extend w2s w2l
         bit_field_insert reduce_nor reduce_nand reduce_xnor reduce_xor
         reduce_or reduce_and word_reduce word_lt word_ls word_lo
         word_le word_hs word_hi word_gt word_ge word_index word_rrx
         word_rol word_ror word_asr word_lsr word_mul word_sub word_add
         word_sdiv word_div word_2comp word_xor word_and word_1comp
         add_with_carry word_msb word_lsb word_modify word_reverse
         word_log2 word_concat_itself word_slice word_extract_itself
         sw2sw_itself word_join word_bit word_signed_bits word_bits
         word_lsl word_or w2w_itself word_eq w2n INT_MAX UINT_MAX
         INT_MIN fromNum dimword * / div mod + - ^ @ <> > < >= <= := o
         before;

  open sumML
  open numML
  open fcpML
  open bitML

  datatype 'a word = n2w_itself of num * 'a itself
  fun dimword a = TIMES_2EXP (dimindex a) ONE

  fun fromNum (n,a) = n2w_itself (MOD n (dimword a),a)

  type word1 = unit word
  fun toWord1 n = fromNum (n,ITSELF(numML.fromInt 1))
  val fromString1 = o(toWord1, numML.fromString) : string -> word1
  type word2 = unit bit0 word
  fun toWord2 n = fromNum (n,ITSELF(numML.fromInt 2))
  val fromString2 = o(toWord2, numML.fromString) : string -> word2
  type word3 = unit bit1 word
  fun toWord3 n = fromNum (n,ITSELF(numML.fromInt 3))
  val fromString3 = o(toWord3, numML.fromString) : string -> word3
  type word4 = unit bit0 bit0 word
  fun toWord4 n = fromNum (n,ITSELF(numML.fromInt 4))
  val fromString4 = o(toWord4, numML.fromString) : string -> word4
  type word5 = unit bit0 bit1 word
  fun toWord5 n = fromNum (n,ITSELF(numML.fromInt 5))
  val fromString5 = o(toWord5, numML.fromString) : string -> word5
  type word6 = unit bit1 bit0 word
  fun toWord6 n = fromNum (n,ITSELF(numML.fromInt 6))
  val fromString6 = o(toWord6, numML.fromString) : string -> word6
  type word7 = unit bit1 bit1 word
  fun toWord7 n = fromNum (n,ITSELF(numML.fromInt 7))
  val fromString7 = o(toWord7, numML.fromString) : string -> word7
  type word8 = unit bit0 bit0 bit0 word
  fun toWord8 n = fromNum (n,ITSELF(numML.fromInt 8))
  val fromString8 = o(toWord8, numML.fromString) : string -> word8
  type word12 = unit bit1 bit0 bit0 word
  fun toWord12 n = fromNum (n,ITSELF(numML.fromInt 12))
  val fromString12 = o(toWord12, numML.fromString) : string -> word12
  type word16 = unit bit0 bit0 bit0 bit0 word
  fun toWord16 n = fromNum (n,ITSELF(numML.fromInt 16))
  val fromString16 = o(toWord16, numML.fromString) : string -> word16
  type word20 = unit bit0 bit1 bit0 bit0 word
  fun toWord20 n = fromNum (n,ITSELF(numML.fromInt 20))
  val fromString20 = o(toWord20, numML.fromString) : string -> word20
  type word24 = unit bit1 bit0 bit0 bit0 word
  fun toWord24 n = fromNum (n,ITSELF(numML.fromInt 24))
  val fromString24 = o(toWord24, numML.fromString) : string -> word24
  type word28 = unit bit1 bit1 bit0 bit0 word
  fun toWord28 n = fromNum (n,ITSELF(numML.fromInt 28))
  val fromString28 = o(toWord28, numML.fromString) : string -> word28
  type word30 = unit bit1 bit1 bit1 bit0 word
  fun toWord30 n = fromNum (n,ITSELF(numML.fromInt 30))
  val fromString30 = o(toWord30, numML.fromString) : string -> word30
  type word32 = unit bit0 bit0 bit0 bit0 bit0 word
  fun toWord32 n = fromNum (n,ITSELF(numML.fromInt 32))
  val fromString32 = o(toWord32, numML.fromString) : string -> word32
  type word64 = unit bit0 bit0 bit0 bit0 bit0 bit0 word
  fun toWord64 n = fromNum (n,ITSELF(numML.fromInt 64))
  val fromString64 = o(toWord64, numML.fromString) : string -> word64
  fun INT_MIN a = TIMES_2EXP (- (dimindex a) ONE) ONE

  fun UINT_MAX a = - (dimword a) ONE

  fun INT_MAX a = - (INT_MIN a) ONE

  fun w2n (n2w_itself (n,a)) = MOD n (dimword a)

  fun word_eq (n2w_itself (m,a)) w =
        MOD m (dimword a) = MOD (w2n w) (dimword a)

  fun w2w_itself b (n2w_itself (n,a)) =
        if <= (dimindex b) (dimindex a) then n2w_itself (n,b)
        else n2w_itself (BITS (- (dimindex a) ONE) ZERO n,b)

  fun word_or w (n2w_itself (m,a)) =
        n2w_itself
          (BITWISE (dimindex a) (fn a => fn b => a orelse b) (w2n w) m,
           a)

  fun word_lsl (n2w_itself (m,a)) n =
        if < (- (dimindex a) ONE) n then n2w_itself (ZERO,a)
        else n2w_itself ( *  m (TIMES_2EXP n ONE),a)

  fun word_bits h l (n2w_itself (n,a)) =
        n2w_itself (BITS (MIN h (- (dimindex a) ONE)) l n,a)

  fun word_signed_bits h l (n2w_itself (n,a)) =
        n2w_itself
          (SIGN_EXTEND (- (MIN (SUC h) (dimindex a)) l) (dimindex a)
             (BITS (MIN h (- (dimindex a) ONE)) l n),a)

  fun word_bit c (n2w_itself (n,a)) =
        <= c (- (dimindex a) ONE) andalso BIT c n

  fun word_join (n2w_itself (m,a)) (n2w_itself (n,b)) =
        let val cv = w2w_itself (SUMi(a, b)) (n2w_itself (m,a))
            val cw = w2w_itself (SUMi(a, b)) (n2w_itself (n,b))
        in
           word_or (word_lsl cv (dimindex b)) cw
        end

  fun sw2sw_itself b (n2w_itself (n,a)) =
        n2w_itself
          (SIGN_EXTEND (dimindex a) (dimindex b)
             (w2n (n2w_itself (n,a))),b)

  fun word_extract_itself b h l (n2w_itself (n,a)) =
        if <= (dimindex b) (dimindex a) then
          n2w_itself (BITS (MIN h (- (dimindex a) ONE)) l n,b)
        else
          n2w_itself
            (BITS
               (MIN (MIN h (- (dimindex a) ONE))
                  (+ (- (dimindex a) ONE) l)) l n,b)

  fun word_slice h l (n2w_itself (n,a)) =
        n2w_itself (SLICE (MIN h (- (dimindex a) ONE)) l n,a)

  fun word_concat_itself c v w = w2w_itself c (word_join v w)

  fun word_log2 (n2w_itself (n,a)) =
        n2w_itself (LOG2 (MOD n (dimword a)),a)

  fun word_reverse (n2w_itself (n,a)) =
        n2w_itself (BIT_REVERSE (dimindex a) n,a)

  fun word_modify f (n2w_itself (n,a)) =
        n2w_itself (BIT_MODIFY (dimindex a) f n,a)

  fun word_lsb (n2w_itself (n,a)) = ODD n

  fun word_msb (n2w_itself (n,a)) = BIT (- (dimindex a) ONE) n

  fun add_with_carry (n2w_itself (n,a),(y,carry_in)) =
        let val unsigned_sum =
                + (+ (w2n (n2w_itself (n,a))) (w2n y))
                  (if carry_in then ONE else ZERO)
            val result = n2w_itself (unsigned_sum,a)
            val carry_out = not (w2n result = unsigned_sum)
            val overflow =
                (word_msb (n2w_itself (n,a)) = word_msb y) andalso
                not (word_msb (n2w_itself (n,a)) = word_msb result)
        in
           (result,(carry_out,overflow))
        end

  fun word_1comp (n2w_itself (n,a)) =
        n2w_itself (- (- (dimword a) ONE) (MOD n (dimword a)),a)

  fun word_and w (n2w_itself (m,a)) =
        n2w_itself
          (BITWISE (dimindex a) (fn a => fn b => a andalso b) (w2n w) m,
           a)

  fun word_xor w (n2w_itself (m,a)) =
        n2w_itself
          (BITWISE (dimindex a) (fn x => fn y => not (x = y)) (w2n w) m,
           a)

  fun word_2comp (n2w_itself (n,a)) =
        n2w_itself (- (dimword a) (MOD n (dimword a)),a)

  fun word_div (n2w_itself (m,a)) w =
        n2w_itself (DIV (w2n (n2w_itself (m,a))) (w2n w),a)

  fun word_sdiv m n =
        if word_msb m then
          (if word_msb n then
             word_div (word_2comp m) (word_2comp n)
           else word_2comp (word_div (word_2comp m) n))
        else
          if word_msb n then
          word_2comp (word_div m (word_2comp n))
        else word_div m n

  fun word_add w (n2w_itself (n,a)) =
        n2w_itself (MOD (+ (w2n w) n) (dimword a),a)

  fun word_sub v w = word_add v (word_2comp w)

  fun word_mul w (n2w_itself (n,a)) =
        n2w_itself (MOD ( *  (w2n w) n) (dimword a),a)

  fun word_lsr (n2w_itself (m,a)) n =
        word_bits (- (dimindex a) ONE) n (n2w_itself (m,a))

  fun word_asr (n2w_itself (m,a)) n =
        if word_msb (n2w_itself (m,a)) then
          word_or
            (n2w_itself
               (- (dimword a)
                  (TIMES_2EXP (- (dimindex a) (MIN n (dimindex a)))
                     ONE),a)) (word_lsr (n2w_itself (m,a)) n)
        else word_lsr (n2w_itself (m,a)) n

  fun word_ror (n2w_itself (m,a)) n =
        let val x = MOD n (dimindex a)
        in
           n2w_itself
             (+ (BITS (- (dimindex a) ONE) x m)
                ( *  (BITS (- x ONE) ZERO m)
                   (TIMES_2EXP (- (dimindex a) x) ONE)),a)
        end

  fun word_rol (n2w_itself (m,a)) n =
        word_ror (n2w_itself (m,a))
          (- (dimindex a) (MOD n (dimindex a)))

  fun word_rrx (c,n2w_itself (m,a)) =
        (ODD m,
         n2w_itself
           (+ (BITS (- (dimindex a) ONE) ONE m)
              (SBIT c (- (dimindex a) ONE)),a))

  fun word_index (n2w_itself (n,a)) i =
        if < i (dimindex a) then BIT i n
        else raise (Fail "fcp_index: index too large")

  fun word_ge w (n2w_itself (n,a)) =
        let val sa = BIT (- (dimindex a) ONE) (w2n w)
            val sb = BIT (- (dimindex a) ONE) n
        in
           (sa = sb) andalso
           >= (MOD (w2n w) (dimword a)) (MOD n (dimword a)) orelse
           not sa andalso sb
        end

  fun word_gt w (n2w_itself (n,a)) =
        let val sa = BIT (- (dimindex a) ONE) (w2n w)
            val sb = BIT (- (dimindex a) ONE) n
        in
           (sa = sb) andalso
           > (MOD (w2n w) (dimword a)) (MOD n (dimword a)) orelse
           not sa andalso sb
        end

  fun word_hi w (n2w_itself (n,a)) =
        > (MOD (w2n w) (dimword a)) (MOD n (dimword a))

  fun word_hs w (n2w_itself (n,a)) =
        >= (MOD (w2n w) (dimword a)) (MOD n (dimword a))

  fun word_le w (n2w_itself (n,a)) =
        let val sa = BIT (- (dimindex a) ONE) (w2n w)
            val sb = BIT (- (dimindex a) ONE) n
        in
           (sa = sb) andalso
           <= (MOD (w2n w) (dimword a)) (MOD n (dimword a)) orelse
           sa andalso not sb
        end

  fun word_lo w (n2w_itself (n,a)) =
        < (MOD (w2n w) (dimword a)) (MOD n (dimword a))

  fun word_ls w (n2w_itself (n,a)) =
        <= (MOD (w2n w) (dimword a)) (MOD n (dimword a))

  fun word_lt w (n2w_itself (n,a)) =
        let val sa = BIT (- (dimindex a) ONE) (w2n w)
            val sb = BIT (- (dimindex a) ONE) n
        in
           (sa = sb) andalso
           < (MOD (w2n w) (dimword a)) (MOD n (dimword a)) orelse
           sa andalso not sb
        end

  fun word_reduce f (n2w_itself (n,a)) =
        n2w_itself
          (if
             let val l = BOOLIFY (dimindex a) n []
             in
                listML.FOLDL f (listML.HD l) (listML.TL l)
             end
           then ONE else ZERO,(ITSELF ONE))

  fun reduce_and (n2w_itself (m,a)) =
        if n2w_itself (m,a) = n2w_itself (UINT_MAX a,a) then
          n2w_itself (ONE,(ITSELF ONE))
        else n2w_itself (ZERO,(ITSELF ONE))

  fun reduce_or (n2w_itself (m,a)) =
        if n2w_itself (m,a) = n2w_itself (ZERO,a) then
          n2w_itself (ZERO,(ITSELF ONE))
        else n2w_itself (ONE,(ITSELF ONE))

  fun reduce_xor x = word_reduce (fn x => fn y => not (x = y)) x

  fun reduce_xnor x = word_reduce (fn x => fn y => x = y) x

  fun reduce_nand x = word_reduce (fn a => fn b => not (a andalso b)) x

  fun reduce_nor x = word_reduce (fn a => fn b => not (a orelse b)) x

  fun bit_field_insert h l m w =
        word_modify (fn i => fn b => if <= l i andalso <= i h then
            word_index m (- i l) else b) w

  fun w2l n w = n2l n (w2n w)

  fun w2s n f w = n2s n f (w2n w)

  fun word_sign_extend n (n2w_itself (w,a)) =
        n2w_itself (SIGN_EXTEND n (dimindex a) (MOD w (dimword a)),a)

  fun word_to_bin_list x = w2l TWO x

  fun word_to_oct_list x = w2l (fromString "8") x

  fun word_to_dec_list x = w2l (fromString "10") x

  fun word_to_hex_list x = w2l (fromString "16") x

  fun word_to_bin_string x = w2s TWO HEX x

  fun word_to_oct_string x = w2s (fromString "8") HEX x

  fun word_to_dec_string x = w2s (fromString "10") HEX x

  fun word_to_hex_string x = w2s (fromString "16") HEX x

end
