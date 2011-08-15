structure numML :> numML =
struct
  nonfix measure DIV_2EXP MOD_2EXP DIV2 MOD DIV DIVMOD findq LEAST WHILE
         MAX MIN FUNPOW FACT ODD EVEN EXP iSQR iSUB iDUB PRE iiSUC iZ
         SUC BIT2 BIT1 ZERO * / div mod + - ^ @ <> > < >= <= := o
         before;
  
  datatype num = ZERO | BIT1 of num | BIT2 of num
  open combinML
  
  val num_size = I
  fun NUMERAL x = x
  val ONE = BIT1 ZERO
  fun SUC ZERO = ONE
    | SUC (BIT1 n) = BIT2 n
    | SUC (BIT2 n) = BIT1 (SUC n)
    
  fun iZ x = x
    
  fun iiSUC n = SUC (SUC n)
    
  fun + ZERO n = n
    | + n ZERO = n
    | + (BIT1 n) (BIT1 m) = BIT2 (+ n m)
    | + (BIT1 n) (BIT2 m) = BIT1 (SUC (+ n m))
    | + (BIT2 n) (BIT1 m) = BIT1 (SUC (+ n m))
    | + (BIT2 n) (BIT2 m) = BIT2 (SUC (+ n m))
    
  fun < ZERO (BIT1 n) = true
    | < ZERO (BIT2 n) = true
    | < n ZERO = false
    | < (BIT1 n) (BIT1 m) = < n m
    | < (BIT2 n) (BIT2 m) = < n m
    | < (BIT1 n) (BIT2 m) = not (< m n)
    | < (BIT2 n) (BIT1 m) = < n m
    
  fun <= ZERO n = true
    | <= (BIT1 n) ZERO = false
    | <= (BIT2 n) ZERO = false
    | <= (BIT1 n) (BIT1 m) = <= n m
    | <= (BIT1 n) (BIT2 m) = <= n m
    | <= (BIT2 n) (BIT1 m) = not (<= m n)
    | <= (BIT2 n) (BIT2 m) = <= n m
    
  fun > m n = < n m
    
  fun >= m n = > m n orelse (m = n)
    
  fun PRE ZERO = ZERO
    | PRE (BIT1 ZERO) = ZERO
    | PRE (BIT1 (BIT1 n)) = BIT2 (PRE (BIT1 n))
    | PRE (BIT1 (BIT2 n)) = BIT2 (BIT1 n)
    | PRE (BIT2 n) = BIT1 n
    
  fun iDUB (BIT1 n) = BIT2 (iDUB n)
    | iDUB (BIT2 n) = BIT2 (BIT1 n)
    | iDUB ZERO = ZERO
    
  fun iSUB b ZERO x = ZERO
    | iSUB true n ZERO = n
    | iSUB false (BIT1 n) ZERO = iDUB n
    | iSUB true (BIT1 n) (BIT1 m) = iDUB (iSUB true n m)
    | iSUB false (BIT1 n) (BIT1 m) = BIT1 (iSUB false n m)
    | iSUB true (BIT1 n) (BIT2 m) = BIT1 (iSUB false n m)
    | iSUB false (BIT1 n) (BIT2 m) = iDUB (iSUB false n m)
    | iSUB false (BIT2 n) ZERO = BIT1 n
    | iSUB true (BIT2 n) (BIT1 m) = BIT1 (iSUB true n m)
    | iSUB false (BIT2 n) (BIT1 m) = iDUB (iSUB true n m)
    | iSUB true (BIT2 n) (BIT2 m) = iDUB (iSUB true n m)
    | iSUB false (BIT2 n) (BIT2 m) = BIT1 (iSUB false n m)
    
  fun - n m = if < m n then iSUB true n m else ZERO
    
  fun  *  ZERO n = ZERO
    |  *  n ZERO = ZERO
    |  *  (BIT1 n) m = iZ (+ (iDUB ( *  n m)) m)
    |  *  (BIT2 n) m = iDUB (iZ (+ ( *  n m) m))
    
  fun iSQR x =  *  x x
    
  fun EXP n ZERO = ONE
    | EXP n (BIT1 m) =  *  n (iSQR (EXP n m))
    | EXP n (BIT2 m) =  *  (iSQR n) (iSQR (EXP n m))
    
  fun EVEN ZERO = true
    | EVEN (BIT2 n) = true
    | EVEN (BIT1 n) = false
    
  fun ODD ZERO = false
    | ODD (BIT2 n) = false
    | ODD (BIT1 n) = true
    
  fun FACT ZERO = ONE
    | FACT (BIT1 n) =  *  (BIT1 n) (FACT (PRE (BIT1 n)))
    | FACT (BIT2 n) =  *  (BIT2 n) (FACT (BIT1 n))
    
  fun FUNPOW f ZERO x = x
    | FUNPOW f (BIT1 n) x = FUNPOW f (PRE (BIT1 n)) (f x)
    | FUNPOW f (BIT2 n) x = FUNPOW f (BIT1 n) (f x)
    
  fun MIN ZERO x = ZERO
    | MIN x ZERO = ZERO
    | MIN x y = (if < x y then x else y)
    
  fun MAX ZERO x = x
    | MAX x ZERO = x
    | MAX x y = (if < x y then y else x)
    
  fun WHILE P g x = if P x then WHILE P g (g x) else x
    
  fun LEAST P = WHILE (o not P) SUC ZERO
    
  fun findq (a,(m,n)) =
        if n = ZERO then a
        else
          let val d = iDUB n
          in
             if < m d then
            a
          else findq (iDUB a,(m,d))
          end
    
  fun DIVMOD (a,(m,n)) =
        if n = ZERO then (ZERO,ZERO)
        else
          if < m n then
          (a,m)
        else
          let val q = findq (ONE,(m,n))
          in
             DIVMOD (+ a q,(- m ( *  n q),n))
          end
    
  fun DIV m ZERO = raise (Fail "DIV: zero denominator")
    | DIV m (BIT1 n) = pairML.FST (DIVMOD (ZERO,(m,BIT1 n)))
    | DIV m (BIT2 n) = pairML.FST (DIVMOD (ZERO,(m,BIT2 n)))
    
  fun MOD m ZERO = raise (Fail "MOD: zero denominator")
    | MOD m (BIT1 n) = pairML.SND (DIVMOD (ZERO,(m,BIT1 n)))
    | MOD m (BIT2 n) = pairML.SND (DIVMOD (ZERO,(m,BIT2 n)))
    
  fun DIV2 ZERO = ZERO
    | DIV2 (BIT1 n) = n
    | DIV2 (BIT2 n) = SUC n
    
  fun MOD_2EXP ZERO n = ZERO
    | MOD_2EXP x ZERO = ZERO
    | MOD_2EXP (BIT1 x) (BIT1 n) = BIT1 (MOD_2EXP (- (BIT1 x) ONE) n)
    | MOD_2EXP (BIT2 x) (BIT1 n) = BIT1 (MOD_2EXP (BIT1 x) n)
    | MOD_2EXP (BIT1 x) (BIT2 n) =
        iDUB (MOD_2EXP (- (BIT1 x) ONE) (SUC n))
    | MOD_2EXP (BIT2 x) (BIT2 n) = iDUB (MOD_2EXP (BIT1 x) (SUC n))
    
  fun DIV_2EXP n x = FUNPOW DIV2 n x
    
  fun measure f x y = < (f x) (f y)
    
  
 (*---------------------------------------------------------------------------*)
 (* Supplementary ML, not generated from HOL theorems, aimed at supporting    *)
 (* parsing and pretty printing of numerals.                                  *)
 (*---------------------------------------------------------------------------*)
 
  val TWO = BIT2 ZERO;
  val THREE = BIT1 (BIT1 ZERO);
  val FOUR = BIT2 (BIT1 ZERO);
  val EIGHT = BIT2(BIT1(BIT1 ZERO));
  val TEN = BIT2(BIT2(BIT1 ZERO));
  val SIXTEEN = BIT2(BIT1(BIT1(BIT1 ZERO)));


  fun toBaseString divmod_b d n =
     let fun toBaseStr n s =
           if n = ZERO then
             if s = "" then "0" else s
           else let val (q, r) = divmod_b n in
             toBaseStr q (^(str (d r), s))
           end
     in
       toBaseStr n ""
     end

  fun BIN ZERO = #"0"
    | BIN (BIT1 ZERO) = #"1"
    | BIN otherwise   = #"?";

  fun UNBIN #"0" = ZERO
    | UNBIN #"1" = BIT1 ZERO
    | UNBIN other = raise Fail "not a binary character";

  fun OCT ZERO = #"0"
    | OCT (BIT1 ZERO) = #"1"
    | OCT (BIT2 ZERO) = #"2"
    | OCT (BIT1(BIT1 ZERO)) = #"3"
    | OCT (BIT2(BIT1 ZERO)) = #"4"
    | OCT (BIT1(BIT2 ZERO)) = #"5"
    | OCT (BIT2(BIT2 ZERO)) = #"6"
    | OCT (BIT1(BIT1(BIT1 ZERO))) = #"7"
    | OCT otherwise = #"?";

  fun UNOCT #"0" = ZERO
    | UNOCT #"1" = BIT1 ZERO
    | UNOCT #"2" = BIT2 ZERO
    | UNOCT #"3" = BIT1(BIT1 ZERO)
    | UNOCT #"4" = BIT2(BIT1 ZERO)
    | UNOCT #"5" = BIT1(BIT2 ZERO)
    | UNOCT #"6" = BIT2(BIT2 ZERO)
    | UNOCT #"7" = BIT1(BIT1(BIT1 ZERO))
    | UNOCT other = raise Fail "not an octal character";


  fun DIGIT ZERO = #"0"
    | DIGIT (BIT1 ZERO) = #"1"
    | DIGIT (BIT2 ZERO) = #"2"
    | DIGIT (BIT1(BIT1 ZERO)) = #"3"
    | DIGIT (BIT2(BIT1 ZERO)) = #"4"
    | DIGIT (BIT1(BIT2 ZERO)) = #"5"
    | DIGIT (BIT2(BIT2 ZERO)) = #"6"
    | DIGIT (BIT1(BIT1(BIT1 ZERO))) = #"7"
    | DIGIT (BIT2(BIT1(BIT1 ZERO))) = #"8"
    | DIGIT (BIT1(BIT2(BIT1 ZERO))) = #"9"
    | DIGIT otherwise = #"?";

  fun UNDIGIT #"0" = ZERO
    | UNDIGIT #"1" = BIT1 ZERO
    | UNDIGIT #"2" = BIT2 ZERO
    | UNDIGIT #"3" = BIT1(BIT1 ZERO)
    | UNDIGIT #"4" = BIT2(BIT1 ZERO)
    | UNDIGIT #"5" = BIT1(BIT2 ZERO)
    | UNDIGIT #"6" = BIT2(BIT2 ZERO)
    | UNDIGIT #"7" = BIT1(BIT1(BIT1 ZERO))
    | UNDIGIT #"8" = BIT2(BIT1(BIT1 ZERO))
    | UNDIGIT #"9" = BIT1(BIT2(BIT1 ZERO))
    | UNDIGIT other = raise Fail "not a decimal character";

  fun HEX ZERO = #"0"
    | HEX (BIT1 ZERO) = #"1"
    | HEX (BIT2 ZERO) = #"2"
    | HEX (BIT1(BIT1 ZERO)) = #"3"
    | HEX (BIT2(BIT1 ZERO)) = #"4"
    | HEX (BIT1(BIT2 ZERO)) = #"5"
    | HEX (BIT2(BIT2 ZERO)) = #"6"
    | HEX (BIT1(BIT1(BIT1 ZERO))) = #"7"
    | HEX (BIT2(BIT1(BIT1 ZERO))) = #"8"
    | HEX (BIT1(BIT2(BIT1 ZERO))) = #"9"
    | HEX (BIT2(BIT2(BIT1 ZERO))) = #"A"
    | HEX (BIT1(BIT1(BIT2 ZERO))) = #"B"
    | HEX (BIT2(BIT1(BIT2 ZERO))) = #"C"
    | HEX (BIT1(BIT2(BIT2 ZERO))) = #"D"
    | HEX (BIT2(BIT2(BIT2 ZERO))) = #"E"
    | HEX (BIT1(BIT1(BIT1(BIT1 ZERO)))) = #"F"
    | HEX otherwise = #"?";

  fun UNHEX #"0" = ZERO
    | UNHEX #"1" = BIT1 ZERO
    | UNHEX #"2" = BIT2 ZERO
    | UNHEX #"3" = BIT1(BIT1 ZERO)
    | UNHEX #"4" = BIT2(BIT1 ZERO)
    | UNHEX #"5" = BIT1(BIT2 ZERO)
    | UNHEX #"6" = BIT2(BIT2 ZERO)
    | UNHEX #"7" = BIT1(BIT1(BIT1 ZERO))
    | UNHEX #"8" = BIT2(BIT1(BIT1 ZERO))
    | UNHEX #"9" = BIT1(BIT2(BIT1 ZERO))
    | UNHEX #"a" = BIT2(BIT2(BIT1 ZERO))
    | UNHEX #"A" = BIT2(BIT2(BIT1 ZERO))
    | UNHEX #"b" = BIT1(BIT1(BIT2 ZERO))
    | UNHEX #"B" = BIT1(BIT1(BIT2 ZERO))
    | UNHEX #"c" = BIT2(BIT1(BIT2 ZERO))
    | UNHEX #"C" = BIT2(BIT1(BIT2 ZERO))
    | UNHEX #"d" = BIT1(BIT2(BIT2 ZERO))
    | UNHEX #"D" = BIT1(BIT2(BIT2 ZERO))
    | UNHEX #"e" = BIT2(BIT2(BIT2 ZERO))
    | UNHEX #"E" = BIT2(BIT2(BIT2 ZERO))
    | UNHEX #"f" = BIT1(BIT1(BIT1(BIT1 ZERO)))
    | UNHEX #"F" = BIT1(BIT1(BIT1(BIT1 ZERO)))
    | UNHEX other = raise Fail "not a hex character";


  val toBinString = toBaseString (fn n => (DIV2 n, MOD_2EXP ONE n)) BIN;
  fun fromBinString dstr =
    let val nlist = List.map UNBIN (String.explode dstr)
    in
      List.foldl (fn (a,b) =>  + a ( * b TWO)) (hd nlist) (tl nlist)
    end;

  val toDecString = toBaseString (fn n => DIVMOD(ZERO, (n, TEN))) DIGIT;
  fun fromDecString dstr =
    let val nlist = List.map UNDIGIT (String.explode dstr)
    in
      List.foldl (fn (a,b) =>  + a ( * b TEN)) (hd nlist) (tl nlist)
    end;

  val toOctString = toBaseString
        (fn n => (DIV2 (DIV2 (DIV2 n)), MOD_2EXP THREE n)) OCT;
  fun fromOctString dstr =
    let val nlist = List.map UNOCT (String.explode dstr)
    in
      List.foldl (fn (a,b) =>  + a ( * b EIGHT)) (hd nlist) (tl nlist)
    end;

  val toHexString = toBaseString
        (fn n => (DIV2 (DIV2 (DIV2 (DIV2 n))), MOD_2EXP FOUR n)) HEX;
  fun fromHexString dstr =
    let val nlist = List.map UNHEX (String.explode dstr)
    in
      List.foldl (fn (a,b) =>  + a ( * b SIXTEEN)) (hd nlist) (tl nlist)
    end;

  (* Uncomment to add mappings to portableML/Arbnum.sml (+ add to signature)

  fun Arbnum2num m =
        if m = Arbnum.zero then ZERO else
          let val n = Arbnum2num (Arbnum.div2 m) in
            if Arbnum.mod2 m = Arbnum.zero then
              iDUB n
            else
              BIT1 n
          end

  fun num2Arbnum ZERO = Arbnum.zero
    | num2Arbnum (BIT1 n) = Arbnum.plus1(Arbnum.times2(num2Arbnum n))
    | num2Arbnum (BIT2 n) = Arbnum.plus2(Arbnum.times2(num2Arbnum n))

  fun toDecString n = Arbnum.toString (num2Arbnum n);
  *)

  (* Installed in MoscowML with Meta.installPP *)

  fun ppBin ppstrm n = PP.add_string ppstrm (toBinString n);
  fun ppOct ppstrm n = PP.add_string ppstrm (toOctString n);
  fun ppDec ppstrm n = PP.add_string ppstrm (toDecString n);
  fun ppHex ppstrm n = PP.add_string ppstrm (toHexString n);
  val toString = toDecString;
  val fromString = fromDecString;
  val pp_num = ppHex;

  fun fromInt i = fromDecString (Int.toString i)
  fun toInt n =
    let fun num2int ZERO = 0
      | num2int (BIT1 n) = Int.+(Int.*(2, num2int n), 1)
      | num2int (BIT2 n) = Int.+(Int.*(2, num2int n), 2)
    in
      SOME (num2int n) handle Overflow => NONE
    end;


end
