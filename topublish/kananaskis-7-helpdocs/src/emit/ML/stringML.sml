structure stringML :> stringML =
struct
  nonfix string_ge string_gt string_le char_ge char_gt char_le char_lt
         PAD_RIGHT PAD_LEFT toUpper toLower isCntrl isAscii isPunct
         isGraph isSpace isPrint isAlphaNum isHexDigit isAlpha isDigit
         isUpper isLower isPREFIX APPEND char_size * / div mod + - ^ @
         <> > < >= <= := o before;
  
  open numML
  open listML
  open optionML
  
  type char = Char.char;
  type string = String.string;
  fun CHR n = Char.chr(valOf(Int.fromString(numML.toDecString n)));
  fun ORD c = numML.fromDecString(Int.toString(Char.ord c));
  fun STRING c s = String.^(Char.toString c,s);
  fun DEST_STRING s = if s = "" then NONE 
          else SOME(String.sub(s,0),String.extract(s,1,NONE));
  fun string_lt a b = String.compare(a,b) = LESS
  val IMPLODE = String.implode
  val EXPLODE = String.explode
  fun STRLEN s = LENGTH (EXPLODE s)
  fun char_size c = ZERO
    
  fun STRCAT s1 s2 = FOLDR STRING s2 (EXPLODE s1)
    
  fun isPREFIX s1 s2 =
        case (DEST_STRING s1,DEST_STRING s2)
         of (NONE,v1) => true
          | (SOME((c1,t1)),NONE) => false
          | (SOME((c1,t1)),SOME((c2,t2))) =>
               (c1 = c2) andalso isPREFIX t1 t2
    
  fun isLower c =
        <= (fromString "97") (ORD c) andalso
        <= (ORD c) (fromString "122")
    
  fun isUpper c =
        <= (fromString "65") (ORD c) andalso
        <= (ORD c) (fromString "90")
    
  fun isDigit c =
        <= (fromString "48") (ORD c) andalso
        <= (ORD c) (fromString "57")
    
  fun isAlpha c = isLower c orelse isUpper c
    
  fun isHexDigit c =
        <= (fromString "48") (ORD c) andalso
        <= (ORD c) (fromString "57") orelse
        (<= (fromString "97") (ORD c) andalso
         <= (ORD c) (fromString "102") orelse
         <= (fromString "65") (ORD c) andalso
         <= (ORD c) (fromString "70"))
    
  fun isAlphaNum c = isAlpha c orelse isDigit c
    
  fun isPrint c =
        <= (fromString "32") (ORD c) andalso
        < (ORD c) (fromString "127")
    
  fun isSpace c =
        (ORD c = (fromString "32")) orelse
        <= (fromString "9") (ORD c) andalso <= (ORD c) (fromString "13")
    
  fun isGraph c = isPrint c andalso not (isSpace c)
    
  fun isPunct c = isGraph c andalso not (isAlphaNum c)
    
  fun isAscii c = <= (ORD c) (fromString "127")
    
  fun isCntrl c =
        < (ORD c) (fromString "32") orelse <= (fromString "127") (ORD c)
    
  fun toLower c =
        if isUpper c then CHR (+ (ORD c) (fromString "32")) else c
    
  fun toUpper c =
        if isLower c then CHR (- (ORD c) (fromString "32")) else c
    
  fun PAD_LEFT c n s =
        STRCAT (IMPLODE (GENLIST (combinML.K c) (- n (STRLEN s)))) s
    
  fun PAD_RIGHT c n s =
        STRCAT s (IMPLODE (GENLIST (combinML.K c) (- n (STRLEN s))))
    
  fun char_lt a b = < (ORD a) (ORD b)
    
  fun char_le a b = <= (ORD a) (ORD b)
    
  fun char_gt a b = > (ORD a) (ORD b)
    
  fun char_ge a b = >= (ORD a) (ORD b)
    
  fun string_le s1 s2 = (s1 = s2) orelse string_lt s1 s2
    
  fun string_gt s1 s2 = string_lt s2 s1
    
  fun string_ge s1 s2 = string_le s2 s1
    
end
