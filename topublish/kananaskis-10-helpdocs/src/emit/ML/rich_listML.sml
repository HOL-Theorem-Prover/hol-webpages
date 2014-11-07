structure rich_listML :> rich_listML =
struct
  nonfix UNZIP_SND UNZIP_FST SUFFIX SEG SCANR SCANL REPLICATE PREFIX
         SPLITP LUPDATE SPLITP_AUX OR_EL IS_SUBLIST isPREFIX LASTN
         BUTLASTN TAKE ELL DROP AND_EL * / div mod + - ^ @ <> > < >= <=
         := o before;

  open pairML
  open numML
  open listML

  val AND_EL = EVERY combinML.I

  fun DROP n l =
        if n = ZERO then l
        else
          if l = [] then
          raise (Fail "DROP: List too short")
        else DROP (PRE n) (TL l)

  fun ELL n l = if n = ZERO then LAST l else ELL (PRE n) (FRONT l)

  fun TAKE n l =
        if n = ZERO then []
        else
          if l = [] then
          raise (Fail "TAKE: List too short")
        else HD l::TAKE (PRE n) (TL l)

  fun BUTLASTN n l =
        let val m = LENGTH l
        in
           if <= n m then
          TAKE (- m n) l
        else raise (Fail "BUTLASTN: longer than list")
        end

  fun LASTN n l =
        let val m = LENGTH l
        in
           if <= n m then
          DROP (- m n) l
        else raise (Fail "LASTN: longer than list")
        end

  fun isPREFIX [] l = true
    | isPREFIX (x::l) [] = false
    | isPREFIX (x2::l2) (x1::l1) = (x1 = x2) andalso isPREFIX l2 l1

  fun IS_SUBLIST l [] = true
    | IS_SUBLIST [] (x::l) = false
    | IS_SUBLIST (x1::l1) (x2::l2) =
        (x1 = x2) andalso isPREFIX l2 l1 orelse IS_SUBLIST l1 (x2::l2)

  val OR_EL = EXISTS combinML.I

  fun SPLITP_AUX acc P [] = (acc,[])
    | SPLITP_AUX acc P (h::t) =
        (if P h then (acc,h::t) else SPLITP_AUX (APPEND acc [h]) P t)

  fun LUPDATE e n [] = []
    | LUPDATE e n (x::l) =
        (if n = ZERO then e::l else x::LUPDATE e (PRE n) l)

  fun SPLITP x' x = SPLITP_AUX [] x' x

  fun PREFIX P l = FST (SPLITP (combinML.o not P) l)

  fun REPLICATE n l = if n = ZERO then [] else l::REPLICATE (PRE n) l

  fun SCANL f e [] = [e]
    | SCANL f e (x::l) = e::SCANL f (f e x) l

  fun SCANR f e [] = [e]
    | SCANR f e (x::l) = f x (HD (SCANR f e l))::SCANR f e l

  fun SEG m k l =
        if m = ZERO then []
        else
          if l = [] then
          raise (Fail "SEG: List too short")
        else
          if k = ZERO then
          HD l::SEG (PRE m) ZERO (TL l)
        else SEG m (PRE k) (TL l)

  fun SUFFIX P l =
        FOLDL (fn l' => fn x => if P x then SNOC x l' else []) [] l

  fun UNZIP_FST l = FST (UNZIP l)

  fun UNZIP_SND l = SND (UNZIP l)

end
