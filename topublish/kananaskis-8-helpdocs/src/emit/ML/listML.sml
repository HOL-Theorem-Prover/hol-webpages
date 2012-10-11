structure listML :> listML =
struct
  nonfix PAD_RIGHT PAD_LEFT list_size REV LEN LENGTH EL ALL_DISTINCT
         FRONT LAST REVERSE UNZIP ZIP MAP2 EXISTS EVERY GENLIST SNOC
         FOLDL FOLDR FILTER MEM MAP FLAT APPEND TL HD NULL * / div mod +
         - ^ @ <> > < >= <= := o before;

  open numML

  fun NULL [] = true
    | NULL (h::t) = false

  fun HD [] = raise (Fail "HD: Empty list")
    | HD (h::t) = h

  fun TL [] = raise (Fail "TL: Empty list")
    | TL (h::t) = t

  fun APPEND [] l = l
    | APPEND (h::l1) l2 = h::APPEND l1 l2

  fun FLAT [] = []
    | FLAT (h::t) = APPEND h (FLAT t)

  fun MAP f [] = []
    | MAP f (h::t) = f h::MAP f t

  fun MEM x [] = false
    | MEM x (h::t) = (x = h) orelse MEM x t

  fun FILTER P [] = []
    | FILTER P (h::t) = (if P h then h::FILTER P t else FILTER P t)

  fun FOLDR f e [] = e
    | FOLDR f e (x::l) = f x (FOLDR f e l)

  fun FOLDL f e [] = e
    | FOLDL f e (x::l) = FOLDL f (f e x) l

  fun SNOC x [] = [x]
    | SNOC x (x'::l) = x'::SNOC x l

  fun GENLIST f n =
        if n = ZERO then [] else SNOC (f (PRE n)) (GENLIST f (PRE n))

  fun EVERY P [] = true
    | EVERY P (h::t) = P h andalso EVERY P t

  fun EXISTS P [] = false
    | EXISTS P (h::t) = P h orelse EXISTS P t

  fun MAP2 f [] [] = []
    | MAP2 f [] (h::t) = raise (Fail "MAP2: unequal length lists")
    | MAP2 f (h::t) [] = raise (Fail "MAP2: unequal length lists")
    | MAP2 f (h1::t1) (h2::t2) = f h1 h2::MAP2 f t1 t2

  fun ZIP ([],[]) = []
    | ZIP ([],h::t) = raise (Fail "ZIP: unequal length lists")
    | ZIP (h::t,[]) = raise (Fail "ZIP: unequal length lists")
    | ZIP (x1::l1,x2::l2) = (x1,x2)::ZIP (l1,l2)

  fun UNZIP [] = ([],[])
    | UNZIP ((x,y)::t) = let val (L1,L2) = UNZIP t in (x::L1,y::L2) end

  fun REVERSE [] = []
    | REVERSE (h::t) = APPEND (REVERSE t) [h]

  fun LAST [] = raise (Fail "LAST: empty list")
    | LAST [x] = x
    | LAST (x::y::z) = LAST (y::z)

  fun FRONT [] = raise (Fail "FRONT: empty list")
    | FRONT [x] = []
    | FRONT (x::y::z) = x::FRONT (y::z)

  fun ALL_DISTINCT [] = true
    | ALL_DISTINCT (h::t) = not (MEM h t) andalso ALL_DISTINCT t

  fun EL n l = if n = ZERO then HD l else EL (PRE n) (TL l)

  fun LENGTH [] = ZERO
    | LENGTH (h::t) = + (LENGTH t) ONE

  fun LEN [] n = n
    | LEN (h::t) n = LEN t (+ n ONE)

  fun REV [] acc = acc
    | REV (h::t) acc = REV t (h::acc)

  fun list_size f [] = ZERO
    | list_size f (a0::a1) = + ONE (+ (f a0) (list_size f a1))

  fun PAD_LEFT c n s =
        APPEND (GENLIST (combinML.K c) (- n (LENGTH s))) s

  fun PAD_RIGHT c n s =
        APPEND s (GENLIST (combinML.K c) (- n (LENGTH s)))

end
