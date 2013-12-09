structure sortingML :> sortingML =
struct
  nonfix SORTED QSORT PARTITION PART * / div mod + - ^ @ <> > < >= <= :=
         o before;

  open listML

  fun PART P [] l1 l2 = (l1,l2)
    | PART P (h::rst) l1 l2 =
        (if P h then PART P rst (h::l1) l2 else PART P rst l1 (h::l2))

  fun PARTITION P l = PART P l [] []

  fun QSORT ord [] = []
    | QSORT ord (h::t) =
        let val (l1,l2) = PARTITION (fn y => ord y h) t
        in
           APPEND (APPEND (QSORT ord l1) [h]) (QSORT ord l2)
        end

  fun SORTED R [] = true
    | SORTED R [x] = true
    | SORTED R (x::y::rst) = R x y andalso SORTED R (y::rst)

end
