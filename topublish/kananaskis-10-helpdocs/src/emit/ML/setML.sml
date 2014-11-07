structure setML :> setML =
struct
  nonfix POW count MIN_SET MAX_SET SUM_SET SUM_IMAGE IS_EMPTY
         LIST_TO_SET CROSS DISJOINT CARD BIGINTER BIGUNION IMAGE PSUBSET
         SUBSET DIFF DELETE INTER UNION IN INSERT EMPTY * / div mod + -
         ^ @ <> > < >= <= := o before;

  datatype 'a set = EMPTY | INSERT of 'a * 'a set
  open numML

  fun IN x EMPTY = false
    | IN x (INSERT (y,s)) = (x = y) orelse IN x s

  fun UNION EMPTY s = s
    | UNION (INSERT (x,s)) t =
        (if IN x t then UNION s t else INSERT (x,UNION s t))

  fun INTER EMPTY s = EMPTY
    | INTER (INSERT (x,s)) t =
        (if IN x t then INSERT (x,INTER s t) else INTER s t)

  fun DELETE EMPTY x = EMPTY
    | DELETE (INSERT (x,s)) y =
        (if x = y then DELETE s y else INSERT (x,DELETE s y))

  fun DIFF s EMPTY = s
    | DIFF s (INSERT (x,t)) = DIFF (DELETE s x) t

  fun SUBSET EMPTY s = true
    | SUBSET (INSERT (x,s)) t = IN x t andalso SUBSET s t

  fun PSUBSET s1 s2 = SUBSET s1 s2 andalso not (SUBSET s2 s1)

  fun IMAGE f EMPTY = EMPTY
    | IMAGE f (INSERT (x,s)) = INSERT (f x,IMAGE f s)

  fun BIGUNION EMPTY = EMPTY
    | BIGUNION (INSERT (s,P)) = UNION s (BIGUNION P)

  fun BIGINTER EMPTY = raise (Fail "BIGINTER: empty set")
    | BIGINTER (INSERT (P,EMPTY)) = P
    | BIGINTER (INSERT (P,B)) = INTER P (BIGINTER B)

  fun CARD EMPTY = ZERO
    | CARD (INSERT (x,s)) = (if IN x s then CARD s else SUC (CARD s))

  fun DISJOINT EMPTY s = true
    | DISJOINT (INSERT (x,s)) t = DISJOINT s t andalso not (IN x t)

  fun CROSS EMPTY s2 = EMPTY
    | CROSS (INSERT (a,s1)) s2 =
        UNION (IMAGE (fn y => (a,y)) s2) (CROSS s1 s2)

  fun LIST_TO_SET [] = EMPTY
    | LIST_TO_SET (h::t) = INSERT (h,LIST_TO_SET t)

  fun IS_EMPTY EMPTY = true
    | IS_EMPTY (INSERT (x,s)) = false

  fun SUM_IMAGE f EMPTY = ZERO
    | SUM_IMAGE f (INSERT (e,s)) = + (f e) (SUM_IMAGE f (DELETE s e))

  fun SUM_SET EMPTY = ZERO
    | SUM_SET (INSERT (x,s)) = + x (SUM_SET (DELETE s x))

  fun MAX_SET EMPTY = ZERO
    | MAX_SET (INSERT (e,s)) = MAX e (MAX_SET s)

  fun MIN_SET EMPTY = raise (Fail "MIN_SET: empty set")
    | MIN_SET (INSERT (e,EMPTY)) = e
    | MIN_SET (INSERT (e1,INSERT (e2,s))) =
        MIN e1 (MIN_SET (INSERT (e2,s)))

  fun count n =
        if n = ZERO then EMPTY
        else let val p = PRE n in INSERT (p,count p) end

  fun POW EMPTY = INSERT (EMPTY,EMPTY)
    | POW (INSERT (e,s)) =
        let val ps = POW s
        in
           UNION (IMAGE (fn v1 => INSERT (e,v1)) ps) ps
        end

  fun fromList alist = listML.FOLDL (fn s => fn a => INSERT(a,s)) EMPTY alist
  fun toList EMPTY = []
    | toList (INSERT(a,s)) = a::toList s
end
