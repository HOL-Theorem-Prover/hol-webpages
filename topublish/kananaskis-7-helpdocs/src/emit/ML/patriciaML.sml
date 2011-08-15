structure patriciaML :> patriciaML =
struct
  nonfix ADD_LIST FIND IS_EMPTY INSERT_PTREE IN_PTREE IS_PTREE DEPTH
         SIZE EXISTS_LEAF EVERY_LEAF TRANSFORM KEYS TRAVERSE REMOVE
         BRANCH ADD JOIN PEEK BRANCHING_BIT Branch Leaf Empty * / div
         mod + - ^ @ <> > < >= <= := o before;
  
  open numML
  open optionML
  open setML
  
  datatype 'a ptree
       = Empty
       | Leaf of num * 'a
       | Branch of num * num * 'a ptree * 'a ptree
  fun toList Empty = []
    | toList (Leaf(j,d)) = [(j,d)]
    | toList (Branch(p,m,l,r)) =
        listML.APPEND (toList l) (toList r)
  fun BRANCHING_BIT p0 p1 =
        if (ODD p0 = EVEN p1) orelse (p0 = p1) then ZERO
        else SUC (BRANCHING_BIT (DIV2 p0) (DIV2 p1))
    
  fun PEEK Empty k = NONE
    | PEEK (Leaf(j,d)) k = (if k = j then SOME(d) else NONE)
    | PEEK (Branch(p,m,l,r)) k = PEEK (if bitML.BIT m k then l else r) k
    
  fun JOIN (p0,(t0,(p1,t1))) =
        let val m = BRANCHING_BIT p0 p1
        in
           if bitML.BIT m p0 then
          Branch(MOD_2EXP m p0,m,t0,t1)
        else Branch(MOD_2EXP m p0,m,t1,t0)
        end
    
  fun ADD Empty (k,e) = Leaf(k,e)
    | ADD (Leaf(j,d)) (k,e) =
        (if j = k then
           Leaf(k,e)
         else JOIN (k,(Leaf(k,e),(j,Leaf(j,d)))))
    | ADD (Branch(p,m,l,r)) (k,e) =
        (if bitML.MOD_2EXP_EQ m k p then
           (if bitML.BIT m k then
              Branch(p,m,ADD l (k,e),r)
            else Branch(p,m,l,ADD r (k,e)))
         else JOIN (k,(Leaf(k,e),(p,Branch(p,m,l,r)))))
    
  fun BRANCH (p,(m,(Empty,Empty))) = Empty
    | BRANCH (p,(m,(Empty,Leaf(v24,v25)))) = Leaf(v24,v25)
    | BRANCH (p,(m,(Empty,Branch(v26,v27,v28,v29)))) =
        Branch(v26,v27,v28,v29)
    | BRANCH (p,(m,(Leaf(v6,v7),Empty))) = Leaf(v6,v7)
    | BRANCH (p,(m,(Branch(v8,v9,v10,v11),Empty))) =
        Branch(v8,v9,v10,v11)
    | BRANCH (p,(m,(Leaf(v12,v13),Leaf(v42,v43)))) =
        Branch(p,m,Leaf(v12,v13),Leaf(v42,v43))
    | BRANCH (p,(m,(Leaf(v12,v13),Branch(v44,v45,v46,v47)))) =
        Branch(p,m,Leaf(v12,v13),Branch(v44,v45,v46,v47))
    | BRANCH (p,(m,(Branch(v14,v15,v16,v17),Leaf(v54,v55)))) =
        Branch(p,m,Branch(v14,v15,v16,v17),Leaf(v54,v55))
    | BRANCH (p,(m,(Branch(v14,v15,v16,v17),Branch(v56,v57,v58,v59)))) =
        Branch(p,m,Branch(v14,v15,v16,v17),Branch(v56,v57,v58,v59))
    
  fun REMOVE Empty k = Empty
    | REMOVE (Leaf(j,d)) k = (if j = k then Empty else Leaf(j,d))
    | REMOVE (Branch(p,m,l,r)) k =
        (if bitML.MOD_2EXP_EQ m k p then
           (if bitML.BIT m k then
              BRANCH (p,(m,(REMOVE l k,r)))
            else BRANCH (p,(m,(l,REMOVE r k))))
         else Branch(p,m,l,r))
    
  fun TRAVERSE Empty = []
    | TRAVERSE (Leaf(j,d)) = [j]
    | TRAVERSE (Branch(p,m,l,r)) =
        listML.APPEND (TRAVERSE l) (TRAVERSE r)
    
  fun KEYS t = sortingML.QSORT < (TRAVERSE t)
    
  fun TRANSFORM f Empty = Empty
    | TRANSFORM f (Leaf(j,d)) = Leaf(j,f d)
    | TRANSFORM f (Branch(p,m,l,r)) =
        Branch(p,m,TRANSFORM f l,TRANSFORM f r)
    
  fun EVERY_LEAF P Empty = true
    | EVERY_LEAF P (Leaf(j,d)) = P j d
    | EVERY_LEAF P (Branch(p,m,l,r)) =
        EVERY_LEAF P l andalso EVERY_LEAF P r
    
  fun EXISTS_LEAF P Empty = false
    | EXISTS_LEAF P (Leaf(j,d)) = P j d
    | EXISTS_LEAF P (Branch(p,m,l,r)) =
        EXISTS_LEAF P l orelse EXISTS_LEAF P r
    
  fun SIZE t = listML.LENGTH (TRAVERSE t)
    
  fun DEPTH Empty = ZERO
    | DEPTH (Leaf(j,d)) = ONE
    | DEPTH (Branch(p,m,l,r)) = + ONE (MAX (DEPTH l) (DEPTH r))
    
  fun IS_PTREE Empty = true
    | IS_PTREE (Leaf(k,d)) = true
    | IS_PTREE (Branch(p,m,l,r)) =
        < p (EXP TWO m) andalso
        (IS_PTREE l andalso
         (IS_PTREE r andalso
          (not (l = Empty) andalso
           (not (r = Empty) andalso
            (EVERY_LEAF (fn k => fn d =>
               bitML.MOD_2EXP_EQ m k p andalso bitML.BIT m k) l andalso
             EVERY_LEAF (fn k => fn d =>
               bitML.MOD_2EXP_EQ m k p andalso not (bitML.BIT m k))
               r)))))
    
  fun IN_PTREE n t = IS_SOME (PEEK t n)
    
  fun INSERT_PTREE n t = ADD t (n,())
    
  fun IS_EMPTY Empty = true
    | IS_EMPTY (Leaf(v,v1)) = false
    | IS_EMPTY (Branch(v2,v3,v4,v5)) = false
    
  fun FIND t k = THE (PEEK t k)
    
  fun ADD_LIST x x' = listML.FOLDL ADD x x'
    
end
