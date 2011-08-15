structure mKML :> mKML =
struct
  nonfix ansterm reify walkstar stepgoal isDEMPTY list_to_defs DLOOKUP
         evalex extend_env primdenv unify OPTION_BIND ext_s_check oc
         walk ConsInf Sing Inc Apply EmptyInf Bind Mplus Gexpr DUPDATE
         DEMPTY NonRec Rec Call LetRec Let LetVar Disj Conj EConst EPair
         EVar Const Pair Var String Num Bool Null * / div mod + - ^ @ <>
         > < >= <= := o before;
  
  open numML
  open fmapML
  
  datatype const = Null | Bool of bool | Num of num | String of string
  datatype term = Var of num | Pair of term * term | Const of const
  type env = (string, term) fmap
  type ('a,'b) alist = ('a * 'b) list
  
  datatype expr
       = EVar of string | EPair of expr * expr | EConst of const
  datatype gexpr
       = Conj of gexpr * gexpr
       | Disj of gexpr * gexpr
       | LetVar of string * gexpr
       | Let of (string * (string list * gexpr)) * gexpr
       | LetRec of (string, string list * gexpr) alist * gexpr
       | Call of string * expr list
  datatype defs
       = Rec of (string, string list * gexpr) fmap
       | NonRec of (string * (string list * gexpr))
  datatype denv = DEMPTY | DUPDATE of denv * env * defs
  type subst = (num, term) fmap
  
  datatype goal
       = Gexpr of (subst * num) * env * denv * gexpr
       | Mplus of inf * goal
       | Bind of inf * env * denv * gexpr
  and
   inf
       = EmptyInf
       | Apply of goal
       | Inc of goal
       | Sing of (subst * num)
       | ConsInf of (subst * num) * goal
  fun walk s (Var(n)) =
        (case FLOOKUP s n
         of optionML.NONE => Var(n) | SOME(t) => walk s t)
    | walk s (Pair(t1,t2)) = Pair(t1,t2)
    | walk s (Const(c)) = Const(c)
    
  fun oc s t v =
        case walk s t
         of Var(w) => v = w
          | Pair(t1,t2) => oc s t1 v orelse oc s t2 v
          | Const(c) => false
    
  fun ext_s_check s v t =
        if oc s t v then optionML.NONE else SOME(FUPDATE (s,(v,t)))
    
  fun OPTION_BIND optionML.NONE f = optionML.NONE
    | OPTION_BIND (SOME(x)) f = f x
    
  fun unify s t1 t2 =
        case (walk s t1,walk s t2)
         of (Var(v1),Var(v2)) =>
               SOME(if v1 = v2 then s else FUPDATE (s,(v1,Var(v2))))
          | (Var(v1),Pair(v27,v28)) => ext_s_check s v1 (Pair(v27,v28))
          | (Var(v1),Const(v29)) => ext_s_check s v1 (Const(v29))
          | (Pair(t1a,t1d),Var(v34)) =>
               ext_s_check s v34 (Pair(t1a,t1d))
          | (Pair(t1a,t1d),Pair(t2a,t2d)) =>
               OPTION_BIND (unify s t1a t2a) (fn sx => unify sx t1d t2d)
          | (Pair(t1a,t1d),Const(v37)) => optionML.NONE
          | (Const(c1),Var(v42)) => ext_s_check s v42 (Const(c1))
          | (Const(c1),Pair(v43,v44)) => optionML.NONE
          | (Const(c1),Const(c2)) =>
               if c1 = c2 then
                 SOME(s)
               else optionML.NONE
    
  val primdenv =
        DUPDATE(DEMPTY,FEMPTY,
                NonRec(("Eqv",
                        (["t1","t2"],
                         Call("Eqv",[EVar("t1"),EVar("t2")])))))
    
  fun extend_env e v t = FUPDATE (e,(v,t))
    
  fun evalex env (EVar(v)) = FAPPLY env v
    | evalex env (EPair(e1,e2)) = Pair(evalex env e1,evalex env e2)
    | evalex env (EConst(c)) = Const(c)
    
  fun DLOOKUP DEMPTY name = optionML.NONE
    | DLOOKUP (DUPDATE(denv,env,defs)) name =
        (case
           case defs
            of Rec(dict) => FLOOKUP dict name
             | NonRec((xname,(fmls,body))) =>
                  if name = xname then
                    SOME((fmls,body))
                  else optionML.NONE
         of optionML.NONE => DLOOKUP denv name
          | SOME((fmls,body)) => SOME((denv,(env,(defs,(fmls,body))))))
    
  fun list_to_defs ls =
        Rec(listML.FOLDL (fn d => fn (n,(f,b)) => FUPDATE (d,(n,(f,b))))
              FEMPTY ls)
    
  fun isDEMPTY DEMPTY = true
    | isDEMPTY (DUPDATE(v,v1,v2)) = false
    
  fun stepgoal (Mplus(EmptyInf,f)) = Apply(f)
    | stepgoal (Mplus(Apply(f'),f)) = Apply(Mplus(stepgoal f',f))
    | stepgoal (Mplus(Inc(f'),f)) = Inc(Mplus(Apply(f),f'))
    | stepgoal (Mplus(Sing(a),f)) = ConsInf(a,f)
    | stepgoal (Mplus(ConsInf(a,f'),f)) = ConsInf(a,Mplus(Apply(f),f'))
    | stepgoal (Bind(EmptyInf,e,d,g)) = EmptyInf
    | stepgoal (Bind(Apply(f),e,d,g)) = Apply(Bind(stepgoal f,e,d,g))
    | stepgoal (Bind(Inc(f),e,d,g)) = Inc(Bind(Apply(f),e,d,g))
    | stepgoal (Bind(Sing(a),e,d,g)) = Apply(Gexpr(a,e,d,g))
    | stepgoal (Bind(ConsInf(a,f),e,d,g)) =
        Apply(Mplus(Apply(Gexpr(a,e,d,g)),Bind(Apply(f),e,d,g)))
    | stepgoal (Gexpr((v11,v12),e,d,Conj(g1,g2))) =
        Apply(Bind(Apply(Gexpr((v11,v12),e,d,g1)),e,d,g2))
    | stepgoal (Gexpr((v13,v14),e,d,Disj(g1,g2))) =
        Apply(Mplus(Apply(Gexpr((v13,v14),e,d,g1)),
                    Gexpr((v13,v14),e,d,g2)))
    | stepgoal (Gexpr((s,n),e,d,LetVar(v,g))) =
        Apply(Gexpr((s,+ n ONE),extend_env e v (Var(n)),d,g))
    | stepgoal (Gexpr((v15,v16),e,d,LetRec(ls,g))) =
        Apply(Gexpr((v15,v16),e,DUPDATE(d,e,list_to_defs ls),g))
    | stepgoal (Gexpr((v17,v18),e,d,Let(nfb,g))) =
        Apply(Gexpr((v17,v18),e,DUPDATE(d,e,NonRec(nfb)),g))
    | stepgoal (Gexpr((v19,v20),e,d,Call(name,args))) =
        (case DLOOKUP d name
         of optionML.NONE => raise Fail "ARB"
          | SOME((cd,(ce,(defs,(fmls,g))))) =>
               let val ce' =
                       listML.FOLDL (fn ce => fn (v,a) =>
                         extend_env ce v (evalex e a)) ce
                         (listML.ZIP (fmls,args))
               in
                  if isDEMPTY cd then
                 (case
                    unify (pairML.FST (v19,v20)) (FAPPLY ce' "t1")
                      (FAPPLY ce' "t2")
                  of optionML.NONE => EmptyInf
                   | SOME(sx) => Sing((sx,pairML.SND (v19,v20))))
               else
                 case defs
                  of Rec(v) =>
                        Inc(Gexpr((v19,v20),ce',DUPDATE(cd,ce,defs),g))
                   | NonRec(v1) => Apply(Gexpr((v19,v20),ce',cd,g))
               end)
    
  fun walkstar s t =
        case walk s t
         of Var(v4) => Var(v4)
          | Pair(t1,t2) => Pair(walkstar s t1,walkstar s t2)
          | Const(v7) => Const(v7)
    
  fun reify s (Var(v)) =
        (case FLOOKUP s v
         of optionML.NONE =>
               let val n = setML.CARD (FDOM s)
               in
                  (Var(n),FUPDATE (s,(v,n)))
               end
          | SOME(n) => (Var(n),s))
    | reify s (Pair(t1,t2)) =
        let val (t1',s') = reify s t1
            val (t2',s'') = reify s' t2
        in
           (Pair(t1',t2'),s'')
        end
    | reify s (Const(c)) = (Const(c),s)
    
  fun ansterm s = pairML.FST (reify FEMPTY (walkstar s (Var(ZERO))))
    
end
