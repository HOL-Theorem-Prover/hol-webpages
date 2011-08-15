signature mKML = 
sig
  type num = numML.num
  type ('a,'b) fmap = ('a,'b) fmapML.fmap
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
  val walk : subst -> term -> term
  val oc : subst -> term -> num -> bool
  val ext_s_check : subst -> num -> term -> subst option
  val OPTION_BIND : 'b option -> ('b -> 'a option) -> 'a option
  val unify : subst -> term -> term -> subst option
  val primdenv : denv
  val extend_env : ('a, 'b) fmap -> 'a -> 'b -> ('a, 'b) fmap
  val evalex : env -> expr -> term
  val DLOOKUP
     : denv ->
       string -> (denv * (env * (defs * (string list * gexpr)))) option
  val list_to_defs : (string, string list * gexpr) alist -> defs
  val isDEMPTY : denv -> bool
  val stepgoal : goal -> inf
  val walkstar : subst -> term -> term
  val reify : (num, num) fmap -> term -> term * (num, num) fmap
  val ansterm : subst -> term
end
