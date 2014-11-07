functor DiskFilesLrValsFun(structure Token : TOKEN)
 : sig structure ParserData : PARSER_DATA
       structure Tokens : DiskFiles_TOKENS
   end
 =
struct
structure ParserData=
struct
structure Header =
struct

open DiskFilesHeader HolKernel

fun warn s = TextIO.output(TextIO.stdErr, s ^ "\n")

type result = (id array *
               pretype array *
               pre_vc array *
               (string * prethm) list)
end
structure LrTable = Token.LrTable
structure Token = Token
local open LrTable in
val table=let val actionRows =
"\
\\001\000\001\000\000\000\000\000\
\\001\000\002\000\037\000\000\000\
\\001\000\002\000\038\000\000\000\
\\001\000\002\000\056\000\000\000\
\\001\000\003\000\028\000\000\000\
\\001\000\004\000\059\000\000\000\
\\001\000\005\000\032\000\000\000\
\\001\000\005\000\046\000\007\000\045\000\014\000\044\000\000\000\
\\001\000\006\000\052\000\000\000\
\\001\000\006\000\060\000\000\000\
\\001\000\008\000\004\000\000\000\
\\001\000\009\000\006\000\000\000\
\\001\000\010\000\010\000\000\000\
\\001\000\011\000\015\000\000\000\
\\001\000\012\000\036\000\000\000\
\\001\000\012\000\047\000\000\000\
\\001\000\012\000\048\000\000\000\
\\001\000\013\000\057\000\000\000\
\\001\000\013\000\064\000\000\000\
\\001\000\013\000\065\000\000\000\
\\001\000\014\000\008\000\000\000\
\\001\000\014\000\012\000\000\000\
\\001\000\014\000\017\000\000\000\
\\001\000\014\000\044\000\000\000\
\\001\000\014\000\050\000\000\000\
\\001\000\014\000\055\000\000\000\
\\001\000\014\000\061\000\000\000\
\\001\000\014\000\062\000\000\000\
\\067\000\000\000\
\\068\000\002\000\020\000\000\000\
\\069\000\000\000\
\\070\000\000\000\
\\071\000\000\000\
\\072\000\000\000\
\\073\000\015\000\027\000\016\000\026\000\000\000\
\\074\000\000\000\
\\075\000\000\000\
\\076\000\000\000\
\\077\000\000\000\
\\078\000\000\000\
\\079\000\014\000\050\000\000\000\
\\080\000\000\000\
\\081\000\017\000\035\000\018\000\034\000\000\000\
\\082\000\000\000\
\\083\000\000\000\
\\084\000\000\000\
\\085\000\000\000\
\\086\000\000\000\
\\087\000\000\000\
\\088\000\002\000\023\000\000\000\
\\089\000\000\000\
\\090\000\000\000\
\\091\000\005\000\032\000\000\000\
\\092\000\000\000\
\\093\000\000\000\
\\094\000\000\000\
\\095\000\005\000\046\000\014\000\044\000\000\000\
\\096\000\000\000\
\\097\000\000\000\
\\098\000\000\000\
\\099\000\000\000\
\\100\000\000\000\
\"
val actionRowNumbers =
"\010\000\011\000\020\000\012\000\
\\021\000\031\000\030\000\013\000\
\\022\000\036\000\035\000\029\000\
\\028\000\049\000\044\000\043\000\
\\034\000\032\000\004\000\049\000\
\\048\000\006\000\042\000\037\000\
\\014\000\001\000\002\000\050\000\
\\051\000\052\000\007\000\045\000\
\\015\000\016\000\024\000\038\000\
\\033\000\053\000\060\000\058\000\
\\056\000\008\000\061\000\023\000\
\\007\000\025\000\003\000\017\000\
\\040\000\057\000\054\000\005\000\
\\009\000\026\000\027\000\039\000\
\\041\000\007\000\059\000\018\000\
\\019\000\055\000\047\000\046\000\
\\000\000"
val gotoT =
"\
\\001\000\064\000\002\000\001\000\000\000\
\\005\000\003\000\000\000\
\\008\000\005\000\000\000\
\\012\000\007\000\000\000\
\\006\000\009\000\000\000\
\\003\000\011\000\000\000\
\\000\000\
\\015\000\012\000\000\000\
\\007\000\014\000\000\000\
\\009\000\016\000\000\000\
\\000\000\
\\004\000\017\000\000\000\
\\000\000\
\\016\000\020\000\017\000\019\000\000\000\
\\013\000\022\000\000\000\
\\000\000\
\\010\000\023\000\000\000\
\\000\000\
\\000\000\
\\016\000\027\000\017\000\019\000\000\000\
\\000\000\
\\018\000\029\000\022\000\028\000\000\000\
\\014\000\031\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\018\000\029\000\022\000\037\000\000\000\
\\019\000\041\000\020\000\040\000\021\000\039\000\023\000\038\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\011\000\047\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\021\000\049\000\023\000\038\000\000\000\
\\000\000\
\\000\000\
\\023\000\051\000\000\000\
\\019\000\052\000\020\000\040\000\021\000\039\000\023\000\038\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\011\000\056\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\019\000\061\000\020\000\040\000\021\000\039\000\023\000\038\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\"
val numstates = 65
val numrules = 34
val s = ref "" and index = ref 0
val string_to_int = fn () =>
let val i = !index
in index := i+2; Char.ord(String.sub(!s,i)) + Char.ord(String.sub(!s,i+1)) * 256
end
val string_to_list = fn s' =>
    let val len = String.size s'
        fun f () =
           if !index < len then string_to_int() :: f()
           else nil
   in index := 0; s := s'; f ()
   end
val string_to_pairlist = fn (conv_key,conv_entry) =>
     let fun f () =
         case string_to_int()
         of 0 => EMPTY
          | n => PAIR(conv_key (n-1),conv_entry (string_to_int()),f())
     in f
     end
val string_to_pairlist_default = fn (conv_key,conv_entry) =>
    let val conv_row = string_to_pairlist(conv_key,conv_entry)
    in fn () =>
       let val default = conv_entry(string_to_int())
           val row = conv_row()
       in (row,default)
       end
   end
val string_to_table = fn (convert_row,s') =>
    let val len = String.size s'
        fun f ()=
           if !index < len then convert_row() :: f()
           else nil
     in (s := s'; index := 0; f ())
     end
local
  val memo = Array.array(numstates+numrules,ERROR)
  val _ =let fun g i=(Array.update(memo,i,REDUCE(i-numstates)); g(i+1))
       fun f i =
            if i=numstates then g i
            else (Array.update(memo,i,SHIFT (STATE i)); f (i+1))
          in f 0 handle Subscript => ()
          end
in
val entry_to_action = fn 0 => ACCEPT | 1 => ERROR | j => Array.sub(memo,(j-2))
end
val gotoT=Array.fromList(string_to_table(string_to_pairlist(NT,STATE),gotoT))
val actionRows=string_to_table(string_to_pairlist_default(T,entry_to_action),actionRows)
val actionRowNumbers = string_to_list actionRowNumbers
val actionT = let val actionRowLookUp=
let val a=Array.fromList(actionRows) in fn i=>Array.sub(a,i) end
in Array.fromList(map actionRowLookUp actionRowNumbers)
end
in LrTable.mkLrTable {actions=actionT,gotos=gotoT,numRules=numrules,
numStates=numstates,initialState=STATE 0}
end
end
local open Header in
type pos = int
type arg = unit
structure MlyValue =
struct
datatype svalue = VOID | ntVOID of unit | NUMBER of  (int)
 | ID of  (string) | tmid of  (int) | termlist of  (preterm list)
 | base_term of  (preterm) | term_c of  (preterm)
 | term_a of  (preterm) | term of  (preterm)
 | namethm of  ( ( string * prethm ) )
 | namethm_list of  ( ( string * prethm )  list)
 | theorems of  ( ( string * prethm )  list) | termdecl of  (pre_vc)
 | termdecl_list of  ( ( int,pre_vc )  Binarymap.dict)
 | terms_section of  ( ( int,pre_vc )  Binarymap.dict)
 | intlist_ne of  (int list) | typedecl of  (pretype)
 | typedecl_list of  ( ( int,pretype )  Binarymap.dict)
 | types_section of  ( ( int,pretype )  Binarymap.dict)
 | idpair of  (id) | idpair_list of  ( ( int,id )  Binarymap.dict)
 | ids_section of  ( ( int,id )  Binarymap.dict)
 | theoryfile of  (result)
end
type svalue = MlyValue.svalue
type result = result
end
structure EC=
struct
open LrTable
val is_keyword =
fn (T 7) => true | (T 8) => true | (T 9) => true | (T 10) => true |
_ => false
val preferred_change =
nil
val noShift =
fn (T 0) => true | _ => false
val showTerminal =
fn (T 0) => "EOF"
  | (T 1) => "ID"
  | (T 2) => "DOLLAR"
  | (T 3) => "FULLSTOP"
  | (T 4) => "LPAREN"
  | (T 5) => "RPAREN"
  | (T 6) => "BACKSLASH"
  | (T 7) => "IDS"
  | (T 8) => "TYPES"
  | (T 9) => "TERMS"
  | (T 10) => "THEOREMS"
  | (T 11) => "LBRACKET"
  | (T 12) => "RBRACKET"
  | (T 13) => "NUMBER"
  | (T 14) => "TYV"
  | (T 15) => "TYOP"
  | (T 16) => "TMV"
  | (T 17) => "TMC"
  | _ => "bogus-term"
local open Header in
val errtermvalue=
fn _ => MlyValue.VOID
end
val terms = (T 0) :: (T 2) :: (T 3) :: (T 4) :: (T 5) :: (T 6) :: (T 7
) :: (T 8) :: (T 9) :: (T 10) :: (T 11) :: (T 12) :: (T 14) :: (T 15)
 :: (T 16) :: (T 17) :: nil
end
structure Actions =
struct
type int = Int.int
exception mlyAction of int
local open Header in
val actions =
fn (i392:int,defaultPos,stack,
    (()):arg) =>
case (i392,stack)
of (0,(_,(MlyValue.theorems theorems,_,theorems1right))::(_,(
MlyValue.terms_section terms_section,_,_))::(_,(MlyValue.types_section
types_section,_,_))::(_,(MlyValue.ids_section ids_section,
ids_section1left,_))::rest671) => let val result=MlyValue.theoryfile((
ids_section, types_section, terms_section, theorems))
 in (LrTable.NT 0,(result,ids_section1left,theorems1right),rest671)
 end
| (1,(_,(MlyValue.idpair_list idpair_list,_,idpair_list1right))::_::(_
,(_,IDS1left,_))::rest671) => let val result=MlyValue.ids_section((
idpair_list))
 in (LrTable.NT 1,(result,IDS1left,idpair_list1right),rest671) end
| (2,(_,(_,NUMBER1left,NUMBER1right))::rest671) => let val result=
MlyValue.ntVOID(())
 in (LrTable.NT 7,(result,NUMBER1left,NUMBER1right),rest671) end
| (3,rest671) => let val result=MlyValue.idpair_list((
Binarymap.mkDict Int.compare))
 in (LrTable.NT 2,(result,defaultPos,defaultPos),rest671) end
| (4,(_,(MlyValue.idpair idpair,_,idpair1right))::(_,(
MlyValue.idpair_list idpair_list,idpair_list1left,_))::rest671) => let
val result=MlyValue.idpair_list((
Binarymap.insert(idpair_list, Binarymap.numItems idpair_list,
                                   idpair)
))
 in (LrTable.NT 2,(result,idpair_list1left,idpair1right),rest671) end
| (5,(_,(MlyValue.ID ID2,_,ID2right))::_::(_,(MlyValue.ID ID1,ID1left,
_))::rest671) => let val result=MlyValue.idpair((
 {Thy = ID1, Name = ID2 } ))
 in (LrTable.NT 3,(result,ID1left,ID2right),rest671) end
| (6,(_,(MlyValue.typedecl_list typedecl_list,_,typedecl_list1right))
::_::(_,(_,TYPES1left,_))::rest671) => let val result=
MlyValue.types_section((typedecl_list))
 in (LrTable.NT 4,(result,TYPES1left,typedecl_list1right),rest671) end
| (7,(_,(_,NUMBER1left,NUMBER1right))::rest671) => let val result=
MlyValue.ntVOID(())
 in (LrTable.NT 5,(result,NUMBER1left,NUMBER1right),rest671) end
| (8,rest671) => let val result=MlyValue.typedecl_list((
Binarymap.mkDict Int.compare))
 in (LrTable.NT 8,(result,defaultPos,defaultPos),rest671) end
| (9,(_,(MlyValue.typedecl typedecl,_,typedecl1right))::(_,(
MlyValue.typedecl_list typedecl_list,typedecl_list1left,_))::rest671)
 => let val result=MlyValue.typedecl_list((
Binarymap.insert(typedecl_list,
                                    Binarymap.numItems typedecl_list,
                                    typedecl)
))
 in (LrTable.NT 8,(result,typedecl_list1left,typedecl1right),rest671)
 end
| (10,(_,(MlyValue.ID ID,_,ID1right))::(_,(_,TYV1left,_))::rest671) =>
let val result=MlyValue.typedecl((ptv ID))
 in (LrTable.NT 9,(result,TYV1left,ID1right),rest671) end
| (11,(_,(_,_,RBRACKET1right))::(_,(MlyValue.intlist_ne intlist_ne,_,_
))::_::(_,(_,TYOP1left,_))::rest671) => let val result=
MlyValue.typedecl((ptop (hd intlist_ne, tl intlist_ne)))
 in (LrTable.NT 9,(result,TYOP1left,RBRACKET1right),rest671) end
| (12,(_,(MlyValue.NUMBER NUMBER,NUMBER1left,NUMBER1right))::rest671)
 => let val result=MlyValue.intlist_ne(([NUMBER]))
 in (LrTable.NT 10,(result,NUMBER1left,NUMBER1right),rest671) end
| (13,(_,(MlyValue.intlist_ne intlist_ne,_,intlist_ne1right))::(_,(
MlyValue.NUMBER NUMBER,NUMBER1left,_))::rest671) => let val result=
MlyValue.intlist_ne((NUMBER::intlist_ne))
 in (LrTable.NT 10,(result,NUMBER1left,intlist_ne1right),rest671) end
| (14,(_,(MlyValue.termdecl_list termdecl_list,_,termdecl_list1right))
::_::(_,(_,TERMS1left,_))::rest671) => let val result=
MlyValue.terms_section((termdecl_list))
 in (LrTable.NT 11,(result,TERMS1left,termdecl_list1right),rest671)
 end
| (15,(_,(_,NUMBER1left,NUMBER1right))::rest671) => let val result=
MlyValue.ntVOID(())
 in (LrTable.NT 6,(result,NUMBER1left,NUMBER1right),rest671) end
| (16,rest671) => let val result=MlyValue.termdecl_list((
Binarymap.mkDict Int.compare))
 in (LrTable.NT 12,(result,defaultPos,defaultPos),rest671) end
| (17,(_,(MlyValue.termdecl termdecl,_,termdecl1right))::(_,(
MlyValue.termdecl_list termdecl_list,termdecl_list1left,_))::rest671)
 => let val result=MlyValue.termdecl_list((
Binarymap.insert(termdecl_list,
                                     Binarymap.numItems termdecl_list,
                                     termdecl)
))
 in (LrTable.NT 12,(result,termdecl_list1left,termdecl1right),rest671)
 end
| (18,(_,(_,_,RBRACKET1right))::(_,(MlyValue.NUMBER NUMBER,_,_))::(_,(
MlyValue.ID ID,_,_))::_::(_,(_,TMV1left,_))::rest671) => let val result
=MlyValue.termdecl((ptm_v(ID, NUMBER)))
 in (LrTable.NT 13,(result,TMV1left,RBRACKET1right),rest671) end
| (19,(_,(_,_,RBRACKET1right))::(_,(MlyValue.NUMBER NUMBER2,_,_))::(_,
(MlyValue.NUMBER NUMBER1,_,_))::_::(_,(_,TMC1left,_))::rest671) => let
val result=MlyValue.termdecl((ptm_c(NUMBER1, NUMBER2)))
 in (LrTable.NT 13,(result,TMC1left,RBRACKET1right),rest671) end
| (20,(_,(MlyValue.namethm_list namethm_list,_,namethm_list1right))::(
_,(_,THEOREMS1left,_))::rest671) => let val result=MlyValue.theorems((
namethm_list))
 in (LrTable.NT 14,(result,THEOREMS1left,namethm_list1right),rest671)
 end
| (21,rest671) => let val result=MlyValue.namethm_list(([]))
 in (LrTable.NT 15,(result,defaultPos,defaultPos),rest671) end
| (22,(_,(MlyValue.namethm_list namethm_list,_,namethm_list1right))::(
_,(MlyValue.namethm namethm,namethm1left,_))::rest671) => let val
result=MlyValue.namethm_list((namethm :: namethm_list))
 in (LrTable.NT 15,(result,namethm1left,namethm_list1right),rest671)
 end
| (23,(_,(MlyValue.termlist termlist,_,termlist1right))::(_,(
MlyValue.ID ID,ID1left,_))::rest671) => let val result=
MlyValue.namethm(((ID, (tl termlist, hd termlist))))
 in (LrTable.NT 16,(result,ID1left,termlist1right),rest671) end
| (24,(_,(MlyValue.term term,term1left,term1right))::rest671) => let
val result=MlyValue.termlist(([term]))
 in (LrTable.NT 21,(result,term1left,term1right),rest671) end
| (25,(_,(MlyValue.termlist termlist,_,termlist1right))::(_,(
MlyValue.term term,term1left,_))::rest671) => let val result=
MlyValue.termlist((term :: termlist))
 in (LrTable.NT 21,(result,term1left,termlist1right),rest671) end
| (26,(_,(_,_,RPAREN1right))::(_,(MlyValue.term_a term_a,_,_))::(_,(_,
LPAREN1left,_))::rest671) => let val result=MlyValue.term((term_a))
 in (LrTable.NT 17,(result,LPAREN1left,RPAREN1right),rest671) end
| (27,(_,(MlyValue.term_a term_a,_,term_a1right))::_::(_,(
MlyValue.tmid tmid,_,_))::(_,(_,BACKSLASH1left,_))::rest671) => let val
result=MlyValue.term_a((abs(tmid, term_a)))
 in (LrTable.NT 18,(result,BACKSLASH1left,term_a1right),rest671) end
| (28,(_,(MlyValue.term_c term_c,term_c1left,term_c1right))::rest671)
 => let val result=MlyValue.term_a((term_c))
 in (LrTable.NT 18,(result,term_c1left,term_c1right),rest671) end
| (29,(_,(MlyValue.base_term base_term,_,base_term1right))::(_,(
MlyValue.term_c term_c,term_c1left,_))::rest671) => let val result=
MlyValue.term_c((app(term_c, base_term)))
 in (LrTable.NT 19,(result,term_c1left,base_term1right),rest671) end
| (30,(_,(MlyValue.base_term base_term,base_term1left,base_term1right)
)::rest671) => let val result=MlyValue.term_c((base_term))
 in (LrTable.NT 19,(result,base_term1left,base_term1right),rest671)
 end
| (31,(_,(_,_,RPAREN1right))::(_,(MlyValue.term_a term_a,_,_))::(_,(_,
LPAREN1left,_))::rest671) => let val result=MlyValue.base_term((term_a
))
 in (LrTable.NT 20,(result,LPAREN1left,RPAREN1right),rest671) end
| (32,(_,(MlyValue.tmid tmid,tmid1left,tmid1right))::rest671) => let
val result=MlyValue.base_term((atom tmid))
 in (LrTable.NT 20,(result,tmid1left,tmid1right),rest671) end
| (33,(_,(MlyValue.NUMBER NUMBER,NUMBER1left,NUMBER1right))::rest671)
 => let val result=MlyValue.tmid((NUMBER))
 in (LrTable.NT 22,(result,NUMBER1left,NUMBER1right),rest671) end
| _ => raise (mlyAction i392)
end
val void = MlyValue.VOID
val extract = fn a => (fn MlyValue.theoryfile x => x
| _ => let exception ParseInternal
	in raise ParseInternal end) a
end
end
structure Tokens : DiskFiles_TOKENS =
struct
type svalue = ParserData.svalue
type ('a,'b) token = ('a,'b) Token.token
fun EOF (p1,p2) = Token.TOKEN (ParserData.LrTable.T 0,(
ParserData.MlyValue.VOID,p1,p2))
fun ID (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 1,(
ParserData.MlyValue.ID i,p1,p2))
fun DOLLAR (p1,p2) = Token.TOKEN (ParserData.LrTable.T 2,(
ParserData.MlyValue.VOID,p1,p2))
fun FULLSTOP (p1,p2) = Token.TOKEN (ParserData.LrTable.T 3,(
ParserData.MlyValue.VOID,p1,p2))
fun LPAREN (p1,p2) = Token.TOKEN (ParserData.LrTable.T 4,(
ParserData.MlyValue.VOID,p1,p2))
fun RPAREN (p1,p2) = Token.TOKEN (ParserData.LrTable.T 5,(
ParserData.MlyValue.VOID,p1,p2))
fun BACKSLASH (p1,p2) = Token.TOKEN (ParserData.LrTable.T 6,(
ParserData.MlyValue.VOID,p1,p2))
fun IDS (p1,p2) = Token.TOKEN (ParserData.LrTable.T 7,(
ParserData.MlyValue.VOID,p1,p2))
fun TYPES (p1,p2) = Token.TOKEN (ParserData.LrTable.T 8,(
ParserData.MlyValue.VOID,p1,p2))
fun TERMS (p1,p2) = Token.TOKEN (ParserData.LrTable.T 9,(
ParserData.MlyValue.VOID,p1,p2))
fun THEOREMS (p1,p2) = Token.TOKEN (ParserData.LrTable.T 10,(
ParserData.MlyValue.VOID,p1,p2))
fun LBRACKET (p1,p2) = Token.TOKEN (ParserData.LrTable.T 11,(
ParserData.MlyValue.VOID,p1,p2))
fun RBRACKET (p1,p2) = Token.TOKEN (ParserData.LrTable.T 12,(
ParserData.MlyValue.VOID,p1,p2))
fun NUMBER (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 13,(
ParserData.MlyValue.NUMBER i,p1,p2))
fun TYV (p1,p2) = Token.TOKEN (ParserData.LrTable.T 14,(
ParserData.MlyValue.VOID,p1,p2))
fun TYOP (p1,p2) = Token.TOKEN (ParserData.LrTable.T 15,(
ParserData.MlyValue.VOID,p1,p2))
fun TMV (p1,p2) = Token.TOKEN (ParserData.LrTable.T 16,(
ParserData.MlyValue.VOID,p1,p2))
fun TMC (p1,p2) = Token.TOKEN (ParserData.LrTable.T 17,(
ParserData.MlyValue.VOID,p1,p2))
end
end
