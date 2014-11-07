functor HolindexLrValsFun(structure Token : TOKEN)
 : sig structure ParserData : PARSER_DATA
       structure Tokens : Holindex_TOKENS
   end
 =
struct
structure ParserData=
struct
structure Header =
struct
open holindexData
end
structure LrTable = Token.LrTable
structure Token = Token
local open LrTable in
val table=let val actionRows =
"\
\\001\000\001\000\011\000\000\000\
\\001\000\001\000\012\000\000\000\
\\001\000\001\000\013\000\000\000\
\\001\000\001\000\014\000\000\000\
\\001\000\002\000\038\000\000\000\
\\001\000\002\000\045\000\000\000\
\\001\000\002\000\046\000\000\000\
\\001\000\002\000\058\000\000\000\
\\001\000\003\000\023\000\000\000\
\\001\000\004\000\047\000\000\000\
\\001\000\005\000\019\000\000\000\
\\001\000\005\000\040\000\000\000\
\\001\000\005\000\041\000\000\000\
\\001\000\005\000\042\000\000\000\
\\001\000\005\000\043\000\000\000\
\\001\000\005\000\044\000\000\000\
\\001\000\006\000\009\000\007\000\008\000\008\000\007\000\009\000\006\000\
\\022\000\005\000\000\000\
\\001\000\010\000\015\000\000\000\
\\001\000\011\000\050\000\000\000\
\\001\000\011\000\051\000\000\000\
\\001\000\011\000\052\000\000\000\
\\001\000\011\000\053\000\000\000\
\\001\000\011\000\054\000\000\000\
\\001\000\020\000\016\000\000\000\
\\001\000\020\000\017\000\000\000\
\\001\000\020\000\018\000\000\000\
\\001\000\021\000\020\000\000\000\
\\001\000\021\000\021\000\000\000\
\\001\000\021\000\022\000\000\000\
\\001\000\021\000\055\000\000\000\
\\001\000\022\000\000\000\000\000\
\\060\000\000\000\
\\061\000\000\000\
\\062\000\000\000\
\\063\000\000\000\
\\064\000\000\000\
\\065\000\000\000\
\\066\000\000\000\
\\067\000\020\000\037\000\000\000\
\\068\000\021\000\048\000\000\000\
\\069\000\000\000\
\\070\000\012\000\033\000\013\000\032\000\014\000\031\000\015\000\030\000\
\\016\000\029\000\017\000\028\000\018\000\027\000\019\000\026\000\000\000\
\\071\000\021\000\039\000\000\000\
\\072\000\000\000\
\\073\000\000\000\
\\074\000\000\000\
\\075\000\000\000\
\\076\000\000\000\
\\077\000\000\000\
\\078\000\000\000\
\\079\000\000\000\
\\080\000\000\000\
\"
val actionRowNumbers =
"\016\000\031\000\016\000\032\000\
\\000\000\001\000\002\000\003\000\
\\033\000\017\000\023\000\024\000\
\\025\000\010\000\026\000\027\000\
\\028\000\008\000\041\000\041\000\
\\041\000\038\000\004\000\042\000\
\\011\000\012\000\013\000\014\000\
\\015\000\046\000\045\000\044\000\
\\005\000\006\000\009\000\039\000\
\\036\000\041\000\018\000\019\000\
\\020\000\021\000\022\000\035\000\
\\034\000\029\000\038\000\043\000\
\\051\000\050\000\049\000\047\000\
\\048\000\041\000\040\000\007\000\
\\037\000\030\000"
val gotoT =
"\
\\001\000\057\000\002\000\002\000\003\000\001\000\000\000\
\\000\000\
\\002\000\002\000\003\000\008\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\005\000\023\000\006\000\022\000\000\000\
\\005\000\023\000\006\000\032\000\000\000\
\\005\000\023\000\006\000\033\000\000\000\
\\004\000\034\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\005\000\023\000\006\000\047\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\004\000\054\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\005\000\023\000\006\000\055\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\"
val numstates = 58
val numrules = 21
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
type pos =  ( int * int )
type arg = unit
structure MlyValue =
struct
datatype svalue = VOID | ntVOID of unit ->  unit
 | IDENT of unit ->  (string) | STRING of unit ->  (string)
 | option_seq of unit ->  (parse_entry -> parse_entry)
 | option of unit ->  (parse_entry -> parse_entry)
 | ident_seq of unit ->  (string list)
 | entry_seq of unit ->  (parse_entry list)
 | entry of unit ->  (parse_entry list)
 | top of unit ->  (parse_entry list)
end
type svalue = MlyValue.svalue
type result = parse_entry list
end
structure EC=
struct
open LrTable
val is_keyword =
fn _ => false
val preferred_change =
nil
val noShift =
fn _ => false
val showTerminal =
fn (T 0) => "LBRACE"
  | (T 1) => "RBRACE"
  | (T 2) => "LBRACKET"
  | (T 3) => "RBRACKET"
  | (T 4) => "EQUAL"
  | (T 5) => "TERM"
  | (T 6) => "TYPE"
  | (T 7) => "THEOREM"
  | (T 8) => "THEOREMS"
  | (T 9) => "IDS"
  | (T 10) => "STRING"
  | (T 11) => "FORCE_INDEX"
  | (T 12) => "LONG_INDEX"
  | (T 13) => "SHORT_INDEX"
  | (T 14) => "OPTIONS"
  | (T 15) => "LABEL"
  | (T 16) => "CONTENT"
  | (T 17) => "LATEX"
  | (T 18) => "COMMENT"
  | (T 19) => "IDENT"
  | (T 20) => "COMMA"
  | (T 21) => "EOF"
  | _ => "bogus-term"
local open Header in
val errtermvalue=
fn _ => MlyValue.VOID
end
val terms = (T 0) :: (T 1) :: (T 2) :: (T 3) :: (T 4) :: (T 5) :: (T 6
) :: (T 7) :: (T 8) :: (T 9) :: (T 11) :: (T 12) :: (T 13) :: (T 14)
 :: (T 15) :: (T 16) :: (T 17) :: (T 18) :: (T 20) :: (T 21) :: nil
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
of (0,(_,(MlyValue.entry_seq entry_seq1,entry_seq1left,entry_seq1right
))::rest671) => let val result=MlyValue.top(fn _ => let val entry_seq
 as entry_seq1=entry_seq1 ()
 in ( entry_seq ) end
)
 in (LrTable.NT 0,(result,entry_seq1left,entry_seq1right),rest671) end
| (1,(_,(_,EOF1left,EOF1right))::rest671) => let val result=
MlyValue.entry_seq(fn _ => ( [] ))
 in (LrTable.NT 2,(result,EOF1left,EOF1right),rest671) end
| (2,(_,(MlyValue.entry_seq entry_seq1,_,entry_seq1right))::(_,(
MlyValue.entry entry1,entry1left,_))::rest671) => let val result=
MlyValue.entry_seq(fn _ => let val entry as entry1=entry1 ()
val entry_seq as entry_seq1=entry_seq1 ()
 in ( entry @ entry_seq ) end
)
 in (LrTable.NT 2,(result,entry1left,entry_seq1right),rest671) end
| (3,(_,(_,_,RBRACE1right))::(_,(MlyValue.option_seq option_seq1,_,_))
::_::(_,(MlyValue.IDENT IDENT1,_,_))::_::(_,(_,TERM1left,_))::rest671)
 => let val result=MlyValue.entry(fn _ => let val IDENT as IDENT1=
IDENT1 ()
val option_seq as option_seq1=option_seq1 ()
 in ( [mk_update_parse_entry ("Term", IDENT) option_seq] ) end
)
 in (LrTable.NT 1,(result,TERM1left,RBRACE1right),rest671) end
| (4,(_,(_,_,RBRACE1right))::(_,(MlyValue.option_seq option_seq1,_,_))
::_::(_,(MlyValue.IDENT IDENT1,_,_))::_::(_,(_,TYPE1left,_))::rest671)
 => let val result=MlyValue.entry(fn _ => let val IDENT as IDENT1=
IDENT1 ()
val option_seq as option_seq1=option_seq1 ()
 in ( [mk_update_parse_entry ("Type", IDENT) option_seq] ) end
)
 in (LrTable.NT 1,(result,TYPE1left,RBRACE1right),rest671) end
| (5,(_,(_,_,RBRACE1right))::(_,(MlyValue.option_seq option_seq1,_,_))
::_::(_,(MlyValue.IDENT IDENT1,_,_))::_::(_,(_,THEOREM1left,_))::
rest671) => let val result=MlyValue.entry(fn _ => let val IDENT as
IDENT1=IDENT1 ()
val option_seq as option_seq1=option_seq1 ()
 in ( [mk_update_parse_entry ("Thm", IDENT) option_seq] ) end
)
 in (LrTable.NT 1,(result,THEOREM1left,RBRACE1right),rest671) end
| (6,(_,(_,_,RBRACE1right))::(_,(MlyValue.option_seq option_seq1,_,_))
::_::_::(_,(MlyValue.ident_seq ident_seq1,_,_))::_::_::_::_::(_,(_,
THEOREMS1left,_))::rest671) => let val result=MlyValue.entry(fn _ =>
let val ident_seq as ident_seq1=ident_seq1 ()
val option_seq as option_seq1=option_seq1 ()
 in ( mk_theorem_parse_entries ident_seq option_seq ) end
)
 in (LrTable.NT 1,(result,THEOREMS1left,RBRACE1right),rest671) end
| (7,rest671) => let val result=MlyValue.ident_seq(fn _ => ([]))
 in (LrTable.NT 3,(result,defaultPos,defaultPos),rest671) end
| (8,(_,(MlyValue.IDENT IDENT1,IDENT1left,IDENT1right))::rest671) =>
let val result=MlyValue.ident_seq(fn _ => let val IDENT as IDENT1=
IDENT1 ()
 in ([IDENT]) end
)
 in (LrTable.NT 3,(result,IDENT1left,IDENT1right),rest671) end
| (9,(_,(MlyValue.ident_seq ident_seq1,_,ident_seq1right))::_::(_,(
MlyValue.IDENT IDENT1,IDENT1left,_))::rest671) => let val result=
MlyValue.ident_seq(fn _ => let val IDENT as IDENT1=IDENT1 ()
val ident_seq as ident_seq1=ident_seq1 ()
 in (IDENT::ident_seq) end
)
 in (LrTable.NT 3,(result,IDENT1left,ident_seq1right),rest671) end
| (10,rest671) => let val result=MlyValue.option_seq(fn _ => (
fn x => x))
 in (LrTable.NT 5,(result,defaultPos,defaultPos),rest671) end
| (11,(_,(MlyValue.option option1,option1left,option1right))::rest671)
 => let val result=MlyValue.option_seq(fn _ => let val option as
option1=option1 ()
 in (option) end
)
 in (LrTable.NT 5,(result,option1left,option1right),rest671) end
| (12,(_,(MlyValue.option_seq option_seq1,_,option_seq1right))::_::(_,
(MlyValue.option option1,option1left,_))::rest671) => let val result=
MlyValue.option_seq(fn _ => let val option as option1=option1 ()
val option_seq as option_seq1=option_seq1 ()
 in (fn e => option_seq (option e)) end
)
 in (LrTable.NT 5,(result,option1left,option_seq1right),rest671) end
| (13,(_,(_,FORCE_INDEX1left,FORCE_INDEX1right))::rest671) => let val
result=MlyValue.option(fn _ => (parse_entry___force_index))
 in (LrTable.NT 4,(result,FORCE_INDEX1left,FORCE_INDEX1right),rest671)
 end
| (14,(_,(_,LONG_INDEX1left,LONG_INDEX1right))::rest671) => let val
result=MlyValue.option(fn _ => (parse_entry___full_index true))
 in (LrTable.NT 4,(result,LONG_INDEX1left,LONG_INDEX1right),rest671)
 end
| (15,(_,(_,SHORT_INDEX1left,SHORT_INDEX1right))::rest671) => let val
result=MlyValue.option(fn _ => (parse_entry___full_index false))
 in (LrTable.NT 4,(result,SHORT_INDEX1left,SHORT_INDEX1right),rest671)
 end
| (16,(_,(MlyValue.STRING STRING1,_,STRING1right))::_::(_,(_,
LABEL1left,_))::rest671) => let val result=MlyValue.option(fn _ => let
val STRING as STRING1=STRING1 ()
 in (parse_entry___set_label STRING) end
)
 in (LrTable.NT 4,(result,LABEL1left,STRING1right),rest671) end
| (17,(_,(MlyValue.STRING STRING1,_,STRING1right))::_::(_,(_,
OPTIONS1left,_))::rest671) => let val result=MlyValue.option(fn _ =>
let val STRING as STRING1=STRING1 ()
 in (parse_entry___set_options STRING) end
)
 in (LrTable.NT 4,(result,OPTIONS1left,STRING1right),rest671) end
| (18,(_,(MlyValue.STRING STRING1,_,STRING1right))::_::(_,(_,
CONTENT1left,_))::rest671) => let val result=MlyValue.option(fn _ =>
let val STRING as STRING1=STRING1 ()
 in (parse_entry___set_content STRING) end
)
 in (LrTable.NT 4,(result,CONTENT1left,STRING1right),rest671) end
| (19,(_,(MlyValue.STRING STRING1,_,STRING1right))::_::(_,(_,
LATEX1left,_))::rest671) => let val result=MlyValue.option(fn _ => let
val STRING as STRING1=STRING1 ()
 in (parse_entry___set_latex STRING) end
)
 in (LrTable.NT 4,(result,LATEX1left,STRING1right),rest671) end
| (20,(_,(MlyValue.STRING STRING1,_,STRING1right))::_::(_,(_,
COMMENT1left,_))::rest671) => let val result=MlyValue.option(fn _ =>
let val STRING as STRING1=STRING1 ()
 in (parse_entry___set_comment STRING) end
)
 in (LrTable.NT 4,(result,COMMENT1left,STRING1right),rest671) end
| _ => raise (mlyAction i392)
end
val void = MlyValue.VOID
val extract = fn a => (fn MlyValue.top x => x
| _ => let exception ParseInternal
	in raise ParseInternal end) a ()
end
end
structure Tokens : Holindex_TOKENS =
struct
type svalue = ParserData.svalue
type ('a,'b) token = ('a,'b) Token.token
fun LBRACE (p1,p2) = Token.TOKEN (ParserData.LrTable.T 0,(
ParserData.MlyValue.VOID,p1,p2))
fun RBRACE (p1,p2) = Token.TOKEN (ParserData.LrTable.T 1,(
ParserData.MlyValue.VOID,p1,p2))
fun LBRACKET (p1,p2) = Token.TOKEN (ParserData.LrTable.T 2,(
ParserData.MlyValue.VOID,p1,p2))
fun RBRACKET (p1,p2) = Token.TOKEN (ParserData.LrTable.T 3,(
ParserData.MlyValue.VOID,p1,p2))
fun EQUAL (p1,p2) = Token.TOKEN (ParserData.LrTable.T 4,(
ParserData.MlyValue.VOID,p1,p2))
fun TERM (p1,p2) = Token.TOKEN (ParserData.LrTable.T 5,(
ParserData.MlyValue.VOID,p1,p2))
fun TYPE (p1,p2) = Token.TOKEN (ParserData.LrTable.T 6,(
ParserData.MlyValue.VOID,p1,p2))
fun THEOREM (p1,p2) = Token.TOKEN (ParserData.LrTable.T 7,(
ParserData.MlyValue.VOID,p1,p2))
fun THEOREMS (p1,p2) = Token.TOKEN (ParserData.LrTable.T 8,(
ParserData.MlyValue.VOID,p1,p2))
fun IDS (p1,p2) = Token.TOKEN (ParserData.LrTable.T 9,(
ParserData.MlyValue.VOID,p1,p2))
fun STRING (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 10,(
ParserData.MlyValue.STRING (fn () => i),p1,p2))
fun FORCE_INDEX (p1,p2) = Token.TOKEN (ParserData.LrTable.T 11,(
ParserData.MlyValue.VOID,p1,p2))
fun LONG_INDEX (p1,p2) = Token.TOKEN (ParserData.LrTable.T 12,(
ParserData.MlyValue.VOID,p1,p2))
fun SHORT_INDEX (p1,p2) = Token.TOKEN (ParserData.LrTable.T 13,(
ParserData.MlyValue.VOID,p1,p2))
fun OPTIONS (p1,p2) = Token.TOKEN (ParserData.LrTable.T 14,(
ParserData.MlyValue.VOID,p1,p2))
fun LABEL (p1,p2) = Token.TOKEN (ParserData.LrTable.T 15,(
ParserData.MlyValue.VOID,p1,p2))
fun CONTENT (p1,p2) = Token.TOKEN (ParserData.LrTable.T 16,(
ParserData.MlyValue.VOID,p1,p2))
fun LATEX (p1,p2) = Token.TOKEN (ParserData.LrTable.T 17,(
ParserData.MlyValue.VOID,p1,p2))
fun COMMENT (p1,p2) = Token.TOKEN (ParserData.LrTable.T 18,(
ParserData.MlyValue.VOID,p1,p2))
fun IDENT (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 19,(
ParserData.MlyValue.IDENT (fn () => i),p1,p2))
fun COMMA (p1,p2) = Token.TOKEN (ParserData.LrTable.T 20,(
ParserData.MlyValue.VOID,p1,p2))
fun EOF (p1,p2) = Token.TOKEN (ParserData.LrTable.T 21,(
ParserData.MlyValue.VOID,p1,p2))
end
end
