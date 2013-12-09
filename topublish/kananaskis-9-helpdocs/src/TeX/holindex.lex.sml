functor HolindexLexFun(structure Tokens : Holindex_TOKENS)=
   struct
    type int = Int.int
    structure UserDeclarations =
      struct
type pos = (int * int);
type arg = int;
open Tokens;
type lexresult  = (svalue,pos) token

val linestart_pos = ref 0;

fun mkTok f text pos line =
  (f text, ((pos - !linestart_pos) - String.size text, line),
            (pos - !linestart_pos, line));

fun mkMtTok text pos line =
  (((pos - !linestart_pos) - String.size text, line),
    (pos - !linestart_pos, line));

fun I x = x;
fun eof () = EOF ((~1, ~1), (~1, ~1));


exception LexicalError of string * int * int;
fun lexError msg text pos line =
  (raise (LexicalError (text, pos, line)))


(* The table of keywords *)

val keyword_table =
List.foldl (fn ((str, tok), t) => Binarymap.insert (t, str, tok))
(Binarymap.mkDict String.compare)
[
  ("TERM",         TERM),
  ("@TERM",        TERM),

  ("THEOREM",      THEOREM),
  ("@THEOREM",     THEOREM),
  ("THM",          THEOREM),
  ("@THM",         THEOREM),
  ("THEOREMS",     THEOREMS),
  ("@THEOREMS",    THEOREMS),
  ("THMS",         THEOREMS),
  ("@THMS",        THEOREMS),


  ("TYPE",         TYPE),
  ("@TYPE",        TYPE),

  ("FORCE_INDEX",  FORCE_INDEX),
  ("FORCE-INDEX",  FORCE_INDEX),
  ("LONG_INDEX" ,  LONG_INDEX),
  ("LONG-INDEX" ,  LONG_INDEX),
  ("SHORT_INDEX" , SHORT_INDEX),
  ("SHORT-INDEX" , SHORT_INDEX),

  ("IDS",          IDS),
  ("OPTIONS",      OPTIONS),
  ("LABEL",        LABEL),
  ("CONTENT",      CONTENT),
  ("COMMENT",      COMMENT),
  ("LATEX",        LATEX)
];


fun toUpperString s =
   String.translate (fn c => Char.toString(Char.toUpper c)) s

fun mkKeyword text pos line =
  (Binarymap.find (keyword_table, toUpperString text)) (mkMtTok text pos line)
  handle Binarymap.NotFound => IDENT (mkTok I text pos line);


end (* end of user routines *)
exception LexError (* raised if illegal leaf action tried *)
structure Internal =
	struct

datatype yyfinstate = N of int
type statedata = {fin : yyfinstate list, trans: string}
(* transition & final state table *)
val tab = let
val s = [
 (0,
"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000"
),
 (1,
"\005\005\005\005\005\005\005\005\005\007\023\005\007\022\005\005\
\\005\005\005\005\005\005\005\005\005\005\005\005\005\005\005\005\
\\007\005\019\005\005\005\005\005\005\005\009\005\018\009\009\005\
\\009\009\009\009\009\009\009\009\009\009\009\005\005\017\005\005\
\\009\009\009\009\009\009\009\009\009\009\009\009\009\009\009\009\
\\009\009\009\009\009\009\009\009\009\009\009\016\005\015\005\009\
\\011\009\009\009\009\009\009\009\009\009\009\009\009\009\009\009\
\\009\009\009\009\009\009\009\009\009\009\009\008\007\006\005\005\
\\005"
),
 (9,
"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\010\000\000\010\010\000\
\\010\010\010\010\010\010\010\010\010\010\010\000\000\000\000\000\
\\010\010\010\010\010\010\010\010\010\010\010\010\010\010\010\010\
\\010\010\010\010\010\010\010\010\010\010\010\000\000\000\000\010\
\\000\010\010\010\010\010\010\010\010\010\010\010\010\010\010\010\
\\010\010\010\010\010\010\010\010\010\010\010\000\000\000\000\000\
\\000"
),
 (11,
"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\012\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000"
),
 (12,
"\012\012\012\012\012\012\012\012\012\012\012\012\012\012\012\012\
\\012\012\012\012\012\012\012\012\012\012\012\012\012\012\012\012\
\\012\012\012\012\012\012\012\012\012\012\012\012\012\012\012\012\
\\012\012\012\012\012\012\012\012\012\012\012\012\012\012\012\012\
\\012\012\012\012\012\012\012\012\012\012\012\012\012\012\012\012\
\\012\012\012\012\012\012\012\012\012\012\012\012\012\012\012\012\
\\013\012\012\012\012\012\012\012\012\012\012\012\012\012\012\012\
\\012\012\012\012\012\012\012\012\012\012\012\012\012\012\012\012\
\\012"
),
 (13,
"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\014\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000"
),
 (19,
"\020\020\020\020\020\020\020\020\020\020\020\020\020\020\020\020\
\\020\020\020\020\020\020\020\020\020\020\020\020\020\020\020\020\
\\020\020\021\020\020\020\020\020\020\020\020\020\020\020\020\020\
\\020\020\020\020\020\020\020\020\020\020\020\020\020\020\020\020\
\\020\020\020\020\020\020\020\020\020\020\020\020\020\020\020\020\
\\020\020\020\020\020\020\020\020\020\020\020\020\020\020\020\020\
\\000\020\020\020\020\020\020\020\020\020\020\020\020\020\020\020\
\\020\020\020\020\020\020\020\020\020\020\020\020\020\020\020\020\
\\020"
),
 (22,
"\000\000\000\000\000\000\000\000\000\000\023\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000"
),
(0, "")]
fun f x = x
val s = map f (rev (tl (rev s)))
exception LexHackingError
fun look ((j,x)::r, i) = if i = j then x else look(r, i)
  | look ([], i) = raise LexHackingError
fun g {fin=x, trans=i} = {fin=x, trans=look(s,i)}
in Vector.fromList(map g
[{fin = [], trans = 0},
{fin = [(N 42)], trans = 1},
{fin = [(N 42)], trans = 1},
{fin = [], trans = 0},
{fin = [], trans = 0},
{fin = [(N 44)], trans = 0},
{fin = [(N 10),(N 44)], trans = 0},
{fin = [(N 6),(N 44)], trans = 0},
{fin = [(N 8),(N 44)], trans = 0},
{fin = [(N 42),(N 44)], trans = 9},
{fin = [(N 42)], trans = 9},
{fin = [(N 44)], trans = 11},
{fin = [], trans = 12},
{fin = [], trans = 13},
{fin = [(N 24),(N 30)], trans = 0},
{fin = [(N 14),(N 44)], trans = 0},
{fin = [(N 12),(N 44)], trans = 0},
{fin = [(N 16),(N 44)], trans = 0},
{fin = [(N 18),(N 44)], trans = 0},
{fin = [(N 44)], trans = 19},
{fin = [], trans = 19},
{fin = [(N 34)], trans = 0},
{fin = [(N 4),(N 44)], trans = 22},
{fin = [(N 4)], trans = 0}])
end
structure StartStates =
	struct
	datatype yystartstate = STARTSTATE of int

(* start state definitions *)

val Comment = STARTSTATE 3;
val INITIAL = STARTSTATE 1;

end
type result = UserDeclarations.lexresult
	exception LexerError (* raised if illegal leaf action tried *)
end

type int = Int.int
fun makeLexer (yyinput: int -> string) =
let	val yygone0:int=0
	val yylineno: int ref = ref 0

	val yyb = ref "\n" 		(* buffer *)
	val yybl: int ref = ref 1		(*buffer length *)
	val yybufpos: int ref = ref 1		(* location of next character to use *)
	val yygone: int ref = ref yygone0	(* position in file of beginning of buffer *)
	val yydone = ref false		(* eof found yet? *)
	val yybegin: int ref = ref 1		(*Current 'start state' for lexer *)

	val YYBEGIN = fn (Internal.StartStates.STARTSTATE x) =>
		 yybegin := x

fun lex () : Internal.result =
let fun continue() = lex() in
  let fun scan (s,AcceptingLeaves : Internal.yyfinstate list list,l,i0: int) =
	let fun action (i: int,nil) = raise LexError
	| action (i,nil::l) = action (i-1,l)
	| action (i,(node::acts)::l) =
		case node of
		    Internal.N yyk =>
			(let fun yymktext() = String.substring(!yyb,i0,i-i0)
			     val yypos: int = i0+ !yygone
			val _ = yylineno := CharVectorSlice.foldli
				(fn (_,#"\n", n) => n+1 | (_,_, n) => n) (!yylineno) (CharVectorSlice.slice(!yyb,i0,SOME(i-i0)))
			open UserDeclarations Internal.StartStates
 in (yybufpos := i; case yyk of

			(* Application actions *)

  10 => let val yytext=yymktext() in RBRACE (mkMtTok yytext yypos (!yylineno))  end
| 12 => let val yytext=yymktext() in LBRACKET (mkMtTok yytext yypos (!yylineno))  end
| 14 => let val yytext=yymktext() in RBRACKET (mkMtTok yytext yypos (!yylineno))  end
| 16 => let val yytext=yymktext() in EQUAL (mkMtTok yytext yypos (!yylineno))  end
| 18 => let val yytext=yymktext() in COMMA (mkMtTok yytext yypos (!yylineno))  end
| 24 => let val yytext=yymktext() in STRING (mkTok (fn s => (substring (s, 2, (String.size s)-4))) yytext yypos (!yylineno))  end
| 30 => let val yytext=yymktext() in STRING (mkTok (fn s => (substring (s, 2, (String.size s)-4))) yytext yypos (!yylineno))  end
| 34 => let val yytext=yymktext() in STRING (mkTok (fn s => (substring (s, 1, (String.size s)-2))) yytext yypos (!yylineno))  end
| 4 => ( ((linestart_pos := yypos); continue ()) )
| 42 => let val yytext=yymktext() in mkKeyword yytext yypos (!yylineno)  end
| 44 => let val yytext=yymktext() in lexError "ill-formed token" yytext yypos (!yylineno)  end
| 6 => ( continue () )
| 8 => let val yytext=yymktext() in LBRACE (mkMtTok yytext yypos (!yylineno))  end
| _ => raise Internal.LexerError

		) end )

	val {fin,trans} = Vector.sub (Internal.tab, s)
	val NewAcceptingLeaves = fin::AcceptingLeaves
	in if l = !yybl then
	     if trans = #trans(Vector.sub(Internal.tab,0))
	       then action(l,NewAcceptingLeaves
) else	    let val newchars= if !yydone then "" else yyinput 1024
	    in if (String.size newchars)=0
		  then (yydone := true;
		        if (l=i0) then UserDeclarations.eof ()
		                  else action(l,NewAcceptingLeaves))
		  else (if i0=l then yyb := newchars
		     else yyb := String.substring(!yyb,i0,l-i0)^newchars;
		     yygone := !yygone+i0;
		     yybl := String.size (!yyb);
		     scan (s,AcceptingLeaves,l-i0,0))
	    end
	  else let val NewChar = Char.ord (CharVector.sub (!yyb,l))
		val NewChar = if NewChar<128 then NewChar else 128
		val NewState = Char.ord (CharVector.sub (trans,NewChar))
		in if NewState=0 then action(l,NewAcceptingLeaves)
		else scan(NewState,NewAcceptingLeaves,l+1,i0)
	end
	end
(*
	val start= if String.substring(!yyb,!yybufpos-1,1)="\n"
then !yybegin+1 else !yybegin
*)
	in scan(!yybegin (* start *),nil,!yybufpos,!yybufpos)
    end
end
  in lex
  end
end
