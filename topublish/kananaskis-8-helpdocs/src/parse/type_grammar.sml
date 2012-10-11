structure type_grammar :> type_grammar =
struct

datatype grammar_rule =
         INFIX of {opname : string, parse_string : string} list *
                  HOLgrammars.associativity

datatype type_structure =
         TYOP of {Thy : string, Tyop : string, Args : type_structure list}
       | PARAM of int

fun typstruct_uptodate ts =
    case ts of
      PARAM _ => true
    | TYOP {Thy, Tyop, Args} => isSome (Type.op_arity {Thy = Thy, Tyop = Tyop})
                                andalso List.all typstruct_uptodate Args



datatype grammar = TYG of (int * grammar_rule) list *
                          string list *
                          (string, type_structure) Binarymap.dict *
                          (int * string) TypeNet.typenet

open HOLgrammars

fun default_typrinter (G:grammar) (pps:Portable.ppstream)
                      (ty:Type.hol_type) = PP.add_string pps "<a type>"

val type_printer = ref default_typrinter
val initialised_printer = ref false

fun initialise_typrinter f =
    if not (!initialised_printer) then
      (type_printer := f; initialised_printer := true)
    else
      raise Feedback.HOL_ERR {origin_structure = "type_grammar",
                              origin_function = "initialised_printer",
                              message = "Printer function already initialised"}

fun pp_type g pps ty = (!type_printer) g pps ty

fun structure_to_type st =
    case st of
      TYOP {Thy,Tyop,Args} =>
      Type.mk_thy_type {Thy = Thy, Tyop = Tyop,
                        Args = map structure_to_type Args}
    | PARAM n => Type.mk_vartype ("'"^str (chr (n + ord #"a")))

fun params0 acc (PARAM i) = HOLset.add(acc, i)
  | params0 acc (TYOP{Args,...}) = foldl (fn (t,set) => params0 set t) acc Args
val params = params0 (HOLset.empty Int.compare)

val num_params = HOLset.numItems o params

fun suffix_arity abbrevs s =
    case Binarymap.peek (abbrevs, s) of
      NONE => let
      in
        case Type.decls s of
          [] => NONE
        | ty :: _ => Option.map (fn n => (s,n)) (Type.op_arity ty)
      end
    | SOME st => if typstruct_uptodate st then SOME (s, num_params st)
                 else NONE

fun merge r1 r2 =
  case (r1, r2) of
    (INFIX(rlist1, a1), INFIX(rlist2, a2)) => let
    in
      if a1 = a2 then INFIX(Lib.union rlist1 rlist2, a1)
      else
        raise GrammarError
          "Attempt to merge two infix types with different associativities"
    end

fun insert_sorted (k, v) [] = [(k, v)]
  | insert_sorted kv1 (wholething as (kv2::rest)) = let
      val (k1, v1) = kv1
      val (k2, v2) = kv2
    in
      if (k1 < k2) then kv1::wholething
      else
        if k1 = k2 then  (k1, merge v1 v2) :: rest
        else
          kv2 :: insert_sorted kv1 rest
    end

fun new_binary_tyop (TYG(G,sfxs,abbrevs,pmap))
                    {precedence, infix_form, opname, associativity} =
    let
      val rule =
          if isSome infix_form then
            (precedence, INFIX([{parse_string = valOf infix_form,
                                 opname = opname}],
                               associativity))
          else (precedence, INFIX([{parse_string = opname, opname = opname}],
                                  associativity))
    in
      TYG (insert_sorted rule G, Lib.insert opname sfxs, abbrevs, pmap)
    end

fun remove_binary_tyop (TYG (G, sfxs, abbrevs, pmap)) s = let
  fun bad_irule {parse_string,...} = parse_string = s
  fun edit_rule (prec, r) =
      case r of
        INFIX (irules, assoc) => let
          val irules' = List.filter (not o bad_irule) irules
        in
          if null irules' then NONE
          else SOME (prec, INFIX (irules', assoc))
        end
in
  TYG(List.mapPartial edit_rule G, sfxs, abbrevs, pmap)
end


fun new_tyop (TYG(G,sfxs,abbrevs,pmap)) name =
  TYG (G, name::sfxs, abbrevs, pmap)

val empty_grammar = TYG ([],
                         [],
                         Binarymap.mkDict String.compare,
                         TypeNet.empty)

fun rules (TYG (G, sfxs, dict, pmap)) = {infixes = G, suffixes = sfxs}
fun abbreviations (TYG (G, sfxs, dict, pmap)) = dict

fun check_structure st = let
  fun param_numbers (PARAM i, pset) = HOLset.add(pset, i)
    | param_numbers (TYOP{Args,...}, pset) = foldl param_numbers pset Args
  val pset = param_numbers (st, HOLset.empty Int.compare)
  val plist = HOLset.listItems pset
  fun check_for_gaps expecting [] = ()
    | check_for_gaps expecting (h::t) =
      if h <> expecting then
        raise GrammarError
                ("Expecting to find parameter #"^Int.toString expecting)
      else
        check_for_gaps (expecting + 1) t
in
  check_for_gaps 0 plist
end

val abb_tstamp = ref 0
fun new_abbreviation (TYG(G, sfxs,dict0,pmap)) (s, st) = let
  val _ = check_structure st
  val _ = case st of PARAM _ =>
                     raise GrammarError
                               "Abbreviation can't be to a type variable"
                   | _ => ()
  val G0 = TYG(G, sfxs,Binarymap.insert(dict0,s,st),
               TypeNet.insert(pmap, structure_to_type st, (!abb_tstamp, s)))
  val _ = abb_tstamp := !abb_tstamp + 1
in
  new_tyop G0 s
end

fun remove_abbreviation(arg as TYG(G, sfxs,dict0, pmap0)) s = let
  val (dict,st) = Binarymap.remove(dict0,s)
  val pmap = #1 (TypeNet.delete(pmap0, structure_to_type st))
      handle Binarymap.NotFound => pmap0
in
  TYG(G, sfxs, dict, pmap)
end handle Binarymap.NotFound => arg

fun rev_append [] acc = acc
  | rev_append (x::xs) acc = rev_append xs (x::acc)

fun merge_abbrevs G (d1, d2) = let
  fun merge_dictinsert (k,v,newdict) =
      case Binarymap.peek(newdict,k) of
        NONE => Binarymap.insert(newdict,k,v)
      | SOME v0 =>
        if v0 <> v then
          (Feedback.HOL_WARNING "parse_type" "merge_grammars"
                                ("Conflicting entries for abbreviation "^k^
                                 "; arbitrarily keeping map to "^
                                 PP.pp_to_string (!Globals.linewidth)
                                                 (pp_type G)
                                                 (structure_to_type v0));
           newdict)
        else
          newdict
in
    Binarymap.foldr merge_dictinsert d1 d2
end

fun merge_pmaps (p1, p2) =
    TypeNet.fold (fn (ty,v,acc) => TypeNet.insert(acc,ty,v)) p1 p2

fun merge_grammars (G1, G2) = let
  (* both grammars are sorted, with no adjacent suffixes *)
  val TYG (grules1, sfxs1, abbrevs1, pmap1) = G1
  val TYG (grules2, sfxs2, abbrevs2, pmap2) = G2
  fun merge_acc acc (gs as (g1, g2)) =
    case gs of
      ([], _) => rev_append acc g2
    | (_, []) => rev_append acc g1
    | ((g1rule as (g1k, g1v))::g1rest, (g2rule as (g2k, g2v))::g2rest) => let
      in
        case Int.compare (g1k, g2k) of
          LESS => merge_acc (g1rule::acc) (g1rest, g2)
        | GREATER => merge_acc (g2rule::acc) (g1, g2rest)
        | EQUAL => merge_acc ((g1k, merge g1v g2v)::acc) (g1rest, g2rest)
      end
in
  TYG (merge_acc [] (grules1, grules2),
       Lib.union sfxs1 sfxs2,
       merge_abbrevs G2 (abbrevs1, abbrevs2),
       merge_pmaps (pmap1, pmap2))
end

fun prettyprint_grammar pps (G as TYG (g,sfxs,abbrevs,pmap)) = let
  open Portable Lib
  val {add_break,add_newline,add_string,begin_block,end_block,...} =
      with_ppstream pps
  fun print_suffix (s,arity) = let
    fun print_ty_n_tuple n =
        case n of
          0 => ()
        | 1 => add_string "TY "
        | n => (add_string "(";
                pr_list (fn () => add_string "TY") (fn () => add_string ", ")
                        (fn () => ()) (List.tabulate(n,K ()));
                add_string ")")
  in
    print_ty_n_tuple arity;
    add_string s
  end

  fun print_abbrev (s, st) = let
    fun print_lhs () =
      case num_params st of
        0 => add_string s
      | 1 => (add_string "'a "; add_string s)
      | n => (begin_block INCONSISTENT 0;
              add_string "(";
              pr_list (pp_type G pps o structure_to_type o PARAM)
                      (fn () => add_string ",")
                      (fn () => add_break(1,0))
                      (List.tabulate(n, I));
             add_string ") ";
             add_string s)
    val ty = structure_to_type st
    val printed = case TypeNet.peek (pmap, ty) of
                    NONE => false
                  | SOME (_, s') => s = s'
  in
    begin_block CONSISTENT 0;
    print_lhs ();
    add_string " =";
    add_break(1,2);
    Feedback.trace ("print_tyabbrevs", 0) (pp_type G pps) ty;
    if not printed then (add_break(5,2); add_string "(not printed)") else ();
    end_block()
  end

  fun print_abbrevs () = let
    fun foldthis (k,st,acc) =
        if typstruct_uptodate st then (k,st)::acc else acc
    val okabbrevs = List.rev (Binarymap.foldl foldthis [] abbrevs)
  in
    if length okabbrevs > 0 then let
      in
        add_newline();
        add_string "Type abbreviations:";
        add_break(2,2);
        begin_block CONSISTENT 0;
        pr_list print_abbrev (fn () => add_newline()) (fn () => ()) okabbrevs;
        end_block()
      end
    else ()
  end

  fun print_infix {opname,parse_string} = let
  in
    add_string "TY ";
    add_string parse_string;
    add_string " TY";
    if opname <> parse_string then
      add_string (" ["^opname^"]")
    else
      ()
  end

  fun print_suffixes slist = let
    val oksl = List.mapPartial (suffix_arity abbrevs) slist
  in
    if null oksl then ()
    else let
      in
        add_string "       TY  ::=  ";
        begin_block INCONSISTENT 0;
        pr_list print_suffix (fn () => add_string " |")
                (fn () => add_break(1,0)) oksl;
        end_block ();
        add_newline()
      end
  end

  fun print_rule0 r =
    case r of
      INFIX(oplist, assoc) => let
        val assocstring =
            case assoc of
              LEFT => "L-"
            | RIGHT => "R-"
            | NONASSOC => "non-"
      in
        add_string "TY  ::=  ";
        begin_block INCONSISTENT 0;
        pr_list print_infix (fn () => add_string " |")
                (fn () => add_break(1,0)) oplist;
        add_string (" ("^assocstring^"associative)");
        end_block()
      end;
  fun print_rule (n, r) = let
    val precstr = StringCvt.padRight #" " 7 ("("^Int.toString n^")")
  in
    add_string precstr;
    print_rule0 r;
    add_newline()
  end
in
  begin_block CONSISTENT 0;
    begin_block CONSISTENT 0;
      add_string "Rules:";
      add_break (1,2);
      begin_block CONSISTENT 0;
        app print_rule g;
        print_suffixes sfxs;
        add_string "       TY  ::=  TY[TY] (array type)";
      end_block ();
    end_block ();
    print_abbrevs();
  end_block()
end;

val print_abbrevs = ref true
val _ = Feedback.register_btrace ("print_tyabbrevs", print_abbrevs)

fun tysize ty =
    if Type.is_vartype ty then 1
    else let
        val {Args,...} = Type.dest_thy_type ty
      in
        1 + List.foldl (fn (ty,acc) => tysize ty + acc) 0 Args
      end

fun abb_dest_type0 (TYG(_, _, _, pmap)) ty = let
  open HolKernel
  val net_matches = TypeNet.match(pmap, ty)
  fun mymatch pat ty = let
    val (i, sames) = Type.raw_match_type pat ty ([], [])
  in
    i @ (map (fn ty => ty |-> ty) sames)
  end
  fun check_match (pat, (tstamp, nm)) =
      SOME(mymatch pat ty, nm, tstamp) handle HOL_ERR _ => NONE
  val checked_matches = List.mapPartial check_match net_matches
  fun instcmp ({redex = r1, ...}, {redex = r2, ...}) = Type.compare(r1, r2)
in
  case checked_matches of
    [] => Type.dest_type ty
  | _ => let
      fun instsize i =
          List.foldl (fn ({redex,residue},acc) => tysize residue + acc) 0 i
      fun match_info (i, _, tstamp) = (instsize i, tstamp)
      val matchcmp = inv_img_cmp match_info
                                 (pair_compare(Int.compare,
                                               Lib.flip_order o Int.compare))
      val allinsts = Listsort.sort matchcmp checked_matches
      val (inst,nm,_) = hd allinsts
      val inst' = Listsort.sort instcmp inst
      val args = map #residue inst'
    in
      (nm, args)
    end
end

fun abb_dest_type G ty = if !print_abbrevs then abb_dest_type0 G ty
                         else Type.dest_type ty

fun disable_abbrev_printing s (arg as TYG(G,sfxs,abbs,pmap)) =
    case Binarymap.peek(abbs, s) of
      NONE => arg
    | SOME st => let
        val ty = structure_to_type st
        val (pmap', (_,s')) = TypeNet.delete(pmap, ty)
      in
        if s = s' then TYG(G, sfxs,abbs, pmap')
        else arg
      end handle Binarymap.NotFound => arg
(* ----------------------------------------------------------------------
    min grammar

    Grammar that knows about types bool and ind, as well as the operator
    fun, which also has an infix -> presentation
   ---------------------------------------------------------------------- *)

open Lib
val min_grammar =
    empty_grammar |> C new_tyop "bool"
                  |> C new_tyop "ind"
                  |> C new_binary_tyop {opname = "fun",
                                        associativity = RIGHT,
                                        infix_form = SOME "->",
                                        precedence = 50}


end
