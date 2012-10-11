signature parse_type =
sig

  type ('a,'b) tyconstructors =
       {vartype : string locn.located -> 'a,
        tyop : (string locn.located * 'a list) -> 'a,
        qtyop : {Thy:string, Tyop:string, Locn:locn.locn, Args: 'a list} -> 'a,
        antiq : 'b -> 'a}
  type term = Term.term

  val parse_type : ('a,'b) tyconstructors ->
                   bool ->
                   type_grammar.grammar ->
                   'b qbuf.qbuf ->
                   'a

  val ty_antiq      : Type.hol_type -> term
  val dest_ty_antiq : term -> Type.hol_type
  val is_ty_antiq   : term -> bool


    (* The record of functions specify how to deal with the need to
       construct variable types, type operators and antiquotations

       The boolean argument specifies whether or not arbitrary type names
       should be accepted as suffixes.  With this set to true, the parser
       will not cavil at "'a foo", for arbitrary identifier foo.  With it
       false, it will only permit suffixes that are present in the grammar.

       The parameter is set to true for parsing datatype definitions, where
       it is useful to be able to mention types that don't actually exist
       yet. *)

end
