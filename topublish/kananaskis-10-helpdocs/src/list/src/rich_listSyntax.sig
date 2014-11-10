signature rich_listSyntax =
sig
   type term = Term.term

   val and_el_tm : term
   val butlastn_tm : term
   val count_list_tm : term
   val ell_tm : term
   val lastn_tm : term
   val list_elem_count_tm : term
   val or_el_tm : term
   val prefix_tm : term
   val replicate_tm : term
   val scanl_tm : term
   val scanr_tm : term
   val seg_tm : term
   val splitl_tm : term
   val splitp_tm : term
   val splitr_tm : term
   val suffix_tm : term
   val unzip_fst_tm : term
   val unzip_snd_tm : term

   val dest_and_el : term -> term
   val dest_butlastn : term -> term * term
   val dest_count_list : term -> term
   val dest_ell : term -> term * term
   val dest_is_sublist : term -> term * term
   val dest_is_suffix : term -> term * term
   val dest_lastn : term -> term * term
   val dest_list_elem_count : term -> term * term
   val dest_or_el : term -> term
   val dest_prefix : term -> term * term
   val dest_replicate : term -> term * term
   val dest_scanl : term -> term * term * term
   val dest_scanr : term -> term * term * term
   val dest_seg : term -> term * term * term
   val dest_splitl : term -> term * term
   val dest_splitp : term -> term * term
   val dest_splitr : term -> term * term
   val dest_suffix : term -> term * term
   val dest_unzip_fst : term -> term
   val dest_unzip_snd : term -> term

   val is_and_el : term -> bool
   val is_butlastn : term -> bool
   val is_count_list : term -> bool
   val is_ell : term -> bool
   val is_is_sublist : term -> bool
   val is_is_suffix : term -> bool
   val is_lastn : term -> bool
   val is_list_elem_count : term -> bool
   val is_or_el : term -> bool
   val is_prefix : term -> bool
   val is_replicate : term -> bool
   val is_scanl : term -> bool
   val is_scanr : term -> bool
   val is_seg : term -> bool
   val is_splitl : term -> bool
   val is_splitp : term -> bool
   val is_splitr : term -> bool
   val is_sublist_tm : term
   val is_suffix : term -> bool
   val is_suffix_tm : term
   val is_unzip_fst : term -> bool
   val is_unzip_snd : term -> bool

   val mk_and_el : term -> term
   val mk_butlastn : term * term -> term
   val mk_count_list : term -> term
   val mk_ell : term * term -> term
   val mk_is_sublist : term * term -> term
   val mk_is_suffix : term * term -> term
   val mk_lastn : term * term -> term
   val mk_list_elem_count : term * term -> term
   val mk_or_el : term -> term
   val mk_prefix : term * term -> term
   val mk_replicate : term * term -> term
   val mk_scanl : term * term * term -> term
   val mk_scanr : term * term * term -> term
   val mk_seg : term * term * term -> term
   val mk_splitl : term * term -> term
   val mk_splitp : term * term -> term
   val mk_splitr : term * term -> term
   val mk_suffix : term * term -> term
   val mk_unzip_fst : term -> term
   val mk_unzip_snd : term -> term

end
