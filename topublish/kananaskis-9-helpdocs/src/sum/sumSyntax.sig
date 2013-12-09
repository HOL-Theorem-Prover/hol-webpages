signature sumSyntax =
sig
  include Abbrev

  val inl_tm : term
  val inr_tm : term
  val isl_tm : term
  val isr_tm : term
  val outl_tm : term
  val outr_tm : term
  val sum_case_tm : term

  val mk_sum      : hol_type * hol_type -> hol_type
  val dest_sum    : hol_type -> hol_type * hol_type
  val strip_sum   : hol_type -> hol_type list
  val list_mk_sum : hol_type list -> hol_type

  val mk_inl      : term * hol_type -> term
  val mk_inr      : term * hol_type -> term
  val mk_isl      : term -> term
  val mk_isr      : term -> term
  val mk_outl     : term -> term
  val mk_outr     : term -> term
  val mk_sum_case : term * term * term -> term

  val dest_inl  : term -> term * hol_type
  val dest_inr  : term -> term * hol_type
  val dest_isl  : term -> term
  val dest_isr  : term -> term
  val dest_outl : term -> term
  val dest_outr : term -> term

  val is_inl  : term -> bool
  val is_inr  : term -> bool
  val is_isl  : term -> bool
  val is_isr  : term -> bool
  val is_outl : term -> bool
  val is_outr : term -> bool

  datatype ('a, 'b) sum = INL of 'a | INR of 'b

  val lift_sum    : hol_type -> ('a -> term )
                             -> ('b -> term)
                             -> ('a,'b)sum
                             -> term
end
