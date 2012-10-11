signature fmapML =
sig
  type ('a,'b) fmap
  type num = numML.num
  type 'a set = 'a setML.set
  val FEMPTY   : ('a,'b) fmap
  val FUPDATE  : ('a,'b) fmap * ('a * 'b) -> ('a,'b)fmap
  val FDOM     : ('a,'b) fmap -> 'a set
  val FAPPLY : (''a, 'b) fmap -> ''a -> 'b
  val FCARD : (''a, 'b) fmap -> num
  val FLOOKUP : (''a, 'b) fmap -> ''a -> 'b option
  val FUPDATE_LIST : ('a, 'b) fmap -> ('a * 'b) list -> ('a, 'b) fmap
  val FUNION : ('a, 'b) fmap -> ('a, 'b) fmap -> ('a, 'b) fmap
  val \\ : (''a, 'b) fmap -> ''a -> (''a, 'b) fmap
  val SUBMAP : (''a, ''b) fmap -> (''a, ''b) fmap -> bool
  val DRESTRICT : ('a, 'b) fmap -> ('a -> bool) -> ('a, 'b) fmap
  val RRESTRICT : (''a, 'b) fmap -> ('b -> bool) -> (''a, 'b) fmap
  val o_f : ('b -> 'c) -> (''a, 'b) fmap -> (''a, 'c) fmap
  val FEVERY : (''a * 'b -> bool) -> (''a, 'b) fmap -> bool
end
