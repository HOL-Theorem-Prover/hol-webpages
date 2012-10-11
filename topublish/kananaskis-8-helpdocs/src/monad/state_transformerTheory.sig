signature state_transformerTheory =
sig
  type thm = Thm.thm

  (*  Definitions  *)
    val BIND_DEF : thm
    val FOR_primitive_def : thm
    val IGNORE_BIND_DEF : thm
    val JOIN_DEF : thm
    val MMAP_DEF : thm
    val READ_def : thm
    val UNIT_DEF : thm
    val WRITE_def : thm

  (*  Theorems  *)
    val BIND_ASSOC : thm
    val BIND_LEFT_UNIT : thm
    val BIND_RIGHT_UNIT : thm
    val FOR_def : thm
    val FOR_ind : thm
    val FST_o_MMAP : thm
    val FST_o_UNIT : thm
    val JOIN_MAP : thm
    val JOIN_MAP_JOIN : thm
    val JOIN_MMAP_UNIT : thm
    val JOIN_UNIT : thm
    val MMAP_COMP : thm
    val MMAP_ID : thm
    val MMAP_JOIN : thm
    val MMAP_UNIT : thm
    val SND_o_UNIT : thm
    val UNIT_UNCURRY : thm

  val state_transformer_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [basicSize] Parent theory of "state_transformer"

   [while] Parent theory of "state_transformer"

   [BIND_DEF]  Definition

      |- ∀g f. BIND g f = UNCURRY f o g

   [FOR_primitive_def]  Definition

      |- FOR =
         WFREC
           (@R.
              WF R ∧
              ∀a j i.
                i ≠ j ⇒ R (if i < j then i + 1 else i − 1,j,a) (i,j,a))
           (λFOR a'.
              case a' of
                (i,j,a) =>
                  I
                    (if i = j then
                       a i
                     else
                       BIND (a i)
                         (λu. FOR (if i < j then i + 1 else i − 1,j,a))))

   [IGNORE_BIND_DEF]  Definition

      |- ∀f g. IGNORE_BIND f g = BIND f (λx. g)

   [JOIN_DEF]  Definition

      |- ∀z. JOIN z = BIND z I

   [MMAP_DEF]  Definition

      |- ∀f m. MMAP f m = BIND m (UNIT o f)

   [READ_def]  Definition

      |- ∀f. READ f = (λs. (f s,s))

   [UNIT_DEF]  Definition

      |- ∀x. UNIT x = (λs. (x,s))

   [WRITE_def]  Definition

      |- ∀f. WRITE f = (λs. ((),f s))

   [BIND_ASSOC]  Theorem

      |- ∀k m n. BIND k (λa. BIND (m a) n) = BIND (BIND k m) n

   [BIND_LEFT_UNIT]  Theorem

      |- ∀k x. BIND (UNIT x) k = k x

   [BIND_RIGHT_UNIT]  Theorem

      |- ∀k. BIND k UNIT = k

   [FOR_def]  Theorem

      |- ∀j i a.
           FOR (i,j,a) =
           if i = j then
             a i
           else
             BIND (a i) (λu. FOR (if i < j then i + 1 else i − 1,j,a))

   [FOR_ind]  Theorem

      |- ∀P.
           (∀i j a.
              (i ≠ j ⇒ P (if i < j then i + 1 else i − 1,j,a)) ⇒
              P (i,j,a)) ⇒
           ∀v v1 v2. P (v,v1,v2)

   [FST_o_MMAP]  Theorem

      |- ∀f g. FST o MMAP f g = f o FST o g

   [FST_o_UNIT]  Theorem

      |- ∀x. FST o UNIT x = K x

   [JOIN_MAP]  Theorem

      |- ∀k m. BIND k m = JOIN (MMAP m k)

   [JOIN_MAP_JOIN]  Theorem

      |- JOIN o MMAP JOIN = JOIN o JOIN

   [JOIN_MMAP_UNIT]  Theorem

      |- JOIN o MMAP UNIT = I

   [JOIN_UNIT]  Theorem

      |- JOIN o UNIT = I

   [MMAP_COMP]  Theorem

      |- ∀f g. MMAP (f o g) = MMAP f o MMAP g

   [MMAP_ID]  Theorem

      |- MMAP I = I

   [MMAP_JOIN]  Theorem

      |- ∀f. MMAP f o JOIN = JOIN o MMAP (MMAP f)

   [MMAP_UNIT]  Theorem

      |- ∀f. MMAP f o UNIT = UNIT o f

   [SND_o_UNIT]  Theorem

      |- ∀x. SND o UNIT x = I

   [UNIT_UNCURRY]  Theorem

      |- ∀s. UNCURRY UNIT s = s


*)
end
