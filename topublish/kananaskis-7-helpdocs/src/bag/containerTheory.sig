signature containerTheory =
sig
  type thm = Thm.thm
  
  (*  Definitions  *)
    val BAG_OF_FMAP_def : thm
    val BAG_TO_LIST_primitive_def : thm
    val LIST_TO_BAG_def : thm
  
  (*  Theorems  *)
    val BAG_IN_BAG_OF_FMAP : thm
    val BAG_IN_MEM : thm
    val BAG_OF_FMAP_THM : thm
    val BAG_TO_LIST_CARD : thm
    val BAG_TO_LIST_EQ_NIL : thm
    val BAG_TO_LIST_IND : thm
    val BAG_TO_LIST_INV : thm
    val BAG_TO_LIST_THM : thm
    val CARD_LIST_TO_BAG : thm
    val EVERY_LIST_TO_BAG : thm
    val FINITE_BAG_OF_FMAP : thm
    val FINITE_LIST_TO_BAG : thm
    val FINITE_LIST_TO_SET : thm
    val IN_LIST_TO_BAG : thm
    val LIST_ELEM_COUNT_LIST_TO_BAG : thm
    val LIST_TO_BAG_APPEND : thm
    val LIST_TO_BAG_EQ_EMPTY : thm
    val LIST_TO_SET_APPEND : thm
    val LIST_TO_SET_THM : thm
    val MEM_BAG_TO_LIST : thm
    val MEM_SET_TO_LIST : thm
    val PERM_LIST_TO_BAG : thm
    val SET_TO_LIST_CARD : thm
    val SET_TO_LIST_IND : thm
    val SET_TO_LIST_INV : thm
    val SET_TO_LIST_IN_MEM : thm
    val SET_TO_LIST_SING : thm
    val SET_TO_LIST_THM : thm
    val UNION_APPEND : thm
  
  val container_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [bag] Parent theory of "container"
   
   [finite_map] Parent theory of "container"
   
   [sorting] Parent theory of "container"
   
   [BAG_OF_FMAP_def]  Definition
      
      |- ∀f b.
           BAG_OF_FMAP f b =
           (λx. CARD (λk. k ∈ FDOM b ∧ (x = f k (b ' k))))
   
   [BAG_TO_LIST_primitive_def]  Definition
      
      |- BAG_TO_LIST =
         WFREC
           (@R.
              WF R ∧
              ∀bag. FINITE_BAG bag ∧ bag ≠ {||} ⇒ R (BAG_REST bag) bag)
           (λBAG_TO_LIST bag.
              I
                (if FINITE_BAG bag then
                   if bag = {||} then
                     []
                   else
                     BAG_CHOICE bag::BAG_TO_LIST (BAG_REST bag)
                 else
                   ARB))
   
   [LIST_TO_BAG_def]  Definition
      
      |- (LIST_TO_BAG [] = {||}) ∧
         ∀h t. LIST_TO_BAG (h::t) = BAG_INSERT h (LIST_TO_BAG t)
   
   [BAG_IN_BAG_OF_FMAP]  Theorem
      
      |- ∀x f b. x ⋲ BAG_OF_FMAP f b ⇔ ∃k. k ∈ FDOM b ∧ (x = f k (b ' k))
   
   [BAG_IN_MEM]  Theorem
      
      |- ∀b. FINITE_BAG b ⇒ ∀x. x ⋲ b ⇔ MEM x (BAG_TO_LIST b)
   
   [BAG_OF_FMAP_THM]  Theorem
      
      |- (∀f. BAG_OF_FMAP f FEMPTY = {||}) ∧
         ∀f b k v.
           BAG_OF_FMAP f (b |+ (k,v)) =
           BAG_INSERT (f k v) (BAG_OF_FMAP f (b \\ k))
   
   [BAG_TO_LIST_CARD]  Theorem
      
      |- ∀b. FINITE_BAG b ⇒ (LENGTH (BAG_TO_LIST b) = BAG_CARD b)
   
   [BAG_TO_LIST_EQ_NIL]  Theorem
      
      |- FINITE_BAG b ⇒
         (([] = BAG_TO_LIST b) ⇔ (b = {||})) ∧
         ((BAG_TO_LIST b = []) ⇔ (b = {||}))
   
   [BAG_TO_LIST_IND]  Theorem
      
      |- ∀P.
           (∀bag.
              (FINITE_BAG bag ∧ bag ≠ {||} ⇒ P (BAG_REST bag)) ⇒ P bag) ⇒
           ∀v. P v
   
   [BAG_TO_LIST_INV]  Theorem
      
      |- ∀b. FINITE_BAG b ⇒ (LIST_TO_BAG (BAG_TO_LIST b) = b)
   
   [BAG_TO_LIST_THM]  Theorem
      
      |- FINITE_BAG bag ⇒
         (BAG_TO_LIST bag =
          if bag = {||} then
            []
          else
            BAG_CHOICE bag::BAG_TO_LIST (BAG_REST bag))
   
   [CARD_LIST_TO_BAG]  Theorem
      
      |- BAG_CARD (LIST_TO_BAG ls) = LENGTH ls
   
   [EVERY_LIST_TO_BAG]  Theorem
      
      |- BAG_EVERY P (LIST_TO_BAG ls) ⇔ EVERY P ls
   
   [FINITE_BAG_OF_FMAP]  Theorem
      
      |- ∀f b. FINITE_BAG (BAG_OF_FMAP f b)
   
   [FINITE_LIST_TO_BAG]  Theorem
      
      |- FINITE_BAG (LIST_TO_BAG ls)
   
   [FINITE_LIST_TO_SET]  Theorem
      
      |- ∀l. FINITE (set l)
   
   [IN_LIST_TO_BAG]  Theorem
      
      |- ∀h l. h ⋲ LIST_TO_BAG l ⇔ MEM h l
   
   [LIST_ELEM_COUNT_LIST_TO_BAG]  Theorem
      
      |- LIST_ELEM_COUNT e ls = LIST_TO_BAG ls e
   
   [LIST_TO_BAG_APPEND]  Theorem
      
      |- ∀l1 l2. LIST_TO_BAG (l1 ++ l2) = LIST_TO_BAG l1 ⊎ LIST_TO_BAG l2
   
   [LIST_TO_BAG_EQ_EMPTY]  Theorem
      
      |- ∀l. (LIST_TO_BAG l = {||}) ⇔ (l = [])
   
   [LIST_TO_SET_APPEND]  Theorem
      
      |- ∀l1 l2. set (l1 ++ l2) = set l1 ∪ set l2
   
   [LIST_TO_SET_THM]  Theorem
      
      |- (set [] = ∅) ∧ (set (h::t) = h INSERT set t)
   
   [MEM_BAG_TO_LIST]  Theorem
      
      |- ∀b. FINITE_BAG b ⇒ ∀x. MEM x (BAG_TO_LIST b) ⇔ x ⋲ b
   
   [MEM_SET_TO_LIST]  Theorem
      
      |- ∀s. FINITE s ⇒ ∀x. MEM x (SET_TO_LIST s) ⇔ x ∈ s
   
   [PERM_LIST_TO_BAG]  Theorem
      
      |- ∀l1 l2. (LIST_TO_BAG l1 = LIST_TO_BAG l2) ⇔ PERM l1 l2
   
   [SET_TO_LIST_CARD]  Theorem
      
      |- ∀s. FINITE s ⇒ (LENGTH (SET_TO_LIST s) = CARD s)
   
   [SET_TO_LIST_IND]  Theorem
      
      |- ∀P. (∀s. (FINITE s ∧ s ≠ ∅ ⇒ P (REST s)) ⇒ P s) ⇒ ∀v. P v
   
   [SET_TO_LIST_INV]  Theorem
      
      |- ∀s. FINITE s ⇒ (set (SET_TO_LIST s) = s)
   
   [SET_TO_LIST_IN_MEM]  Theorem
      
      |- ∀s. FINITE s ⇒ ∀x. x ∈ s ⇔ MEM x (SET_TO_LIST s)
   
   [SET_TO_LIST_SING]  Theorem
      
      |- SET_TO_LIST {x} = [x]
   
   [SET_TO_LIST_THM]  Theorem
      
      |- FINITE s ⇒
         (SET_TO_LIST s =
          if s = ∅ then [] else CHOICE s::SET_TO_LIST (REST s))
   
   [UNION_APPEND]  Theorem
      
      |- ∀l1 l2. set l1 ∪ set l2 = set (l1 ++ l2)
   
   
*)
end
