signature int_bitwiseTheory =
sig
  type thm = Thm.thm

  (*  Definitions  *)
    val bits_bitwise_curried_def : thm
    val bits_bitwise_tupled_primitive_def : thm
    val bits_of_int_def : thm
    val bits_of_num_primitive_def : thm
    val int_and_def : thm
    val int_bit_def : thm
    val int_bitwise_def : thm
    val int_not_def : thm
    val int_of_bits_def : thm
    val int_or_def : thm
    val int_shift_left_def : thm
    val int_shift_right_def : thm
    val int_xor_def : thm
    val num_of_bits_primitive_def : thm

  (*  Theorems  *)
    val bits_bitwise_def : thm
    val bits_bitwise_ind : thm
    val bits_of_num_def : thm
    val bits_of_num_ind : thm
    val int_bit_and : thm
    val int_bit_bitwise : thm
    val int_bit_equiv : thm
    val int_bit_int_of_bits : thm
    val int_bit_not : thm
    val int_bit_or : thm
    val int_bit_shift_left : thm
    val int_bit_shift_right : thm
    val int_bit_xor : thm
    val int_not : thm
    val int_not_not : thm
    val int_of_bits_bits_of_int : thm
    val num_of_bits_def : thm
    val num_of_bits_ind : thm

  val int_bitwise_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [Omega] Parent theory of "int_bitwise"

   [bit] Parent theory of "int_bitwise"

   [int_arith] Parent theory of "int_bitwise"

   [bits_bitwise_curried_def]  Definition

      |- ∀x x1 x2. bits_bitwise x x1 x2 = bits_bitwise_tupled (x,x1,x2)

   [bits_bitwise_tupled_primitive_def]  Definition

      |- bits_bitwise_tupled =
         WFREC
           (@R.
              WF R ∧
              (∀b2 r2 bs2 r1 f.
                 R (f,([],r1),bs2,r2) (f,([],r1),b2::bs2,r2)) ∧
              (∀b1 r2 r1 bs1 f.
                 R (f,(bs1,r1),[],r2) (f,(b1::bs1,r1),[],r2)) ∧
              ∀b2 b1 r2 bs2 r1 bs1 f.
                R (f,(bs1,r1),bs2,r2) (f,(b1::bs1,r1),b2::bs2,r2))
           (λbits_bitwise_tupled a.
              case a of
                (f,([],r1),[],r2) => I ([],f r1 r2)
              | (f,(b1::bs1,r1),[],r2) =>
                  I
                    (let (bs,r) = bits_bitwise_tupled (f,(bs1,r1),[],r2)
                     in
                       (f b1 r2::bs,r))
              | (f,([],r1),b2::bs2,r2) =>
                  I
                    (let (bs,r) = bits_bitwise_tupled (f,([],r1),bs2,r2)
                     in
                       (f r1 b2::bs,r))
              | (f,(b1'::bs1',r1),b2::bs2,r2) =>
                  I
                    (let (bs,r) = bits_bitwise_tupled (f,(bs1',r1),bs2,r2)
                     in
                       (f b1' b2::bs,r)))

   [bits_of_int_def]  Definition

      |- ∀i.
           bits_of_int i =
           if i < 0 then (MAP $~ (bits_of_num (Num (int_not i))),T)
           else (bits_of_num (Num i),F)

   [bits_of_num_primitive_def]  Definition

      |- bits_of_num =
         WFREC (@R. WF R ∧ ∀n. n ≠ 0 ⇒ R (n DIV 2) n)
           (λbits_of_num n.
              I (if n = 0 then [] else ODD n::bits_of_num (n DIV 2)))

   [int_and_def]  Definition

      |- int_and = int_bitwise $/\

   [int_bit_def]  Definition

      |- ∀b i.
           int_bit b i ⇔
           if i < 0 then ¬BIT b (Num (int_not i)) else BIT b (Num i)

   [int_bitwise_def]  Definition

      |- ∀f i j.
           int_bitwise f i j =
           int_of_bits (bits_bitwise f (bits_of_int i) (bits_of_int j))

   [int_not_def]  Definition

      |- ∀i. int_not i = 0 − i − 1

   [int_of_bits_def]  Definition

      |- ∀bs rest.
           int_of_bits (bs,rest) =
           if rest then int_not (&num_of_bits (MAP $~ bs))
           else &num_of_bits bs

   [int_or_def]  Definition

      |- int_or = int_bitwise $\/

   [int_shift_left_def]  Definition

      |- ∀n i.
           int_shift_left n i =
           (let (bs,r) = bits_of_int i
            in
              int_of_bits (GENLIST (K F) n ++ bs,r))

   [int_shift_right_def]  Definition

      |- ∀n i.
           int_shift_right n i =
           (let (bs,r) = bits_of_int i in int_of_bits (DROP n bs,r))

   [int_xor_def]  Definition

      |- int_xor = int_bitwise (λx y. x ⇎ y)

   [num_of_bits_primitive_def]  Definition

      |- num_of_bits =
         WFREC (@R. WF R ∧ (∀bs. R bs (F::bs)) ∧ ∀bs. R bs (T::bs))
           (λnum_of_bits a.
              case a of
                [] => I 0
              | T::bs => I (1 + 2 * num_of_bits bs)
              | F::bs => I (2 * num_of_bits bs))

   [bits_bitwise_def]  Theorem

      |- (∀r2 r1 f. bits_bitwise f ([],r1) ([],r2) = ([],f r1 r2)) ∧
         (∀r2 r1 f bs2 b2.
            bits_bitwise f ([],r1) (b2::bs2,r2) =
            (let (bs,r) = bits_bitwise f ([],r1) (bs2,r2)
             in
               (f r1 b2::bs,r))) ∧
         (∀r2 r1 f bs1 b1.
            bits_bitwise f (b1::bs1,r1) ([],r2) =
            (let (bs,r) = bits_bitwise f (bs1,r1) ([],r2)
             in
               (f b1 r2::bs,r))) ∧
         ∀r2 r1 f bs2 bs1 b2 b1.
           bits_bitwise f (b1::bs1,r1) (b2::bs2,r2) =
           (let (bs,r) = bits_bitwise f (bs1,r1) (bs2,r2)
            in
              (f b1 b2::bs,r))

   [bits_bitwise_ind]  Theorem

      |- ∀P.
           (∀f r1 r2. P f ([],r1) ([],r2)) ∧
           (∀f r1 b2 bs2 r2.
              P f ([],r1) (bs2,r2) ⇒ P f ([],r1) (b2::bs2,r2)) ∧
           (∀f b1 bs1 r1 r2.
              P f (bs1,r1) ([],r2) ⇒ P f (b1::bs1,r1) ([],r2)) ∧
           (∀f b1 bs1 r1 b2 bs2 r2.
              P f (bs1,r1) (bs2,r2) ⇒ P f (b1::bs1,r1) (b2::bs2,r2)) ⇒
           ∀v v1 v2 v3 v4. P v (v1,v2) (v3,v4)

   [bits_of_num_def]  Theorem

      |- ∀n.
           bits_of_num n =
           if n = 0 then [] else ODD n::bits_of_num (n DIV 2)

   [bits_of_num_ind]  Theorem

      |- ∀P. (∀n. (n ≠ 0 ⇒ P (n DIV 2)) ⇒ P n) ⇒ ∀v. P v

   [int_bit_and]  Theorem

      |- ∀n i j. int_bit n (int_and i j) ⇔ int_bit n i ∧ int_bit n j

   [int_bit_bitwise]  Theorem

      |- ∀n f i j.
           int_bit n (int_bitwise f i j) ⇔ f (int_bit n i) (int_bit n j)

   [int_bit_equiv]  Theorem

      |- ∀i j. (i = j) ⇔ ∀n. int_bit n i ⇔ int_bit n j

   [int_bit_int_of_bits]  Theorem

      |- int_bit n (int_of_bits b) ⇔
         if n < LENGTH (FST b) then EL n (FST b) else SND b

   [int_bit_not]  Theorem

      |- ∀b i. int_bit b (int_not i) ⇔ ¬int_bit b i

   [int_bit_or]  Theorem

      |- ∀n i j. int_bit n (int_or i j) ⇔ int_bit n i ∨ int_bit n j

   [int_bit_shift_left]  Theorem

      |- ∀b n i. int_bit b (int_shift_left n i) ⇔ n ≤ b ∧ int_bit (b − n) i

   [int_bit_shift_right]  Theorem

      |- ∀b n i. int_bit b (int_shift_right n i) ⇔ int_bit (b + n) i

   [int_bit_xor]  Theorem

      |- ∀n i j. int_bit n (int_xor i j) ⇔ (int_bit n i ⇎ int_bit n j)

   [int_not]  Theorem

      |- int_not = int_bitwise (λx y. ¬y) 0

   [int_not_not]  Theorem

      |- ∀i. int_not (int_not i) = i

   [int_of_bits_bits_of_int]  Theorem

      |- ∀i. int_of_bits (bits_of_int i) = i

   [num_of_bits_def]  Theorem

      |- (num_of_bits [] = 0) ∧
         (∀bs. num_of_bits (F::bs) = 2 * num_of_bits bs) ∧
         ∀bs. num_of_bits (T::bs) = 1 + 2 * num_of_bits bs

   [num_of_bits_ind]  Theorem

      |- ∀P.
           P [] ∧ (∀bs. P bs ⇒ P (F::bs)) ∧ (∀bs. P bs ⇒ P (T::bs)) ⇒
           ∀v. P v


*)
end
