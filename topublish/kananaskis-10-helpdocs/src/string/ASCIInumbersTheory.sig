signature ASCIInumbersTheory =
sig
  type thm = Thm.thm

  (*  Definitions  *)
    val HEX_primitive_def : thm
    val UNHEX_primitive_def : thm
    val fromBinString_def : thm
    val fromDecString_def : thm
    val fromHexString_def : thm
    val n2s_def : thm
    val num_from_bin_string_def : thm
    val num_from_dec_string_def : thm
    val num_from_hex_string_def : thm
    val num_from_oct_string_def : thm
    val num_to_bin_string_def : thm
    val num_to_dec_string_def : thm
    val num_to_hex_string_def : thm
    val num_to_oct_string_def : thm
    val s2n_def : thm

  (*  Theorems  *)
    val BIT_num_from_bin_string : thm
    val DEC_UNDEC : thm
    val HEX_UNHEX : thm
    val HEX_def : thm
    val HEX_ind : thm
    val STRCAT_toString_inj : thm
    val SUB_num_to_bin_string : thm
    val UNHEX_HEX : thm
    val UNHEX_def : thm
    val UNHEX_ind : thm
    val n2s_compute : thm
    val n2s_s2n : thm
    val num_bin_string : thm
    val num_dec_string : thm
    val num_hex_string : thm
    val num_oct_string : thm
    val s2n_compute : thm
    val s2n_n2s : thm
    val toNum_toString : thm
    val toString_11 : thm
    val toString_inj : thm
    val toString_toNum_cancel : thm

  val ASCIInumbers_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [numposrep] Parent theory of "ASCIInumbers"

   [string] Parent theory of "ASCIInumbers"

   [HEX_primitive_def]  Definition

      |- HEX =
         WFREC (@R. WF R)
           (λHEX a.
              case a of
                0 => I #"0"
              | 1 => I #"1"
              | 2 => I #"2"
              | 3 => I #"3"
              | 4 => I #"4"
              | 5 => I #"5"
              | 6 => I #"6"
              | 7 => I #"7"
              | 8 => I #"8"
              | 9 => I #"9"
              | 10 => I #"A"
              | 11 => I #"B"
              | 12 => I #"C"
              | 13 => I #"D"
              | 14 => I #"E"
              | 15 => I #"F"
              | v => ARB)

   [UNHEX_primitive_def]  Definition

      |- UNHEX =
         WFREC (@R. WF R)
           (λUNHEX a.
              case a of
                #"0" => I 0
              | #"1" => I 1
              | #"2" => I 2
              | #"3" => I 3
              | #"4" => I 4
              | #"5" => I 5
              | #"6" => I 6
              | #"7" => I 7
              | #"8" => I 8
              | #"9" => I 9
              | #"a" => I 10
              | #"b" => I 11
              | #"c" => I 12
              | #"d" => I 13
              | #"e" => I 14
              | #"f" => I 15
              | #"A" => I 10
              | #"B" => I 11
              | #"C" => I 12
              | #"D" => I 13
              | #"E" => I 14
              | #"F" => I 15
              | v => ARB)

   [fromBinString_def]  Definition

      |- ∀s.
           fromBinString s =
           if s ≠ "" ∧ EVERY (λc. (c = #"0") ∨ (c = #"1")) s then
             SOME (num_from_bin_string s)
           else NONE

   [fromDecString_def]  Definition

      |- ∀s.
           fromDecString s =
           if s ≠ "" ∧ EVERY isDigit s then SOME (toNum s) else NONE

   [fromHexString_def]  Definition

      |- ∀s.
           fromHexString s =
           if s ≠ "" ∧ EVERY isHexDigit s then SOME (num_from_hex_string s)
           else NONE

   [n2s_def]  Definition

      |- ∀b f n. n2s b f n = REVERSE (MAP f (n2l b n))

   [num_from_bin_string_def]  Definition

      |- num_from_bin_string = s2n 2 UNHEX

   [num_from_dec_string_def]  Definition

      |- toNum = s2n 10 UNHEX

   [num_from_hex_string_def]  Definition

      |- num_from_hex_string = s2n 16 UNHEX

   [num_from_oct_string_def]  Definition

      |- num_from_oct_string = s2n 8 UNHEX

   [num_to_bin_string_def]  Definition

      |- num_to_bin_string = n2s 2 HEX

   [num_to_dec_string_def]  Definition

      |- toString = n2s 10 HEX

   [num_to_hex_string_def]  Definition

      |- num_to_hex_string = n2s 16 HEX

   [num_to_oct_string_def]  Definition

      |- num_to_oct_string = n2s 8 HEX

   [s2n_def]  Definition

      |- ∀b f s. s2n b f s = l2n b (MAP f (REVERSE s))

   [BIT_num_from_bin_string]  Theorem

      |- ∀x s.
           EVERY ($> 2 o UNHEX) s ∧ x < STRLEN s ⇒
           (BIT x (num_from_bin_string s) ⇔
            (UNHEX (SUB (s,PRE (STRLEN s − x))) = 1))

   [DEC_UNDEC]  Theorem

      |- ∀c. isDigit c ⇒ (HEX (UNHEX c) = c)

   [HEX_UNHEX]  Theorem

      |- ∀c. isHexDigit c ⇒ (HEX (UNHEX c) = toUpper c)

   [HEX_def]  Theorem

      |- (HEX 0 = #"0") ∧ (HEX 1 = #"1") ∧ (HEX 2 = #"2") ∧
         (HEX 3 = #"3") ∧ (HEX 4 = #"4") ∧ (HEX 5 = #"5") ∧
         (HEX 6 = #"6") ∧ (HEX 7 = #"7") ∧ (HEX 8 = #"8") ∧
         (HEX 9 = #"9") ∧ (HEX 10 = #"A") ∧ (HEX 11 = #"B") ∧
         (HEX 12 = #"C") ∧ (HEX 13 = #"D") ∧ (HEX 14 = #"E") ∧
         (HEX 15 = #"F")

   [HEX_ind]  Theorem

      |- ∀P.
           P 0 ∧ P 1 ∧ P 2 ∧ P 3 ∧ P 4 ∧ P 5 ∧ P 6 ∧ P 7 ∧ P 8 ∧ P 9 ∧
           P 10 ∧ P 11 ∧ P 12 ∧ P 13 ∧ P 14 ∧ P 15 ∧ (∀v18. P v18) ⇒
           ∀v. P v

   [STRCAT_toString_inj]  Theorem

      |- ∀n m s. (STRCAT s (toString n) = STRCAT s (toString m)) ⇔ (n = m)

   [SUB_num_to_bin_string]  Theorem

      |- ∀x n.
           x < STRLEN (num_to_bin_string n) ⇒
           (SUB (num_to_bin_string n,x) =
            HEX (BITV n (PRE (STRLEN (num_to_bin_string n) − x))))

   [UNHEX_HEX]  Theorem

      |- ∀n. n < 16 ⇒ (UNHEX (HEX n) = n)

   [UNHEX_def]  Theorem

      |- (UNHEX #"0" = 0) ∧ (UNHEX #"1" = 1) ∧ (UNHEX #"2" = 2) ∧
         (UNHEX #"3" = 3) ∧ (UNHEX #"4" = 4) ∧ (UNHEX #"5" = 5) ∧
         (UNHEX #"6" = 6) ∧ (UNHEX #"7" = 7) ∧ (UNHEX #"8" = 8) ∧
         (UNHEX #"9" = 9) ∧ (UNHEX #"a" = 10) ∧ (UNHEX #"b" = 11) ∧
         (UNHEX #"c" = 12) ∧ (UNHEX #"d" = 13) ∧ (UNHEX #"e" = 14) ∧
         (UNHEX #"f" = 15) ∧ (UNHEX #"A" = 10) ∧ (UNHEX #"B" = 11) ∧
         (UNHEX #"C" = 12) ∧ (UNHEX #"D" = 13) ∧ (UNHEX #"E" = 14) ∧
         (UNHEX #"F" = 15)

   [UNHEX_ind]  Theorem

      |- ∀P.
           P #"0" ∧ P #"1" ∧ P #"2" ∧ P #"3" ∧ P #"4" ∧ P #"5" ∧ P #"6" ∧
           P #"7" ∧ P #"8" ∧ P #"9" ∧ P #"a" ∧ P #"b" ∧ P #"c" ∧ P #"d" ∧
           P #"e" ∧ P #"f" ∧ P #"A" ∧ P #"B" ∧ P #"C" ∧ P #"D" ∧ P #"E" ∧
           P #"F" ∧ (∀v24. P v24) ⇒
           ∀v. P v

   [n2s_compute]  Theorem

      |- n2s b f n = IMPLODE (REVERSE (MAP f (n2l b n)))

   [n2s_s2n]  Theorem

      |- ∀c2n n2c b s.
           1 < b ∧ EVERY ($> b o c2n) s ⇒
           (n2s b n2c (s2n b c2n s) =
            if s2n b c2n s = 0 then STRING (n2c 0) ""
            else MAP (n2c o c2n) (LASTN (SUC (LOG b (s2n b c2n s))) s))

   [num_bin_string]  Theorem

      |- num_from_bin_string o num_to_bin_string = I

   [num_dec_string]  Theorem

      |- toNum o toString = I

   [num_hex_string]  Theorem

      |- num_from_hex_string o num_to_hex_string = I

   [num_oct_string]  Theorem

      |- num_from_oct_string o num_to_oct_string = I

   [s2n_compute]  Theorem

      |- s2n b f s = l2n b (MAP f (REVERSE (EXPLODE s)))

   [s2n_n2s]  Theorem

      |- ∀c2n n2c b n.
           1 < b ∧ (∀x. x < b ⇒ (c2n (n2c x) = x)) ⇒
           (s2n b c2n (n2s b n2c n) = n)

   [toNum_toString]  Theorem

      |- ∀n. toNum (toString n) = n

   [toString_11]  Theorem

      |- ∀n m. (toString n = toString m) ⇔ (n = m)

   [toString_inj]  Theorem

      |- ∀n m. (toString n = toString m) ⇔ (n = m)

   [toString_toNum_cancel]  Theorem

      |- ∀n. toNum (toString n) = n


*)
end
