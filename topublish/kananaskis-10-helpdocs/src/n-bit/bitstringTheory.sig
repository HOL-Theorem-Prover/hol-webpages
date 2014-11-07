signature bitstringTheory =
sig
  type thm = Thm.thm

  (*  Definitions  *)
    val add_def : thm
    val band_def : thm
    val bitify_curried_def : thm
    val bitify_tupled_primitive_def : thm
    val bitwise_def : thm
    val bnand_def : thm
    val bnor_def : thm
    val bnot_def : thm
    val boolify_def : thm
    val bor_def : thm
    val bxnor_def : thm
    val bxor_def : thm
    val extend_def : thm
    val field_def : thm
    val field_insert_def : thm
    val fixwidth_def : thm
    val modify_def : thm
    val n2v_def : thm
    val replicate_def : thm
    val rev_count_list_def : thm
    val rotate_def : thm
    val s2v_def : thm
    val shiftl_def : thm
    val shiftr_def : thm
    val sign_extend_def : thm
    val testbit_def : thm
    val v2n_def : thm
    val v2s_def : thm
    val v2w_def : thm
    val w2v_def : thm
    val zero_extend_def : thm

  (*  Theorems  *)
    val bit_v2w : thm
    val bitify_def : thm
    val bitify_ind : thm
    val bitify_reverse_map : thm
    val bitstring_nchotomy : thm
    val boolify_reverse_map : thm
    val el_field : thm
    val el_fixwidth : thm
    val el_rev_count_list : thm
    val el_shiftr : thm
    val el_sign_extend : thm
    val el_w2v : thm
    val el_zero_extend : thm
    val every_bit_bitify : thm
    val extend : thm
    val extend_cons : thm
    val extend_def_compute : thm
    val extract_v2w : thm
    val field_concat_left : thm
    val field_concat_right : thm
    val field_fixwidth : thm
    val field_id_imp : thm
    val fixwidth : thm
    val fixwidth_eq : thm
    val fixwidth_fixwidth : thm
    val fixwidth_id : thm
    val fixwidth_id_imp : thm
    val length_bitify : thm
    val length_bitify_null : thm
    val length_field : thm
    val length_fixwidth : thm
    val length_pad_left : thm
    val length_pad_right : thm
    val length_rev_count_list : thm
    val length_shiftr : thm
    val length_sign_extend : thm
    val length_w2v : thm
    val length_zero_extend : thm
    val n2w_v2n : thm
    val ops_to_n2w : thm
    val ops_to_v2w : thm
    val pad_left_extend : thm
    val ranged_bitstring_nchotomy : thm
    val reduce_and_v2w : thm
    val reduce_or_v2w : thm
    val shiftl_replicate_F : thm
    val shiftr_0 : thm
    val sw2sw_v2w : thm
    val testbit : thm
    val testbit_el : thm
    val testbit_geq_len : thm
    val testbit_w2v : thm
    val v2n_lt : thm
    val v2n_n2v : thm
    val v2w_11 : thm
    val v2w_fixwidth : thm
    val v2w_n2v : thm
    val v2w_w2v : thm
    val w2n_v2w : thm
    val w2v_v2w : thm
    val w2w_v2w : thm
    val word_1comp_v2w : thm
    val word_and_v2w : thm
    val word_asr_v2w : thm
    val word_bit_last_shiftr : thm
    val word_bits_v2w : thm
    val word_concat_v2w : thm
    val word_concat_v2w_rwt : thm
    val word_extract_v2w : thm
    val word_index_v2w : thm
    val word_join_v2w : thm
    val word_join_v2w_rwt : thm
    val word_lsb_v2w : thm
    val word_lsl_v2w : thm
    val word_lsr_v2w : thm
    val word_modify_v2w : thm
    val word_msb_v2w : thm
    val word_nand_v2w : thm
    val word_nor_v2w : thm
    val word_or_v2w : thm
    val word_reduce_v2w : thm
    val word_reverse_v2w : thm
    val word_ror_v2w : thm
    val word_slice_v2w : thm
    val word_xnor_v2w : thm
    val word_xor_v2w : thm

  val bitstring_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [words] Parent theory of "bitstring"

   [add_def]  Definition

      |- ∀a b.
           add a b =
           (let m = MAX (LENGTH a) (LENGTH b)
            in
              zero_extend m (n2v (v2n a + v2n b)))

   [band_def]  Definition

      |- band = bitwise $/\

   [bitify_curried_def]  Definition

      |- ∀x x1. bitify x x1 = bitify_tupled (x,x1)

   [bitify_tupled_primitive_def]  Definition

      |- bitify_tupled =
         WFREC
           (@R.
              WF R ∧ (∀l a. R (0::a,l) (a,F::l)) ∧
              ∀l a. R (1::a,l) (a,T::l))
           (λbitify_tupled a'.
              case a' of
                (a,[]) => I a
              | (a,T::l) => I (bitify_tupled (1::a,l))
              | (a,F::l) => I (bitify_tupled (0::a,l)))

   [bitwise_def]  Definition

      |- ∀f v1 v2.
           bitwise f v1 v2 =
           (let m = MAX (LENGTH v1) (LENGTH v2)
            in
              MAP (UNCURRY f) (ZIP (fixwidth m v1,fixwidth m v2)))

   [bnand_def]  Definition

      |- bnand = bitwise (λx y. ¬(x ∧ y))

   [bnor_def]  Definition

      |- bnor = bitwise (λx y. ¬(x ∨ y))

   [bnot_def]  Definition

      |- bnot = MAP $~

   [boolify_def]  Definition

      |- (∀a. boolify a [] = a) ∧
         ∀a n l. boolify a (n::l) = boolify ((n ≠ 0)::a) l

   [bor_def]  Definition

      |- bor = bitwise $\/

   [bxnor_def]  Definition

      |- bxnor = bitwise $<=>

   [bxor_def]  Definition

      |- bxor = bitwise (λx y. x ⇎ y)

   [extend_def]  Definition

      |- (∀v0 l. extend v0 0 l = l) ∧
         ∀c n l. extend c (SUC n) l = extend c n (c::l)

   [field_def]  Definition

      |- ∀h l v. field h l v = fixwidth (SUC h − l) (shiftr v l)

   [field_insert_def]  Definition

      |- ∀h l s.
           field_insert h l s =
           modify (λi. COND (l ≤ i ∧ i ≤ h) (testbit (i − l) s))

   [fixwidth_def]  Definition

      |- ∀n v.
           fixwidth n v =
           (let l = LENGTH v
            in
              if l < n then zero_extend n v else DROP (l − n) v)

   [modify_def]  Definition

      |- ∀f v.
           modify f v = MAP (UNCURRY f) (ZIP (rev_count_list (LENGTH v),v))

   [n2v_def]  Definition

      |- ∀n.
           n2v n =
           if n = 0 then [F]
           else
             (let w = LOG2 n
              in
                PAD_LEFT F (w + 1)
                  (boolify [] (num_to_bin_list (BITS w 0 n))))

   [replicate_def]  Definition

      |- ∀v n. replicate v n = FLAT (GENLIST (K v) n)

   [rev_count_list_def]  Definition

      |- ∀n. rev_count_list n = GENLIST (λi. n − 1 − i) n

   [rotate_def]  Definition

      |- ∀v m.
           rotate v m =
           (let l = LENGTH v in
            let x = m MOD l
            in
              if x = 0 then v else field (x − 1) 0 v ++ field (l − 1) x v)

   [s2v_def]  Definition

      |- s2v = MAP (λc. (c = #"1") ∨ (c = #"T"))

   [shiftl_def]  Definition

      |- ∀v m. shiftl v m = PAD_RIGHT F (LENGTH v + m) v

   [shiftr_def]  Definition

      |- ∀v m. shiftr v m = TAKE (LENGTH v − m) v

   [sign_extend_def]  Definition

      |- ∀n v. sign_extend n v = PAD_LEFT (HD v) n v

   [testbit_def]  Definition

      |- ∀b v. testbit b v ⇔ (field b b v = [T])

   [v2n_def]  Definition

      |- ∀l. v2n l = num_from_bin_list (bitify [] l)

   [v2s_def]  Definition

      |- v2s = MAP (λb. if b then #"1" else #"0")

   [v2w_def]  Definition

      |- ∀v. v2w v = FCP i. testbit i v

   [w2v_def]  Definition

      |- ∀w.
           w2v w =
           GENLIST (λi. w ' (dimindex (:α) − 1 − i)) (dimindex (:α))

   [zero_extend_def]  Definition

      |- ∀n v. zero_extend n v = PAD_LEFT F n v

   [bit_v2w]  Theorem

      |- ∀n v. word_bit n (v2w v) ⇔ n < dimindex (:α) ∧ testbit n v

   [bitify_def]  Theorem

      |- (∀a. bitify a [] = a) ∧
         (∀l a. bitify a (F::l) = bitify (0::a) l) ∧
         ∀l a. bitify a (T::l) = bitify (1::a) l

   [bitify_ind]  Theorem

      |- ∀P.
           (∀a. P a []) ∧ (∀a l. P (0::a) l ⇒ P a (F::l)) ∧
           (∀a l. P (1::a) l ⇒ P a (T::l)) ⇒
           ∀v v1. P v v1

   [bitify_reverse_map]  Theorem

      |- ∀v a. bitify a v = REVERSE (MAP (λb. if b then 1 else 0) v) ++ a

   [bitstring_nchotomy]  Theorem

      |- ∀w. ∃v. w = v2w v

   [boolify_reverse_map]  Theorem

      |- ∀v a. boolify a v = REVERSE (MAP (λn. n ≠ 0) v) ++ a

   [el_field]  Theorem

      |- ∀v h l i.
           i < SUC h − l ⇒
           (EL i (field h l v) ⇔
            SUC h ≤ i + LENGTH v ∧ EL (i + LENGTH v − SUC h) v)

   [el_fixwidth]  Theorem

      |- ∀i n w.
           i < n ⇒
           (EL i (fixwidth n w) ⇔
            if LENGTH w < n then
              n − LENGTH w ≤ i ∧ EL (i − (n − LENGTH w)) w
            else EL (i + (LENGTH w − n)) w)

   [el_rev_count_list]  Theorem

      |- ∀n i. i < n ⇒ (EL i (rev_count_list n) = n − 1 − i)

   [el_shiftr]  Theorem

      |- ∀i v n d.
           n < d ∧ i < d − n ∧ 0 < d ⇒
           (EL i (shiftr (fixwidth d v) n) ⇔
            d ≤ i + LENGTH v ∧ EL (i + LENGTH v − d) v)

   [el_sign_extend]  Theorem

      |- ∀n i v.
           EL i (sign_extend n v) =
           if i < n − LENGTH v then EL 0 v else EL (i − (n − LENGTH v)) v

   [el_w2v]  Theorem

      |- ∀w n.
           n < dimindex (:α) ⇒ (EL n (w2v w) ⇔ w ' (dimindex (:α) − 1 − n))

   [el_zero_extend]  Theorem

      |- ∀n i v.
           EL i (zero_extend n v) ⇔
           n − LENGTH v ≤ i ∧ EL (i − (n − LENGTH v)) v

   [every_bit_bitify]  Theorem

      |- ∀v. EVERY ($> 2) (bitify [] v)

   [extend]  Theorem

      |- (∀n v. zero_extend n v = extend F (n − LENGTH v) v) ∧
         ∀n v. sign_extend n v = extend (HD v) (n − LENGTH v) v

   [extend_cons]  Theorem

      |- ∀n c l. extend c (SUC n) l = c::extend c n l

   [extend_def_compute]  Theorem

      |- (∀v0 l. extend v0 0 l = l) ∧
         (∀c n l.
            extend c (NUMERAL (BIT1 n)) l =
            extend c (NUMERAL (BIT1 n) − 1) (c::l)) ∧
         ∀c n l.
           extend c (NUMERAL (BIT2 n)) l =
           extend c (NUMERAL (BIT1 n)) (c::l)

   [extract_v2w]  Theorem

      |- ∀h l v.
           LENGTH v ≤ dimindex (:α) ∧ (dimindex (:β) = SUC h − l) ∧
           dimindex (:β) < dimindex (:α) ⇒
           ((h >< l) (v2w v) = v2w (field h l v))

   [field_concat_left]  Theorem

      |- ∀h l a b.
           l ≤ h ∧ LENGTH b ≤ l ⇒
           (field h l (a ++ b) = field (h − LENGTH b) (l − LENGTH b) a)

   [field_concat_right]  Theorem

      |- ∀h a b. (LENGTH b = SUC h) ⇒ (field h 0 (a ++ b) = b)

   [field_fixwidth]  Theorem

      |- ∀h v. field h 0 v = fixwidth (SUC h) v

   [field_id_imp]  Theorem

      |- ∀n v. (SUC n = LENGTH v) ⇒ (field n 0 v = v)

   [fixwidth]  Theorem

      |- ∀n v.
           fixwidth n v =
           (let l = LENGTH v
            in
              if l < n then extend F (n − l) v else DROP (l − n) v)

   [fixwidth_eq]  Theorem

      |- ∀n v w.
           (fixwidth n v = fixwidth n w) ⇔
           ∀i. i < n ⇒ (testbit i v ⇔ testbit i w)

   [fixwidth_fixwidth]  Theorem

      |- ∀n v. fixwidth n (fixwidth n v) = fixwidth n v

   [fixwidth_id]  Theorem

      |- ∀w. fixwidth (LENGTH w) w = w

   [fixwidth_id_imp]  Theorem

      |- ∀n w. (n = LENGTH w) ⇒ (fixwidth n w = w)

   [length_bitify]  Theorem

      |- ∀v l. LENGTH (bitify l v) = LENGTH l + LENGTH v

   [length_bitify_null]  Theorem

      |- ∀v l. LENGTH (bitify [] v) = LENGTH v

   [length_field]  Theorem

      |- ∀h l v. LENGTH (field h l v) = SUC h − l

   [length_fixwidth]  Theorem

      |- ∀n v. LENGTH (fixwidth n v) = n

   [length_pad_left]  Theorem

      |- ∀x n a.
           LENGTH (PAD_LEFT x n a) = if LENGTH a < n then n else LENGTH a

   [length_pad_right]  Theorem

      |- ∀x n a.
           LENGTH (PAD_RIGHT x n a) = if LENGTH a < n then n else LENGTH a

   [length_rev_count_list]  Theorem

      |- ∀n. LENGTH (rev_count_list n) = n

   [length_shiftr]  Theorem

      |- ∀v n. LENGTH (shiftr v n) = LENGTH v − n

   [length_sign_extend]  Theorem

      |- ∀n v. LENGTH v < n ⇒ (LENGTH (sign_extend n v) = n)

   [length_w2v]  Theorem

      |- ∀w. LENGTH (w2v w) = dimindex (:α)

   [length_zero_extend]  Theorem

      |- ∀n v. LENGTH v < n ⇒ (LENGTH (zero_extend n v) = n)

   [n2w_v2n]  Theorem

      |- ∀v. n2w (v2n v) = v2w v

   [ops_to_n2w]  Theorem

      |- (∀v. -v2w v = -n2w (v2n v)) ∧
         (∀v. word_log2 (v2w v) = word_log2 (n2w (v2n v))) ∧
         (∀v n. (v2w v = n2w n) ⇔ (n2w (v2n v) = n2w n)) ∧
         (∀v n. (n2w n = v2w v) ⇔ (n2w n = n2w (v2n v))) ∧
         (∀v w. v2w v + w = n2w (v2n v) + w) ∧
         (∀v w. w + v2w v = w + n2w (v2n v)) ∧
         (∀v w. v2w v − w = n2w (v2n v) − w) ∧
         (∀v w. w − v2w v = w − n2w (v2n v)) ∧
         (∀v w. v2w v * w = n2w (v2n v) * w) ∧
         (∀v w. w * v2w v = w * n2w (v2n v)) ∧
         (∀v w. v2w v / w = n2w (v2n v) / w) ∧
         (∀v w. w / v2w v = w / n2w (v2n v)) ∧
         (∀v w. v2w v // w = n2w (v2n v) // w) ∧
         (∀v w. w // v2w v = w // n2w (v2n v)) ∧
         (∀v w. word_mod (v2w v) w = word_mod (n2w (v2n v)) w) ∧
         (∀v w. word_mod w (v2w v) = word_mod w (n2w (v2n v))) ∧
         (∀v w. v2w v < w ⇔ n2w (v2n v) < w) ∧
         (∀v w. w < v2w v ⇔ w < n2w (v2n v)) ∧
         (∀v w. v2w v > w ⇔ n2w (v2n v) > w) ∧
         (∀v w. w > v2w v ⇔ w > n2w (v2n v)) ∧
         (∀v w. v2w v ≤ w ⇔ n2w (v2n v) ≤ w) ∧
         (∀v w. w ≤ v2w v ⇔ w ≤ n2w (v2n v)) ∧
         (∀v w. v2w v ≥ w ⇔ n2w (v2n v) ≥ w) ∧
         (∀v w. w ≥ v2w v ⇔ w ≥ n2w (v2n v)) ∧
         (∀v w. v2w v <₊ w ⇔ n2w (v2n v) <₊ w) ∧
         (∀v w. w <₊ v2w v ⇔ w <₊ n2w (v2n v)) ∧
         (∀v w. v2w v >₊ w ⇔ n2w (v2n v) >₊ w) ∧
         (∀v w. w >₊ v2w v ⇔ w >₊ n2w (v2n v)) ∧
         (∀v w. v2w v ≤₊ w ⇔ n2w (v2n v) ≤₊ w) ∧
         (∀v w. w ≤₊ v2w v ⇔ w ≤₊ n2w (v2n v)) ∧
         (∀v w. v2w v ≥₊ w ⇔ n2w (v2n v) ≥₊ w) ∧
         ∀v w. w ≥₊ v2w v ⇔ w ≥₊ n2w (v2n v)

   [ops_to_v2w]  Theorem

      |- (∀v n. v2w v ‖ n2w n = v2w v ‖ v2w (n2v n)) ∧
         (∀v n. n2w n ‖ v2w v = v2w (n2v n) ‖ v2w v) ∧
         (∀v n. v2w v && n2w n = v2w v && v2w (n2v n)) ∧
         (∀v n. n2w n && v2w v = v2w (n2v n) && v2w v) ∧
         (∀v n. v2w v ⊕ n2w n = v2w v ⊕ v2w (n2v n)) ∧
         (∀v n. n2w n ⊕ v2w v = v2w (n2v n) ⊕ v2w v) ∧
         (∀v n. v2w v ~|| n2w n = v2w v ~|| v2w (n2v n)) ∧
         (∀v n. n2w n ~|| v2w v = v2w (n2v n) ~|| v2w v) ∧
         (∀v n. v2w v ~&& n2w n = v2w v ~&& v2w (n2v n)) ∧
         (∀v n. n2w n ~&& v2w v = v2w (n2v n) ~&& v2w v) ∧
         (∀v n. v2w v ~?? n2w n = v2w v ~?? v2w (n2v n)) ∧
         (∀v n. n2w n ~?? v2w v = v2w (n2v n) ~?? v2w v) ∧
         (∀v n. v2w v @@ n2w n = v2w v @@ v2w (n2v n)) ∧
         (∀v n. n2w n @@ v2w v = v2w (n2v n) @@ v2w v) ∧
         (∀v n.
            word_join (v2w v) (n2w n) = word_join (v2w v) (v2w (n2v n))) ∧
         ∀v n. word_join (n2w n) (v2w v) = word_join (v2w (n2v n)) (v2w v)

   [pad_left_extend]  Theorem

      |- ∀n l c. PAD_LEFT c n l = extend c (n − LENGTH l) l

   [ranged_bitstring_nchotomy]  Theorem

      |- ∀w. ∃v. (w = v2w v) ∧ Abbrev (LENGTH v = dimindex (:α))

   [reduce_and_v2w]  Theorem

      |- ∀v. reduce_and (v2w v) = word_reduce $/\ (v2w v)

   [reduce_or_v2w]  Theorem

      |- ∀v. reduce_or (v2w v) = word_reduce $\/ (v2w v)

   [shiftl_replicate_F]  Theorem

      |- ∀v n. shiftl v n = v ++ replicate [F] n

   [shiftr_0]  Theorem

      |- ∀v. shiftr v 0 = v

   [sw2sw_v2w]  Theorem

      |- ∀v.
           sw2sw (v2w v) =
           if dimindex (:α) < dimindex (:β) then
             v2w (sign_extend (dimindex (:β)) (fixwidth (dimindex (:α)) v))
           else v2w (fixwidth (dimindex (:β)) v)

   [testbit]  Theorem

      |- ∀b v. testbit b v ⇔ (let n = LENGTH v in b < n ∧ EL (n − 1 − b) v)

   [testbit_el]  Theorem

      |- ∀v i. i < LENGTH v ⇒ (testbit i v ⇔ EL (LENGTH v − 1 − i) v)

   [testbit_geq_len]  Theorem

      |- ∀v i. LENGTH v ≤ i ⇒ ¬testbit i v

   [testbit_w2v]  Theorem

      |- ∀n w. testbit n (w2v w) ⇔ word_bit n w

   [v2n_lt]  Theorem

      |- ∀v. v2n v < 2 ** LENGTH v

   [v2n_n2v]  Theorem

      |- ∀n. v2n (n2v n) = n

   [v2w_11]  Theorem

      |- ∀v w.
           (v2w v = v2w w) ⇔
           (fixwidth (dimindex (:α)) v = fixwidth (dimindex (:α)) w)

   [v2w_fixwidth]  Theorem

      |- ∀v. v2w (fixwidth (dimindex (:α)) v) = v2w v

   [v2w_n2v]  Theorem

      |- ∀n. v2w (n2v n) = n2w n

   [v2w_w2v]  Theorem

      |- ∀w. v2w (w2v w) = w

   [w2n_v2w]  Theorem

      |- ∀v. w2n (v2w v) = MOD_2EXP (dimindex (:α)) (v2n v)

   [w2v_v2w]  Theorem

      |- ∀v. w2v (v2w v) = fixwidth (dimindex (:α)) v

   [w2w_v2w]  Theorem

      |- ∀v.
           w2w (v2w v) =
           v2w
             (fixwidth
                (if dimindex (:β) < dimindex (:α) then dimindex (:β)
                 else dimindex (:α)) v)

   [word_1comp_v2w]  Theorem

      |- ∀v. ¬v2w v = v2w (bnot (fixwidth (dimindex (:α)) v))

   [word_and_v2w]  Theorem

      |- ∀v w. v2w v && v2w w = v2w (band v w)

   [word_asr_v2w]  Theorem

      |- ∀n v.
           v2w v ≫ n =
           (let l = fixwidth (dimindex (:α)) v
            in
              v2w
                (sign_extend (dimindex (:α))
                   (if dimindex (:α) ≤ n then [HD l] else shiftr l n)))

   [word_bit_last_shiftr]  Theorem

      |- ∀i v.
           i < dimindex (:α) ⇒
           (word_bit i (v2w v) ⇔ (let l = shiftr v i in ¬NULL l ∧ LAST l))

   [word_bits_v2w]  Theorem

      |- ∀h l v.
           (h -- l) (v2w v) = v2w (field h l (fixwidth (dimindex (:α)) v))

   [word_concat_v2w]  Theorem

      |- ∀v1 v2.
           FINITE 𝕌(:α) ∧ FINITE 𝕌(:β) ⇒
           (v2w v1 @@ v2w v2 =
            v2w
              (fixwidth
                 (MIN (dimindex (:γ)) (dimindex (:α) + dimindex (:β)))
                 (v1 ++ fixwidth (dimindex (:β)) v2)))

   [word_concat_v2w_rwt]  Theorem

      |- ∀v1 v2.
           v2w v1 @@ v2w v2 =
           if FINITE 𝕌(:α) ∧ FINITE 𝕌(:β) then
             v2w
               (fixwidth
                  (MIN (dimindex (:γ)) (dimindex (:α) + dimindex (:β)))
                  (v1 ++ fixwidth (dimindex (:β)) v2))
           else FAIL $@@ bad domain (v2w v1) (v2w v2)

   [word_extract_v2w]  Theorem

      |- ∀h l v. (h >< l) (v2w v) = w2w ((h -- l) (v2w v))

   [word_index_v2w]  Theorem

      |- ∀v i.
           v2w v ' i ⇔
           if i < dimindex (:α) then testbit i v
           else FAIL $' index too large (v2w v) i

   [word_join_v2w]  Theorem

      |- ∀v1 v2.
           FINITE 𝕌(:α) ∧ FINITE 𝕌(:β) ⇒
           (word_join (v2w v1) (v2w v2) =
            v2w (v1 ++ fixwidth (dimindex (:β)) v2))

   [word_join_v2w_rwt]  Theorem

      |- ∀v1 v2.
           word_join (v2w v1) (v2w v2) =
           if FINITE 𝕌(:α) ∧ FINITE 𝕌(:β) then
             v2w (v1 ++ fixwidth (dimindex (:β)) v2)
           else FAIL word_join bad domain (v2w v1) (v2w v2)

   [word_lsb_v2w]  Theorem

      |- ∀v. word_lsb (v2w v) ⇔ v ≠ [] ∧ LAST v

   [word_lsl_v2w]  Theorem

      |- ∀n v. v2w v ≪ n = v2w (shiftl v n)

   [word_lsr_v2w]  Theorem

      |- ∀n v. v2w v ⋙ n = v2w (shiftr (fixwidth (dimindex (:α)) v) n)

   [word_modify_v2w]  Theorem

      |- ∀f v.
           word_modify f (v2w v) =
           v2w (modify f (fixwidth (dimindex (:α)) v))

   [word_msb_v2w]  Theorem

      |- ∀v. word_msb (v2w v) ⇔ testbit (dimindex (:α) − 1) v

   [word_nand_v2w]  Theorem

      |- ∀v w.
           v2w v ~&& v2w w =
           v2w
             (bnand (fixwidth (dimindex (:α)) v)
                (fixwidth (dimindex (:α)) w))

   [word_nor_v2w]  Theorem

      |- ∀v w.
           v2w v ~|| v2w w =
           v2w
             (bnor (fixwidth (dimindex (:α)) v)
                (fixwidth (dimindex (:α)) w))

   [word_or_v2w]  Theorem

      |- ∀v w. v2w v ‖ v2w w = v2w (bor v w)

   [word_reduce_v2w]  Theorem

      |- ∀f v.
           word_reduce f (v2w v) =
           (let l = fixwidth (dimindex (:α)) v
            in
              v2w [FOLDL f (HD l) (TL l)])

   [word_reverse_v2w]  Theorem

      |- ∀v.
           word_reverse (v2w v) =
           v2w (REVERSE (fixwidth (dimindex (:α)) v))

   [word_ror_v2w]  Theorem

      |- ∀n v. v2w v ⇄ n = v2w (rotate (fixwidth (dimindex (:α)) v) n)

   [word_slice_v2w]  Theorem

      |- ∀h l v.
           (h '' l) (v2w v) =
           v2w (shiftl (field h l (fixwidth (dimindex (:α)) v)) l)

   [word_xnor_v2w]  Theorem

      |- ∀v w.
           v2w v ~?? v2w w =
           v2w
             (bxnor (fixwidth (dimindex (:α)) v)
                (fixwidth (dimindex (:α)) w))

   [word_xor_v2w]  Theorem

      |- ∀v w. v2w v ⊕ v2w w = v2w (bxor v w)


*)
end
