signature HolSmtTheory =
sig
  type thm = Thm.thm

  (*  Definitions  *)
    val array_ext_def : thm
    val xor_def : thm

  (*  Theorems  *)
    val ALL_DISTINCT_CONS : thm
    val ALL_DISTINCT_NIL : thm
    val AND_IMP_INTRO_SYM : thm
    val AND_T : thm
    val CONJ_CONG : thm
    val DISJ_ELIM_1 : thm
    val DISJ_ELIM_2 : thm
    val F_OR : thm
    val IMP_DISJ_1 : thm
    val IMP_DISJ_2 : thm
    val IMP_FALSE : thm
    val NEG_IFF_1_1 : thm
    val NEG_IFF_1_2 : thm
    val NEG_IFF_2_1 : thm
    val NEG_IFF_2_2 : thm
    val NNF_CONJ : thm
    val NNF_DISJ : thm
    val NNF_NOT_NOT : thm
    val NOT_FALSE : thm
    val NOT_MEM_CONS : thm
    val NOT_MEM_NIL : thm
    val NOT_NOT_ELIM : thm
    val T_AND : thm
    val VALID_IFF_TRUE : thm
    val d001 : thm
    val d002 : thm
    val d003 : thm
    val d004 : thm
    val d005 : thm
    val d006 : thm
    val d007 : thm
    val d008 : thm
    val d009 : thm
    val d010 : thm
    val d011 : thm
    val d012 : thm
    val d013 : thm
    val d014 : thm
    val d015 : thm
    val d016 : thm
    val d017 : thm
    val d018 : thm
    val d019 : thm
    val d020 : thm
    val d021 : thm
    val d022 : thm
    val d023 : thm
    val d024 : thm
    val d025 : thm
    val d026 : thm
    val d027 : thm
    val d028 : thm
    val p001 : thm
    val p002 : thm
    val p003 : thm
    val p004 : thm
    val p005 : thm
    val p006 : thm
    val p007 : thm
    val p008 : thm
    val p009 : thm
    val r001 : thm
    val r002 : thm
    val r003 : thm
    val r004 : thm
    val r005 : thm
    val r006 : thm
    val r007 : thm
    val r008 : thm
    val r009 : thm
    val r010 : thm
    val r011 : thm
    val r012 : thm
    val r013 : thm
    val r014 : thm
    val r015 : thm
    val r016 : thm
    val r017 : thm
    val r018 : thm
    val r019 : thm
    val r020 : thm
    val r021 : thm
    val r022 : thm
    val r023 : thm
    val r024 : thm
    val r025 : thm
    val r026 : thm
    val r027 : thm
    val r028 : thm
    val r029 : thm
    val r030 : thm
    val r031 : thm
    val r032 : thm
    val r033 : thm
    val r034 : thm
    val r035 : thm
    val r036 : thm
    val r037 : thm
    val r038 : thm
    val r039 : thm
    val r040 : thm
    val r041 : thm
    val r042 : thm
    val r043 : thm
    val r044 : thm
    val r045 : thm
    val r046 : thm
    val r047 : thm
    val r048 : thm
    val r049 : thm
    val r050 : thm
    val r051 : thm
    val r052 : thm
    val r053 : thm
    val r054 : thm
    val r055 : thm
    val r056 : thm
    val r057 : thm
    val r058 : thm
    val r059 : thm
    val r060 : thm
    val r061 : thm
    val r062 : thm
    val r063 : thm
    val r064 : thm
    val r065 : thm
    val r066 : thm
    val r067 : thm
    val r068 : thm
    val r069 : thm
    val r070 : thm
    val r071 : thm
    val r072 : thm
    val r073 : thm
    val r074 : thm
    val r075 : thm
    val r076 : thm
    val r077 : thm
    val r078 : thm
    val r079 : thm
    val r080 : thm
    val r081 : thm
    val r082 : thm
    val r083 : thm
    val r084 : thm
    val r085 : thm
    val r086 : thm
    val r087 : thm
    val r088 : thm
    val r089 : thm
    val r090 : thm
    val r091 : thm
    val r092 : thm
    val r093 : thm
    val r094 : thm
    val r095 : thm
    val r096 : thm
    val r097 : thm
    val r098 : thm
    val r099 : thm
    val r100 : thm
    val r101 : thm
    val r102 : thm
    val r103 : thm
    val r104 : thm
    val r105 : thm
    val r106 : thm
    val r107 : thm
    val r108 : thm
    val r109 : thm
    val r110 : thm
    val r111 : thm
    val r112 : thm
    val r113 : thm
    val r114 : thm
    val r115 : thm
    val r116 : thm
    val r117 : thm
    val r118 : thm
    val r119 : thm
    val r120 : thm
    val r121 : thm
    val r122 : thm
    val r123 : thm
    val r124 : thm
    val r125 : thm
    val r126 : thm
    val r127 : thm
    val r128 : thm
    val r129 : thm
    val r130 : thm
    val r131 : thm
    val r132 : thm
    val r133 : thm
    val r134 : thm
    val r135 : thm
    val r136 : thm
    val r137 : thm
    val r138 : thm
    val r139 : thm
    val r140 : thm
    val r141 : thm
    val r142 : thm
    val r143 : thm
    val r144 : thm
    val r145 : thm
    val r146 : thm
    val r147 : thm
    val r148 : thm
    val r149 : thm
    val r150 : thm
    val r151 : thm
    val r152 : thm
    val r153 : thm
    val r154 : thm
    val r155 : thm
    val r156 : thm
    val r157 : thm
    val r158 : thm
    val r159 : thm
    val r160 : thm
    val r161 : thm
    val r162 : thm
    val r163 : thm
    val r164 : thm
    val r165 : thm
    val r166 : thm
    val r167 : thm
    val r168 : thm
    val r169 : thm
    val r170 : thm
    val r171 : thm
    val r172 : thm
    val r173 : thm
    val r174 : thm
    val r175 : thm
    val r176 : thm
    val r177 : thm
    val r178 : thm
    val r179 : thm
    val r180 : thm
    val r181 : thm
    val r182 : thm
    val r183 : thm
    val r184 : thm
    val r185 : thm
    val r186 : thm
    val r187 : thm
    val r188 : thm
    val r189 : thm
    val r190 : thm
    val r191 : thm
    val r192 : thm
    val r193 : thm
    val r194 : thm
    val r195 : thm
    val r196 : thm
    val r197 : thm
    val r198 : thm
    val r199 : thm
    val r200 : thm
    val r201 : thm
    val r202 : thm
    val r203 : thm
    val r204 : thm
    val r205 : thm
    val r206 : thm
    val r207 : thm
    val r208 : thm
    val r209 : thm
    val r210 : thm
    val r211 : thm
    val r212 : thm
    val r213 : thm
    val r214 : thm
    val r215 : thm
    val r216 : thm
    val r217 : thm
    val r218 : thm
    val r219 : thm
    val r220 : thm
    val r221 : thm
    val r222 : thm
    val r223 : thm
    val r224 : thm
    val r225 : thm
    val r226 : thm
    val r227 : thm
    val r228 : thm
    val r229 : thm
    val r230 : thm
    val r231 : thm
    val r232 : thm
    val r233 : thm
    val r234 : thm
    val r235 : thm
    val r236 : thm
    val r237 : thm
    val r238 : thm
    val r239 : thm
    val r240 : thm
    val r241 : thm
    val r242 : thm
    val r243 : thm
    val r244 : thm
    val r245 : thm
    val r246 : thm
    val r247 : thm
    val r248 : thm
    val r249 : thm
    val r250 : thm
    val r251 : thm
    val r252 : thm
    val r253 : thm
    val r254 : thm
    val r255 : thm
    val t001 : thm
    val t002 : thm
    val t003 : thm
    val t004 : thm
    val t005 : thm
    val t006 : thm
    val t007 : thm
    val t008 : thm
    val t009 : thm
    val t010 : thm
    val t011 : thm
    val t012 : thm
    val t013 : thm
    val t014 : thm
    val t015 : thm
    val t016 : thm
    val t017 : thm
    val t018 : thm
    val t019 : thm
    val t020 : thm
    val t021 : thm
    val t022 : thm
    val t023 : thm
    val t024 : thm
    val t025 : thm
    val t026 : thm
    val t027 : thm
    val t028 : thm
    val t029 : thm
    val t030 : thm
    val t031 : thm
    val t032 : thm
    val t033 : thm
    val t034 : thm
    val t035 : thm

  val HolSmt_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [Omega] Parent theory of "HolSmt"

   [bitstring] Parent theory of "HolSmt"

   [blast] Parent theory of "HolSmt"

   [int_arith] Parent theory of "HolSmt"

   [poly] Parent theory of "HolSmt"

   [transc] Parent theory of "HolSmt"

   [array_ext_def]  Definition

      |- ∀A B. array_ext A B = @i. A i ≠ B i

   [xor_def]  Definition

      |- ∀x y. xor x y ⇔ (x ⇎ y)

   [ALL_DISTINCT_CONS]  Theorem

      |- ∀h t. ALL_DISTINCT (h::t) ⇔ ¬MEM h t ∧ ALL_DISTINCT t

   [ALL_DISTINCT_NIL]  Theorem

      |- ALL_DISTINCT [] ⇔ T

   [AND_IMP_INTRO_SYM]  Theorem

      |- ∀p q r. p ∧ q ⇒ r ⇔ p ⇒ q ⇒ r

   [AND_T]  Theorem

      |- ∀p. p ∧ T ⇔ p

   [CONJ_CONG]  Theorem

      |- ∀p q r s. (p ⇔ q) ⇒ (r ⇔ s) ⇒ (p ∧ r ⇔ q ∧ s)

   [DISJ_ELIM_1]  Theorem

      |- ∀p q r. (p ∨ q ⇒ r) ⇒ p ⇒ r

   [DISJ_ELIM_2]  Theorem

      |- ∀p q r. (p ∨ q ⇒ r) ⇒ q ⇒ r

   [F_OR]  Theorem

      |- ∀p q. (F ∨ p ⇔ F ∨ q) ⇒ (p ⇔ q)

   [IMP_DISJ_1]  Theorem

      |- ∀p q. (p ⇒ q) ⇒ ¬p ∨ q

   [IMP_DISJ_2]  Theorem

      |- ∀p q. (¬p ⇒ q) ⇒ p ∨ q

   [IMP_FALSE]  Theorem

      |- ∀p. (¬p ⇒ F) ⇒ p

   [NEG_IFF_1_1]  Theorem

      |- ∀p q. (q ⇔ p) ⇒ (p ⇎ ¬q)

   [NEG_IFF_1_2]  Theorem

      |- ∀p q. (p ⇎ ¬q) ⇒ (q ⇔ p)

   [NEG_IFF_2_1]  Theorem

      |- ∀p q. (p ⇔ ¬q) ⇒ (p ⇎ q)

   [NEG_IFF_2_2]  Theorem

      |- ∀p q. (p ⇎ q) ⇒ (p ⇔ ¬q)

   [NNF_CONJ]  Theorem

      |- ∀p q r s. (¬p ⇔ r) ⇒ (¬q ⇔ s) ⇒ (¬(p ∧ q) ⇔ r ∨ s)

   [NNF_DISJ]  Theorem

      |- ∀p q r s. (¬p ⇔ r) ⇒ (¬q ⇔ s) ⇒ (¬(p ∨ q) ⇔ r ∧ s)

   [NNF_NOT_NOT]  Theorem

      |- ∀p q. (p ⇔ q) ⇒ (¬ ¬p ⇔ q)

   [NOT_FALSE]  Theorem

      |- ∀p. p ⇒ ¬p ⇒ F

   [NOT_MEM_CONS]  Theorem

      |- ∀x h t. ¬MEM x (h::t) ⇔ x ≠ h ∧ ¬MEM x t

   [NOT_MEM_NIL]  Theorem

      |- ∀x. ¬MEM x [] ⇔ T

   [NOT_NOT_ELIM]  Theorem

      |- ∀p. ¬ ¬p ⇒ p

   [T_AND]  Theorem

      |- ∀p q. (T ∧ p ⇔ T ∧ q) ⇒ (p ⇔ q)

   [VALID_IFF_TRUE]  Theorem

      |- ∀p. p ⇒ (p ⇔ T)

   [d001]  Theorem

      |- (p ⇎ q) ∨ ¬p ∨ q

   [d002]  Theorem

      |- (p ⇎ q) ∨ p ∨ ¬q

   [d003]  Theorem

      |- (p ⇔ ¬q) ∨ ¬p ∨ q

   [d004]  Theorem

      |- (¬p ⇔ q) ∨ p ∨ ¬q

   [d005]  Theorem

      |- (p ⇔ q) ∨ ¬p ∨ ¬q

   [d006]  Theorem

      |- (p ⇔ q) ∨ p ∨ q

   [d007]  Theorem

      |- (¬p ⇎ q) ∨ p ∨ q

   [d008]  Theorem

      |- (p ⇎ ¬q) ∨ p ∨ q

   [d009]  Theorem

      |- ¬p ∨ q ∨ (p ⇎ q)

   [d010]  Theorem

      |- p ∨ ¬q ∨ (p ⇎ q)

   [d011]  Theorem

      |- p ∨ q ∨ (¬p ⇎ q)

   [d012]  Theorem

      |- p ∨ q ∨ (p ⇎ ¬q)

   [d013]  Theorem

      |- ¬p ∧ ¬q ∨ p ∨ q

   [d014]  Theorem

      |- ¬p ∧ q ∨ p ∨ ¬q

   [d015]  Theorem

      |- p ∧ ¬q ∨ ¬p ∨ q

   [d016]  Theorem

      |- p ∧ q ∨ ¬p ∨ ¬q

   [d017]  Theorem

      |- p ∨ (y = if p then x else y)

   [d018]  Theorem

      |- ¬p ∨ (x = if p then x else y)

   [d019]  Theorem

      |- p ∨ ((if p then x else y) = y)

   [d020]  Theorem

      |- ¬p ∨ ((if p then x else y) = x)

   [d021]  Theorem

      |- p ∨ q ∨ ¬if p then r else q

   [d022]  Theorem

      |- ¬p ∨ q ∨ ¬if p then q else r

   [d023]  Theorem

      |- (if p then q else r) ∨ ¬p ∨ ¬q

   [d024]  Theorem

      |- (if p then q else r) ∨ p ∨ ¬r

   [d025]  Theorem

      |- (if p then ¬q else r) ∨ ¬p ∨ q

   [d026]  Theorem

      |- (if p then q else ¬r) ∨ p ∨ r

   [d027]  Theorem

      |- ¬(if p then q else r) ∨ ¬p ∨ q

   [d028]  Theorem

      |- ¬(if p then q else r) ∨ p ∨ r

   [p001]  Theorem

      |- 0 < dimword (:α)

   [p002]  Theorem

      |- 1 < dimword (:α)

   [p003]  Theorem

      |- 255 < dimword (:8)

   [p004]  Theorem

      |- FINITE 𝕌(:unit)

   [p005]  Theorem

      |- FINITE 𝕌(:16)

   [p006]  Theorem

      |- FINITE 𝕌(:24)

   [p007]  Theorem

      |- FINITE 𝕌(:30)

   [p008]  Theorem

      |- FINITE 𝕌(:31)

   [p009]  Theorem

      |- dimindex (:8) ≤ dimindex (:32)

   [r001]  Theorem

      |- (x = y) ⇔ (y = x)

   [r002]  Theorem

      |- (x = x) ⇔ T

   [r003]  Theorem

      |- (p ⇔ T) ⇔ p

   [r004]  Theorem

      |- (T ⇔ p) ⇔ p

   [r005]  Theorem

      |- (p ⇔ F) ⇔ ¬p

   [r006]  Theorem

      |- (F ⇔ p) ⇔ ¬p

   [r007]  Theorem

      |- (¬p ⇔ ¬q) ⇔ (p ⇔ q)

   [r008]  Theorem

      |- (p ⇎ ¬q) ⇔ (p ⇔ q)

   [r009]  Theorem

      |- (¬p ⇎ q) ⇔ (p ⇔ q)

   [r010]  Theorem

      |- (if T then x else y) = x

   [r011]  Theorem

      |- (if F then x else y) = y

   [r012]  Theorem

      |- (if p then q else T) ⇔ ¬p ∨ q

   [r013]  Theorem

      |- (if p then q else T) ⇔ q ∨ ¬p

   [r014]  Theorem

      |- (if p then q else ¬q) ⇔ (p ⇔ q)

   [r015]  Theorem

      |- (if p then q else ¬q) ⇔ (q ⇔ p)

   [r016]  Theorem

      |- (if p then ¬q else q) ⇔ (p ⇔ ¬q)

   [r017]  Theorem

      |- (if p then ¬q else q) ⇔ (¬q ⇔ p)

   [r018]  Theorem

      |- (if ¬p then x else y) = if p then y else x

   [r019]  Theorem

      |- (if p then if q then x else y else x) = if p ∧ ¬q then y else x

   [r020]  Theorem

      |- (if p then if q then x else y else x) = if ¬q ∧ p then y else x

   [r021]  Theorem

      |- (if p then if q then x else y else y) = if p ∧ q then x else y

   [r022]  Theorem

      |- (if p then if q then x else y else y) = if q ∧ p then x else y

   [r023]  Theorem

      |- (if p then x else if p then y else z) = if p then x else z

   [r024]  Theorem

      |- (if p then x else if q then x else y) = if p ∨ q then x else y

   [r025]  Theorem

      |- (if p then x else if q then x else y) = if q ∨ p then x else y

   [r026]  Theorem

      |- (if p then x = y else (x = z)) ⇔ (x = if p then y else z)

   [r027]  Theorem

      |- (if p then x = y else (y = z)) ⇔ (y = if p then x else z)

   [r028]  Theorem

      |- (if p then x = y else (z = y)) ⇔ (y = if p then x else z)

   [r029]  Theorem

      |- ¬p ⇒ q ⇔ p ∨ q

   [r030]  Theorem

      |- ¬p ⇒ q ⇔ q ∨ p

   [r031]  Theorem

      |- p ⇒ q ⇔ ¬p ∨ q

   [r032]  Theorem

      |- p ⇒ q ⇔ q ∨ ¬p

   [r033]  Theorem

      |- T ⇒ p ⇔ p

   [r034]  Theorem

      |- p ⇒ T ⇔ T

   [r035]  Theorem

      |- F ⇒ p ⇔ T

   [r036]  Theorem

      |- p ⇒ p ⇔ T

   [r037]  Theorem

      |- (p ⇔ q) ⇒ r ⇔ r ∨ (q ⇔ ¬p)

   [r038]  Theorem

      |- ¬T ⇔ F

   [r039]  Theorem

      |- ¬F ⇔ T

   [r040]  Theorem

      |- ¬ ¬p ⇔ p

   [r041]  Theorem

      |- p ∨ q ⇔ q ∨ p

   [r042]  Theorem

      |- p ∨ T ⇔ T

   [r043]  Theorem

      |- p ∨ ¬p ⇔ T

   [r044]  Theorem

      |- ¬p ∨ p ⇔ T

   [r045]  Theorem

      |- T ∨ p ⇔ T

   [r046]  Theorem

      |- p ∨ F ⇔ p

   [r047]  Theorem

      |- F ∨ p ⇔ p

   [r048]  Theorem

      |- p ∧ q ⇔ q ∧ p

   [r049]  Theorem

      |- p ∧ T ⇔ p

   [r050]  Theorem

      |- T ∧ p ⇔ p

   [r051]  Theorem

      |- p ∧ F ⇔ F

   [r052]  Theorem

      |- F ∧ p ⇔ F

   [r053]  Theorem

      |- p ∧ q ⇔ ¬(¬p ∨ ¬q)

   [r054]  Theorem

      |- ¬p ∧ q ⇔ ¬(p ∨ ¬q)

   [r055]  Theorem

      |- p ∧ ¬q ⇔ ¬(¬p ∨ q)

   [r056]  Theorem

      |- ¬p ∧ ¬q ⇔ ¬(p ∨ q)

   [r057]  Theorem

      |- p ∧ q ⇔ ¬(¬q ∨ ¬p)

   [r058]  Theorem

      |- ¬p ∧ q ⇔ ¬(¬q ∨ p)

   [r059]  Theorem

      |- p ∧ ¬q ⇔ ¬(q ∨ ¬p)

   [r060]  Theorem

      |- ¬p ∧ ¬q ⇔ ¬(q ∨ p)

   [r061]  Theorem

      |- (x =+ f x) f = f

   [r062]  Theorem

      |- ALL_DISTINCT [x; x] ⇔ F

   [r063]  Theorem

      |- ALL_DISTINCT [x; y] ⇔ x ≠ y

   [r064]  Theorem

      |- ALL_DISTINCT [x; y] ⇔ y ≠ x

   [r065]  Theorem

      |- (x = y) ⇔ (x + -1 * y = 0)

   [r066]  Theorem

      |- (x = y + z) ⇔ (x + -1 * z = y)

   [r067]  Theorem

      |- (x = y + -1 * z) ⇔ (x + (-1 * y + z) = 0)

   [r068]  Theorem

      |- (x = -1 * y + z) ⇔ (y + (-1 * z + x) = 0)

   [r069]  Theorem

      |- (x = y + z) ⇔ (x + (-1 * y + -1 * z) = 0)

   [r070]  Theorem

      |- (x = y + z) ⇔ (y + (z + -1 * x) = 0)

   [r071]  Theorem

      |- (x = y + z) ⇔ (y + (-1 * x + z) = 0)

   [r072]  Theorem

      |- (x = y + z) ⇔ (z + -1 * x = -y)

   [r073]  Theorem

      |- (x = -y + z) ⇔ (z + -1 * x = y)

   [r074]  Theorem

      |- (-1 * x = -y) ⇔ (x = y)

   [r075]  Theorem

      |- (-1 * x + y = z) ⇔ (x + -1 * y = -z)

   [r076]  Theorem

      |- (x + y = 0) ⇔ (y = -x)

   [r077]  Theorem

      |- (x + y = z) ⇔ (y + -1 * z = -x)

   [r078]  Theorem

      |- (a + (-1 * x + (v * y + w * z)) = 0) ⇔ (x + (-v * y + -w * z) = a)

   [r079]  Theorem

      |- 0 + x = x

   [r080]  Theorem

      |- x + 0 = x

   [r081]  Theorem

      |- x + y = y + x

   [r082]  Theorem

      |- x + x = 2 * x

   [r083]  Theorem

      |- x + y + z = x + (y + z)

   [r084]  Theorem

      |- x + y + z = x + (z + y)

   [r085]  Theorem

      |- x + (y + z) = y + (z + x)

   [r086]  Theorem

      |- x + (y + z) = y + (x + z)

   [r087]  Theorem

      |- x + (y + (z + u)) = y + (z + (u + x))

   [r088]  Theorem

      |- x ≥ x ⇔ T

   [r089]  Theorem

      |- x ≥ y ⇔ x + -1 * y ≥ 0

   [r090]  Theorem

      |- x ≥ y ⇔ y + -1 * x ≤ 0

   [r091]  Theorem

      |- x ≥ y + z ⇔ y + (z + -1 * x) ≤ 0

   [r092]  Theorem

      |- -1 * x ≥ 0 ⇔ x ≤ 0

   [r093]  Theorem

      |- -1 * x ≥ -y ⇔ x ≤ y

   [r094]  Theorem

      |- -1 * x + y ≥ 0 ⇔ x + -1 * y ≤ 0

   [r095]  Theorem

      |- x + -1 * y ≥ 0 ⇔ y ≤ x

   [r096]  Theorem

      |- x > y ⇔ ¬(y ≥ x)

   [r097]  Theorem

      |- x > y ⇔ ¬(x ≤ y)

   [r098]  Theorem

      |- x > y ⇔ ¬(x + -1 * y ≤ 0)

   [r099]  Theorem

      |- x > y ⇔ ¬(y + -1 * x ≥ 0)

   [r100]  Theorem

      |- x > y + z ⇔ ¬(z + -1 * x ≥ -y)

   [r101]  Theorem

      |- x ≤ x ⇔ T

   [r102]  Theorem

      |- 0 ≤ 1 ⇔ T

   [r103]  Theorem

      |- x ≤ y ⇔ y ≥ x

   [r104]  Theorem

      |- 0 ≤ -x + y ⇔ y ≥ x

   [r105]  Theorem

      |- -1 * x ≤ 0 ⇔ x ≥ 0

   [r106]  Theorem

      |- x ≤ y ⇔ x + -1 * y ≤ 0

   [r107]  Theorem

      |- x ≤ y ⇔ y + -1 * x ≥ 0

   [r108]  Theorem

      |- -1 * x + y ≤ 0 ⇔ x + -1 * y ≥ 0

   [r109]  Theorem

      |- -1 * x + y ≤ -z ⇔ x + -1 * y ≥ z

   [r110]  Theorem

      |- -x + y ≤ z ⇔ y + -1 * z ≤ x

   [r111]  Theorem

      |- x + -1 * y ≤ z ⇔ x + (-1 * y + -1 * z) ≤ 0

   [r112]  Theorem

      |- x ≤ y + z ⇔ x + -1 * z ≤ y

   [r113]  Theorem

      |- x ≤ y + z ⇔ z + -1 * x ≥ -y

   [r114]  Theorem

      |- x ≤ y + z ⇔ x + (-1 * y + -1 * z) ≤ 0

   [r115]  Theorem

      |- x < y ⇔ ¬(y ≤ x)

   [r116]  Theorem

      |- x < y ⇔ ¬(x ≥ y)

   [r117]  Theorem

      |- x < y ⇔ ¬(y + -1 * x ≤ 0)

   [r118]  Theorem

      |- x < y ⇔ ¬(x + -1 * y ≥ 0)

   [r119]  Theorem

      |- x < y + -1 * z ⇔ ¬(x + -1 * y + z ≥ 0)

   [r120]  Theorem

      |- x < y + -1 * z ⇔ ¬(x + (-1 * y + z) ≥ 0)

   [r121]  Theorem

      |- x < -y + z ⇔ ¬(z + -1 * x ≤ y)

   [r122]  Theorem

      |- x < -y + (z + u) ⇔ ¬(z + (u + -1 * x) ≤ y)

   [r123]  Theorem

      |- x < -y + (z + (u + v)) ⇔ ¬(z + (u + (v + -1 * x)) ≤ y)

   [r124]  Theorem

      |- -x + y < z ⇔ ¬(y + -1 * z ≥ x)

   [r125]  Theorem

      |- x + y < z ⇔ ¬(z + -1 * y ≤ x)

   [r126]  Theorem

      |- 0 < -x + y ⇔ ¬(y ≤ x)

   [r127]  Theorem

      |- x − 0 = x

   [r128]  Theorem

      |- 0 − x = -x

   [r129]  Theorem

      |- 0 − x = -1 * x

   [r130]  Theorem

      |- x − y = -y + x

   [r131]  Theorem

      |- x − y = x + -1 * y

   [r132]  Theorem

      |- x − y = -1 * y + x

   [r133]  Theorem

      |- x − 1 = -1 + x

   [r134]  Theorem

      |- x + y − z = x + (y + -1 * z)

   [r135]  Theorem

      |- x + y − z = x + (-1 * z + y)

   [r136]  Theorem

      |- (0 = -u * x) ⇔ (u * x = 0)

   [r137]  Theorem

      |- (a = -u * x) ⇔ (u * x = -a)

   [r138]  Theorem

      |- (a = x + (y + z)) ⇔ (x + (y + (-1 * a + z)) = 0)

   [r139]  Theorem

      |- (a = x + (y + z)) ⇔ (x + (y + (z + -1 * a)) = 0)

   [r140]  Theorem

      |- (a = -u * y + v * z) ⇔ (u * y + (-v * z + a) = 0)

   [r141]  Theorem

      |- (a = -u * y + -v * z) ⇔ (u * y + (a + v * z) = 0)

   [r142]  Theorem

      |- (-a = -u * x + v * y) ⇔ (u * x + -v * y = a)

   [r143]  Theorem

      |- (a = -u * x + (-v * y + w * z)) ⇔
         (u * x + (v * y + (-w * z + a)) = 0)

   [r144]  Theorem

      |- (a = -u * x + (v * y + w * z)) ⇔ (u * x + (-v * y + -w * z) = -a)

   [r145]  Theorem

      |- (a = -u * x + (v * y + -w * z)) ⇔ (u * x + (-v * y + w * z) = -a)

   [r146]  Theorem

      |- (a = -u * x + (-v * y + w * z)) ⇔ (u * x + (v * y + -w * z) = -a)

   [r147]  Theorem

      |- (a = -u * x + (-v * y + -w * z)) ⇔ (u * x + (v * y + w * z) = -a)

   [r148]  Theorem

      |- (-a = -u * x + (v * y + w * z)) ⇔ (u * x + (-v * y + -w * z) = a)

   [r149]  Theorem

      |- (-a = -u * x + (v * y + -w * z)) ⇔ (u * x + (-v * y + w * z) = a)

   [r150]  Theorem

      |- (-a = -u * x + (-v * y + w * z)) ⇔ (u * x + (v * y + -w * z) = a)

   [r151]  Theorem

      |- (-a = -u * x + (-v * y + -w * z)) ⇔ (u * x + (v * y + w * z) = a)

   [r152]  Theorem

      |- (a = -u * x + (-1 * y + w * z)) ⇔ (u * x + (y + -w * z) = -a)

   [r153]  Theorem

      |- (a = -u * x + (-1 * y + -w * z)) ⇔ (u * x + (y + w * z) = -a)

   [r154]  Theorem

      |- (-u * x + -v * y = -a) ⇔ (u * x + v * y = a)

   [r155]  Theorem

      |- (-1 * x + (-v * y + -w * z) = -a) ⇔ (x + (v * y + w * z) = a)

   [r156]  Theorem

      |- (-u * x + (v * y + w * z) = -a) ⇔ (u * x + (-v * y + -w * z) = a)

   [r157]  Theorem

      |- (-u * x + (-v * y + w * z) = -a) ⇔ (u * x + (v * y + -w * z) = a)

   [r158]  Theorem

      |- (-u * x + (-v * y + -w * z) = -a) ⇔ (u * x + (v * y + w * z) = a)

   [r159]  Theorem

      |- x + -1 * y ≥ 0 ⇔ y ≤ x

   [r160]  Theorem

      |- x ≥ y ⇔ x + -1 * y ≥ 0

   [r161]  Theorem

      |- x > y ⇔ ¬(x + -1 * y ≤ 0)

   [r162]  Theorem

      |- x ≤ y ⇔ x + -1 * y ≤ 0

   [r163]  Theorem

      |- x ≤ y + z ⇔ x + -1 * z ≤ y

   [r164]  Theorem

      |- -u * x ≤ a ⇔ u * x ≥ -a

   [r165]  Theorem

      |- -u * x ≤ -a ⇔ u * x ≥ a

   [r166]  Theorem

      |- -u * x + v * y ≤ 0 ⇔ u * x + -v * y ≥ 0

   [r167]  Theorem

      |- -u * x + v * y ≤ a ⇔ u * x + -v * y ≥ -a

   [r168]  Theorem

      |- -u * x + v * y ≤ -a ⇔ u * x + -v * y ≥ a

   [r169]  Theorem

      |- -u * x + -v * y ≤ a ⇔ u * x + v * y ≥ -a

   [r170]  Theorem

      |- -u * x + -v * y ≤ -a ⇔ u * x + v * y ≥ a

   [r171]  Theorem

      |- -u * x + (v * y + w * z) ≤ 0 ⇔ u * x + (-v * y + -w * z) ≥ 0

   [r172]  Theorem

      |- -u * x + (v * y + -w * z) ≤ 0 ⇔ u * x + (-v * y + w * z) ≥ 0

   [r173]  Theorem

      |- -u * x + (-v * y + w * z) ≤ 0 ⇔ u * x + (v * y + -w * z) ≥ 0

   [r174]  Theorem

      |- -u * x + (-v * y + -w * z) ≤ 0 ⇔ u * x + (v * y + w * z) ≥ 0

   [r175]  Theorem

      |- -u * x + (v * y + w * z) ≤ a ⇔ u * x + (-v * y + -w * z) ≥ -a

   [r176]  Theorem

      |- -u * x + (v * y + w * z) ≤ -a ⇔ u * x + (-v * y + -w * z) ≥ a

   [r177]  Theorem

      |- -u * x + (v * y + -w * z) ≤ a ⇔ u * x + (-v * y + w * z) ≥ -a

   [r178]  Theorem

      |- -u * x + (v * y + -w * z) ≤ -a ⇔ u * x + (-v * y + w * z) ≥ a

   [r179]  Theorem

      |- -u * x + (-v * y + w * z) ≤ a ⇔ u * x + (v * y + -w * z) ≥ -a

   [r180]  Theorem

      |- -u * x + (-v * y + w * z) ≤ -a ⇔ u * x + (v * y + -w * z) ≥ a

   [r181]  Theorem

      |- -u * x + (-v * y + -w * z) ≤ a ⇔ u * x + (v * y + w * z) ≥ -a

   [r182]  Theorem

      |- -u * x + (-v * y + -w * z) ≤ -a ⇔ u * x + (v * y + w * z) ≥ a

   [r183]  Theorem

      |- -1 * x + (v * y + w * z) ≤ -a ⇔ x + (-v * y + -w * z) ≥ a

   [r184]  Theorem

      |- x < y ⇔ ¬(x ≥ y)

   [r185]  Theorem

      |- -u * x < a ⇔ ¬(u * x ≤ -a)

   [r186]  Theorem

      |- -u * x < -a ⇔ ¬(u * x ≤ a)

   [r187]  Theorem

      |- -u * x + v * y < 0 ⇔ ¬(u * x + -v * y ≤ 0)

   [r188]  Theorem

      |- -u * x + -v * y < 0 ⇔ ¬(u * x + v * y ≤ 0)

   [r189]  Theorem

      |- -u * x + v * y < a ⇔ ¬(u * x + -v * y ≤ -a)

   [r190]  Theorem

      |- -u * x + v * y < -a ⇔ ¬(u * x + -v * y ≤ a)

   [r191]  Theorem

      |- -u * x + -v * y < a ⇔ ¬(u * x + v * y ≤ -a)

   [r192]  Theorem

      |- -u * x + -v * y < -a ⇔ ¬(u * x + v * y ≤ a)

   [r193]  Theorem

      |- -u * x + (v * y + w * z) < a ⇔ ¬(u * x + (-v * y + -w * z) ≤ -a)

   [r194]  Theorem

      |- -u * x + (v * y + w * z) < -a ⇔ ¬(u * x + (-v * y + -w * z) ≤ a)

   [r195]  Theorem

      |- -u * x + (v * y + -w * z) < a ⇔ ¬(u * x + (-v * y + w * z) ≤ -a)

   [r196]  Theorem

      |- -u * x + (v * y + -w * z) < -a ⇔ ¬(u * x + (-v * y + w * z) ≤ a)

   [r197]  Theorem

      |- -u * x + (-v * y + w * z) < a ⇔ ¬(u * x + (v * y + -w * z) ≤ -a)

   [r198]  Theorem

      |- -u * x + (-v * y + w * z) < -a ⇔ ¬(u * x + (v * y + -w * z) ≤ a)

   [r199]  Theorem

      |- -u * x + (-v * y + -w * z) < a ⇔ ¬(u * x + (v * y + w * z) ≤ -a)

   [r200]  Theorem

      |- -u * x + (-v * y + -w * z) < -a ⇔ ¬(u * x + (v * y + w * z) ≤ a)

   [r201]  Theorem

      |- -u * x + (-v * y + w * z) < 0 ⇔ ¬(u * x + (v * y + -w * z) ≤ 0)

   [r202]  Theorem

      |- -u * x + (-v * y + -w * z) < 0 ⇔ ¬(u * x + (v * y + w * z) ≤ 0)

   [r203]  Theorem

      |- -1 * x + (v * y + w * z) < a ⇔ ¬(x + (-v * y + -w * z) ≤ -a)

   [r204]  Theorem

      |- -1 * x + (v * y + w * z) < -a ⇔ ¬(x + (-v * y + -w * z) ≤ a)

   [r205]  Theorem

      |- -1 * x + (v * y + -w * z) < a ⇔ ¬(x + (-v * y + w * z) ≤ -a)

   [r206]  Theorem

      |- -1 * x + (v * y + -w * z) < -a ⇔ ¬(x + (-v * y + w * z) ≤ a)

   [r207]  Theorem

      |- -1 * x + (-v * y + w * z) < a ⇔ ¬(x + (v * y + -w * z) ≤ -a)

   [r208]  Theorem

      |- -1 * x + (-v * y + w * z) < -a ⇔ ¬(x + (v * y + -w * z) ≤ a)

   [r209]  Theorem

      |- -1 * x + (-v * y + -w * z) < a ⇔ ¬(x + (v * y + w * z) ≤ -a)

   [r210]  Theorem

      |- -1 * x + (-v * y + -w * z) < -a ⇔ ¬(x + (v * y + w * z) ≤ a)

   [r211]  Theorem

      |- -u * x + (-1 * y + -w * z) < -a ⇔ ¬(u * x + (y + w * z) ≤ a)

   [r212]  Theorem

      |- -u * x + (v * y + -1 * z) < -a ⇔ ¬(u * x + (-v * y + z) ≤ a)

   [r213]  Theorem

      |- 0 + x = x

   [r214]  Theorem

      |- x + 0 = x

   [r215]  Theorem

      |- x + y = y + x

   [r216]  Theorem

      |- x + x = 2 * x

   [r217]  Theorem

      |- x + y + z = x + (y + z)

   [r218]  Theorem

      |- x + y + z = x + (z + y)

   [r219]  Theorem

      |- x + (y + z) = y + (z + x)

   [r220]  Theorem

      |- x + (y + z) = y + (x + z)

   [r221]  Theorem

      |- 0 − x = -x

   [r222]  Theorem

      |- 0 − u * x = -u * x

   [r223]  Theorem

      |- x − 0 = x

   [r224]  Theorem

      |- x − y = x + -1 * y

   [r225]  Theorem

      |- x − y = -1 * y + x

   [r226]  Theorem

      |- x − u * y = x + -u * y

   [r227]  Theorem

      |- x − u * y = -u * y + x

   [r228]  Theorem

      |- x + y − z = x + (y + -1 * z)

   [r229]  Theorem

      |- x + y − z = x + (-1 * z + y)

   [r230]  Theorem

      |- x + y − u * z = -u * z + (x + y)

   [r231]  Theorem

      |- x + y − u * z = x + (-u * z + y)

   [r232]  Theorem

      |- x + y − u * z = x + (y + -u * z)

   [r233]  Theorem

      |- 0 * x = 0

   [r234]  Theorem

      |- 1 * x = x

   [r235]  Theorem

      |- 0w + x = x

   [r236]  Theorem

      |- x + y = y + x

   [r237]  Theorem

      |- 1w + (1w + x) = 2w + x

   [r238]  Theorem

      |- (x + z = y + x) ⇔ (y = z)

   [r239]  Theorem

      [oracles: DISK_THM] [axioms: ] [FINITE 𝕌(:α), x < dimword (:β)]
      |- 0w @@ n2w x = n2w x

   [r240]  Theorem

      [oracles: DISK_THM] [axioms: ] [x < dimword (:α)]
      |- w2w (n2w x) = n2w x

   [r241]  Theorem

      [oracles: DISK_THM] [axioms: ]
      [FINITE 𝕌(:α), y < dimword (:β), dimindex (:β) ≤ dimindex (:γ)]
      |- (0w @@ x = n2w y) ⇔ (x = n2w y)

   [r242]  Theorem

      [oracles: DISK_THM] [axioms: ]
      [FINITE 𝕌(:α), y < dimword (:β), dimindex (:β) ≤ dimindex (:γ)]
      |- (0w @@ x = n2w y) ⇔ (n2w y = x)

   [r243]  Theorem

      [oracles: DISK_THM] [axioms: ]
      [FINITE 𝕌(:α), y < dimword (:β), dimindex (:β) ≤ dimindex (:γ)]
      |- (n2w y = 0w @@ x) ⇔ (x = n2w y)

   [r244]  Theorem

      [oracles: DISK_THM] [axioms: ]
      [FINITE 𝕌(:α), y < dimword (:β), dimindex (:β) ≤ dimindex (:γ)]
      |- (n2w y = 0w @@ x) ⇔ (n2w y = x)

   [r245]  Theorem

      |- x && y = y && x

   [r246]  Theorem

      |- x && y && z = y && x && z

   [r247]  Theorem

      |- x && y && z = (x && y) && z

   [r248]  Theorem

      |- (1w = x && y) ⇔ (1w = x) ∧ (1w = y)

   [r249]  Theorem

      |- (1w = x && y) ⇔ (1w = y) ∧ (1w = x)

   [r250]  Theorem

      |- (7 >< 0) x = x

   [r251]  Theorem

      |- x <₊ y ⇔ ¬(y ≤₊ x)

   [r252]  Theorem

      |- x * y = y * x

   [r253]  Theorem

      |- (0 >< 0) x = x

   [r254]  Theorem

      |- (x && y) && z = x && y && z

   [r255]  Theorem

      |- 0w ‖ x = x

   [t001]  Theorem

      |- (x = y) ∨ (f x = (y =+ z) f x)

   [t002]  Theorem

      |- (x = y) ∨ (f y = (x =+ z) f y)

   [t003]  Theorem

      |- (x = y) ∨ ((y =+ z) f x = f x)

   [t004]  Theorem

      |- (x = y) ∨ ((x =+ z) f y = f y)

   [t005]  Theorem

      |- (f = g) ∨ f (array_ext f g) ≠ g (array_ext f g)

   [t006]  Theorem

      |- x ≠ y ∨ x ≤ y

   [t007]  Theorem

      |- x ≠ y ∨ x ≥ y

   [t008]  Theorem

      |- x ≠ y ∨ x + -1 * y ≥ 0

   [t009]  Theorem

      |- x ≠ y ∨ x + -1 * y ≤ 0

   [t010]  Theorem

      |- (x = y) ∨ ¬(x ≤ y) ∨ ¬(x ≥ y)

   [t011]  Theorem

      |- ¬(x ≤ 0) ∨ x ≤ 1

   [t012]  Theorem

      |- ¬(x ≤ -1) ∨ x ≤ 0

   [t013]  Theorem

      |- ¬(x ≥ 0) ∨ x ≥ -1

   [t014]  Theorem

      |- ¬(x ≥ 0) ∨ ¬(x ≤ -1)

   [t015]  Theorem

      |- x ≥ y ∨ x ≤ y

   [t016]  Theorem

      |- x ≠ y ∨ x + -1 * y ≥ 0

   [t017]  Theorem

      |- x ≠ ¬x

   [t018]  Theorem

      |- (x = y) ⇒ x ' i ⇒ y ' i

   [t019]  Theorem

      |- (1w = ¬x) ∨ x ' 0

   [t020]  Theorem

      |- x ' 0 ⇒ (0w = ¬x)

   [t021]  Theorem

      |- x ' 0 ⇒ (1w = x)

   [t022]  Theorem

      |- ¬x ' 0 ⇒ (0w = x)

   [t023]  Theorem

      |- ¬x ' 0 ⇒ (1w = ¬x)

   [t024]  Theorem

      |- (0w = ¬x) ∨ ¬x ' 0

   [t025]  Theorem

      |- (1w = ¬x ‖ ¬y) ∨ ¬(¬x ' 0 ∨ ¬y ' 0)

   [t026]  Theorem

      |- (0w = x) ∨ x ' 0 ∨ x ' 1 ∨ x ' 2 ∨ x ' 3 ∨ x ' 4 ∨ x ' 5 ∨ x ' 6 ∨
         x ' 7

   [t027]  Theorem

      |- ((x = 1w) ⇔ p) ⇔ (x = if p then 1w else 0w)

   [t028]  Theorem

      |- ((1w = x) ⇔ p) ⇔ (x = if p then 1w else 0w)

   [t029]  Theorem

      |- (p ⇔ (x = 1w)) ⇔ (x = if p then 1w else 0w)

   [t030]  Theorem

      |- (p ⇔ (1w = x)) ⇔ (x = if p then 1w else 0w)

   [t031]  Theorem

      |- (0w = 0xFFFFFFFFw * sw2sw x) ⇒ ¬x ' 0

   [t032]  Theorem

      |- (0w = 0xFFFFFFFFw * sw2sw x) ⇒ (x ' 1 ⇎ ¬x ' 0)

   [t033]  Theorem

      |- (0w = 0xFFFFFFFFw * sw2sw x) ⇒ (x ' 2 ⇎ ¬x ' 0 ∧ ¬x ' 1)

   [t034]  Theorem

      |- (1w + x = y) ⇒ x ' 0 ⇒ ¬y ' 0

   [t035]  Theorem

      |- (1w = x) ∨ (0 >< 0) x ≠ 1w


*)
end
