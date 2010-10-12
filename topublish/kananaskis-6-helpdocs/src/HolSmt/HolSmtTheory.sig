signature HolSmtTheory =
sig
  type thm = Thm.thm
  
  (*  Definitions  *)
    val carry_def : thm
    val xor3_def : thm
    val xor_def : thm
  
  (*  Theorems  *)
    val ALL_DISTINCT_CONS : thm
    val ALL_DISTINCT_NIL : thm
    val AND_T : thm
    val CONJ_CONG : thm
    val DISJ_ELIM_1 : thm
    val DISJ_ELIM_2 : thm
    val F_OR : thm
    val IMP_DISJ_1 : thm
    val IMP_DISJ_2 : thm
    val IMP_FALSE : thm
    val NEG_IFF_1 : thm
    val NEG_IFF_2 : thm
    val NNF_CONJ : thm
    val NNF_DISJ : thm
    val NNF_NOT_NOT : thm
    val NOT_FALSE : thm
    val NOT_MEM_CONS : thm
    val NOT_MEM_CONS_SWAP : thm
    val NOT_MEM_NIL : thm
    val NOT_NOT_ELIM : thm
    val T_AND : thm
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
    val d029 : thm
    val d030 : thm
    val d031 : thm
    val d032 : thm
    val d033 : thm
    val d034 : thm
    val d035 : thm
    val d036 : thm
    val d037 : thm
    val d038 : thm
    val d039 : thm
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
  
  val HolSmt_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [Omega] Parent theory of "HolSmt"
   
   [blast] Parent theory of "HolSmt"
   
   [int_arith] Parent theory of "HolSmt"
   
   [poly] Parent theory of "HolSmt"
   
   [transc] Parent theory of "HolSmt"
   
   [carry_def]  Definition
      
      |- ∀x y z. carry x y z ⇔ x ∧ y ∨ x ∧ z ∨ y ∧ z
   
   [xor3_def]  Definition
      
      |- ∀x y z. xor3 x y z ⇔ xor (xor x y) z
   
   [xor_def]  Definition
      
      |- ∀x y. xor x y ⇔ (x ⇎ y)
   
   [ALL_DISTINCT_CONS]  Theorem
      
      |- ∀h t. ALL_DISTINCT (h::t) ⇔ ¬MEM h t ∧ ALL_DISTINCT t
   
   [ALL_DISTINCT_NIL]  Theorem
      
      |- ALL_DISTINCT [] ⇔ T
   
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
   
   [NEG_IFF_1]  Theorem
      
      |- ∀p q. (p ⇔ q) ⇒ (q ⇎ ¬p)
   
   [NEG_IFF_2]  Theorem
      
      |- ∀p q. (p ⇎ ¬q) ⇒ (q ⇔ p)
   
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
   
   [NOT_MEM_CONS_SWAP]  Theorem
      
      |- ∀x h t. ¬MEM x (h::t) ⇔ h ≠ x ∧ ¬MEM x t
   
   [NOT_MEM_NIL]  Theorem
      
      |- ∀x. ¬MEM x [] ⇔ T
   
   [NOT_NOT_ELIM]  Theorem
      
      |- ∀p. ¬ ¬p ⇒ p
   
   [T_AND]  Theorem
      
      |- ∀p q. (T ∧ p ⇔ T ∧ q) ⇒ (p ⇔ q)
   
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
      
      |- p ∨ q ∨ (p ⇎ ¬q)
   
   [d012]  Theorem
      
      |- ¬p ∧ ¬q ∨ p ∨ q
   
   [d013]  Theorem
      
      |- ¬p ∧ q ∨ p ∨ ¬q
   
   [d014]  Theorem
      
      |- p ∧ ¬q ∨ ¬p ∨ q
   
   [d015]  Theorem
      
      |- p ∧ q ∨ ¬p ∨ ¬q
   
   [d016]  Theorem
      
      |- ¬xor3 p q r ∨ ¬p ∨ ¬q ∨ r
   
   [d017]  Theorem
      
      |- ¬xor3 p q r ∨ ¬p ∨ q ∨ ¬r
   
   [d018]  Theorem
      
      |- ¬xor3 p q r ∨ p ∨ ¬q ∨ ¬r
   
   [d019]  Theorem
      
      |- ¬xor3 p q r ∨ p ∨ q ∨ r
   
   [d020]  Theorem
      
      |- xor3 p q r ∨ ¬p ∨ ¬q ∨ ¬r
   
   [d021]  Theorem
      
      |- xor3 p q r ∨ ¬p ∨ q ∨ r
   
   [d022]  Theorem
      
      |- xor3 p q r ∨ p ∨ ¬q ∨ r
   
   [d023]  Theorem
      
      |- xor3 p q r ∨ p ∨ q ∨ ¬r
   
   [d024]  Theorem
      
      |- ¬carry p q r ∨ p ∨ q
   
   [d025]  Theorem
      
      |- ¬carry p q r ∨ p ∨ r
   
   [d026]  Theorem
      
      |- ¬carry p q r ∨ q ∨ r
   
   [d027]  Theorem
      
      |- carry p q r ∨ ¬p ∨ ¬q
   
   [d028]  Theorem
      
      |- carry p q r ∨ ¬p ∨ ¬r
   
   [d029]  Theorem
      
      |- carry p q r ∨ ¬q ∨ ¬r
   
   [d030]  Theorem
      
      |- p ∨ (x = if p then y else x)
   
   [d031]  Theorem
      
      |- ¬p ∨ (x = if p then x else y)
   
   [d032]  Theorem
      
      |- p ∨ ((if p then x else y) = y)
   
   [d033]  Theorem
      
      |- ¬p ∨ ((if p then x else y) = x)
   
   [d034]  Theorem
      
      |- p ∨ q ∨ ¬if p then r else q
   
   [d035]  Theorem
      
      |- ¬p ∨ q ∨ ¬if p then q else r
   
   [d036]  Theorem
      
      |- (if p then q else r) ∨ ¬p ∨ ¬q
   
   [d037]  Theorem
      
      |- (if p then q else r) ∨ p ∨ ¬r
   
   [d038]  Theorem
      
      |- ¬(if p then q else r) ∨ ¬p ∨ q
   
   [d039]  Theorem
      
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
      
      |- (p ⇔ F) ⇔ ¬p
   
   [r005]  Theorem
      
      |- (¬p ⇔ ¬q) ⇔ (p ⇔ q)
   
   [r006]  Theorem
      
      |- (if ¬p then x else y) = if p then y else x
   
   [r007]  Theorem
      
      |- (if p then if q then x else y else x) = if p ∧ ¬q then y else x
   
   [r008]  Theorem
      
      |- (if p then if q then x else y else y) = if p ∧ q then x else y
   
   [r009]  Theorem
      
      |- (if p then if q then x else y else y) = if q ∧ p then x else y
   
   [r010]  Theorem
      
      |- (if p then x else if q then x else y) ⇔ if p ∨ q then x else y
   
   [r011]  Theorem
      
      |- (if p then x else if q then x else y) ⇔ if q ∨ p then x else y
   
   [r012]  Theorem
      
      |- (if p then x = y else (x = z)) ⇔ (x = if p then y else z)
   
   [r013]  Theorem
      
      |- (if p then x = y else (y = z)) ⇔ (y = if p then x else z)
   
   [r014]  Theorem
      
      |- (if p then x = y else (z = y)) ⇔ (y = if p then x else z)
   
   [r015]  Theorem
      
      |- ¬p ⇒ q ⇔ p ∨ q
   
   [r016]  Theorem
      
      |- ¬p ⇒ q ⇔ q ∨ p
   
   [r017]  Theorem
      
      |- p ⇒ q ⇔ ¬p ∨ q
   
   [r018]  Theorem
      
      |- p ⇒ q ⇔ q ∨ ¬p
   
   [r019]  Theorem
      
      |- T ⇒ p ⇔ p
   
   [r020]  Theorem
      
      |- p ⇒ T ⇔ T
   
   [r021]  Theorem
      
      |- F ⇒ p ⇔ T
   
   [r022]  Theorem
      
      |- p ⇒ p ⇔ T
   
   [r023]  Theorem
      
      |- (p ⇔ q) ⇒ r ⇔ r ∨ (q ⇔ ¬p)
   
   [r024]  Theorem
      
      |- ¬T ⇔ F
   
   [r025]  Theorem
      
      |- ¬F ⇔ T
   
   [r026]  Theorem
      
      |- ¬ ¬p ⇔ p
   
   [r027]  Theorem
      
      |- p ∨ q ⇔ q ∨ p
   
   [r028]  Theorem
      
      |- p ∨ T ⇔ T
   
   [r029]  Theorem
      
      |- p ∨ ¬p ⇔ T
   
   [r030]  Theorem
      
      |- ¬p ∨ p ⇔ T
   
   [r031]  Theorem
      
      |- T ∨ p ⇔ T
   
   [r032]  Theorem
      
      |- p ∨ F ⇔ p
   
   [r033]  Theorem
      
      |- F ∨ p ⇔ p
   
   [r034]  Theorem
      
      |- p ∧ q ⇔ q ∧ p
   
   [r035]  Theorem
      
      |- p ∧ T ⇔ p
   
   [r036]  Theorem
      
      |- T ∧ p ⇔ p
   
   [r037]  Theorem
      
      |- p ∧ F ⇔ F
   
   [r038]  Theorem
      
      |- F ∧ p ⇔ F
   
   [r039]  Theorem
      
      |- p ∧ q ⇔ ¬(¬p ∨ ¬q)
   
   [r040]  Theorem
      
      |- ¬p ∧ q ⇔ ¬(p ∨ ¬q)
   
   [r041]  Theorem
      
      |- p ∧ ¬q ⇔ ¬(¬p ∨ q)
   
   [r042]  Theorem
      
      |- ¬p ∧ ¬q ⇔ ¬(p ∨ q)
   
   [r043]  Theorem
      
      |- p ∧ q ⇔ ¬(¬q ∨ ¬p)
   
   [r044]  Theorem
      
      |- ¬p ∧ q ⇔ ¬(¬q ∨ p)
   
   [r045]  Theorem
      
      |- p ∧ ¬q ⇔ ¬(q ∨ ¬p)
   
   [r046]  Theorem
      
      |- ¬p ∧ ¬q ⇔ ¬(q ∨ p)
   
   [r047]  Theorem
      
      |- ALL_DISTINCT [x; x] ⇔ F
   
   [r048]  Theorem
      
      |- ALL_DISTINCT [x; y] ⇔ x ≠ y
   
   [r049]  Theorem
      
      |- ALL_DISTINCT [x; y] ⇔ y ≠ x
   
   [r050]  Theorem
      
      |- (x = y) ⇔ (x + -1 * y = 0)
   
   [r051]  Theorem
      
      |- (x = y + z) ⇔ (x + -1 * z = y)
   
   [r052]  Theorem
      
      |- (x = y + -1 * z) ⇔ (x + (-1 * y + z) = 0)
   
   [r053]  Theorem
      
      |- (x = -1 * y + z) ⇔ (y + (-1 * z + x) = 0)
   
   [r054]  Theorem
      
      |- (x = y + z) ⇔ (x + (-1 * y + -1 * z) = 0)
   
   [r055]  Theorem
      
      |- (x = y + z) ⇔ (y + (z + -1 * x) = 0)
   
   [r056]  Theorem
      
      |- (x = y + z) ⇔ (y + (-1 * x + z) = 0)
   
   [r057]  Theorem
      
      |- (x = y + z) ⇔ (z + -1 * x = -y)
   
   [r058]  Theorem
      
      |- (x = -y + z) ⇔ (z + -1 * x = y)
   
   [r059]  Theorem
      
      |- (-1 * x = -y) ⇔ (x = y)
   
   [r060]  Theorem
      
      |- (-1 * x + y = z) ⇔ (x + -1 * y = -z)
   
   [r061]  Theorem
      
      |- (x + y = 0) ⇔ (y = -x)
   
   [r062]  Theorem
      
      |- (x + y = z) ⇔ (y + -1 * z = -x)
   
   [r063]  Theorem
      
      |- (a + (-1 * x + (v * y + w * z)) = 0) ⇔ (x + (-v * y + -w * z) = a)
   
   [r064]  Theorem
      
      |- 0 + x = x
   
   [r065]  Theorem
      
      |- x + 0 = x
   
   [r066]  Theorem
      
      |- x + y = y + x
   
   [r067]  Theorem
      
      |- x + x = 2 * x
   
   [r068]  Theorem
      
      |- x + y + z = x + (y + z)
   
   [r069]  Theorem
      
      |- x + y + z = x + (z + y)
   
   [r070]  Theorem
      
      |- x + (y + z) = y + (z + x)
   
   [r071]  Theorem
      
      |- x + (y + z) = y + (x + z)
   
   [r072]  Theorem
      
      |- x + (y + (z + u)) = y + (z + (u + x))
   
   [r073]  Theorem
      
      |- x ≥ x ⇔ T
   
   [r074]  Theorem
      
      |- x ≥ y ⇔ x + -1 * y ≥ 0
   
   [r075]  Theorem
      
      |- x ≥ y ⇔ y + -1 * x ≤ 0
   
   [r076]  Theorem
      
      |- x ≥ y + z ⇔ y + (z + -1 * x) ≤ 0
   
   [r077]  Theorem
      
      |- -1 * x ≥ 0 ⇔ x ≤ 0
   
   [r078]  Theorem
      
      |- -1 * x ≥ -y ⇔ x ≤ y
   
   [r079]  Theorem
      
      |- -1 * x + y ≥ 0 ⇔ x + -1 * y ≤ 0
   
   [r080]  Theorem
      
      |- x + -1 * y ≥ 0 ⇔ y ≤ x
   
   [r081]  Theorem
      
      |- x > y ⇔ ¬(y ≥ x)
   
   [r082]  Theorem
      
      |- x > y ⇔ ¬(x ≤ y)
   
   [r083]  Theorem
      
      |- x > y ⇔ ¬(x + -1 * y ≤ 0)
   
   [r084]  Theorem
      
      |- x > y ⇔ ¬(y + -1 * x ≥ 0)
   
   [r085]  Theorem
      
      |- x > y + z ⇔ ¬(z + -1 * x ≥ -y)
   
   [r086]  Theorem
      
      |- x ≤ x ⇔ T
   
   [r087]  Theorem
      
      |- 0 ≤ 1 ⇔ T
   
   [r088]  Theorem
      
      |- x ≤ y ⇔ y ≥ x
   
   [r089]  Theorem
      
      |- 0 ≤ -x + y ⇔ y ≥ x
   
   [r090]  Theorem
      
      |- -1 * x ≤ 0 ⇔ x ≥ 0
   
   [r091]  Theorem
      
      |- x ≤ y ⇔ x + -1 * y ≤ 0
   
   [r092]  Theorem
      
      |- x ≤ y ⇔ y + -1 * x ≥ 0
   
   [r093]  Theorem
      
      |- -1 * x + y ≤ 0 ⇔ x + -1 * y ≥ 0
   
   [r094]  Theorem
      
      |- -1 * x + y ≤ -z ⇔ x + -1 * y ≥ z
   
   [r095]  Theorem
      
      |- -x + y ≤ z ⇔ y + -1 * z ≤ x
   
   [r096]  Theorem
      
      |- x + -1 * y ≤ z ⇔ x + (-1 * y + -1 * z) ≤ 0
   
   [r097]  Theorem
      
      |- x ≤ y + z ⇔ x + -1 * z ≤ y
   
   [r098]  Theorem
      
      |- x ≤ y + z ⇔ z + -1 * x ≥ -y
   
   [r099]  Theorem
      
      |- x ≤ y + z ⇔ x + (-1 * y + -1 * z) ≤ 0
   
   [r100]  Theorem
      
      |- x < y ⇔ ¬(y ≤ x)
   
   [r101]  Theorem
      
      |- x < y ⇔ ¬(x ≥ y)
   
   [r102]  Theorem
      
      |- x < y ⇔ ¬(y + -1 * x ≤ 0)
   
   [r103]  Theorem
      
      |- x < y ⇔ ¬(x + -1 * y ≥ 0)
   
   [r104]  Theorem
      
      |- x < y + -1 * z ⇔ ¬(x + -1 * y + z ≥ 0)
   
   [r105]  Theorem
      
      |- x < y + -1 * z ⇔ ¬(x + (-1 * y + z) ≥ 0)
   
   [r106]  Theorem
      
      |- x < -y + z ⇔ ¬(z + -1 * x ≤ y)
   
   [r107]  Theorem
      
      |- x < -y + (z + u) ⇔ ¬(z + (u + -1 * x) ≤ y)
   
   [r108]  Theorem
      
      |- x < -y + (z + (u + v)) ⇔ ¬(z + (u + (v + -1 * x)) ≤ y)
   
   [r109]  Theorem
      
      |- -x + y < z ⇔ ¬(y + -1 * z ≥ x)
   
   [r110]  Theorem
      
      |- x + y < z ⇔ ¬(z + -1 * y ≤ x)
   
   [r111]  Theorem
      
      |- 0 < -x + y ⇔ ¬(y ≤ x)
   
   [r112]  Theorem
      
      |- x − 0 = x
   
   [r113]  Theorem
      
      |- 0 − x = -x
   
   [r114]  Theorem
      
      |- 0 − x = -1 * x
   
   [r115]  Theorem
      
      |- x − y = -y + x
   
   [r116]  Theorem
      
      |- x − y = x + -1 * y
   
   [r117]  Theorem
      
      |- x − y = -1 * y + x
   
   [r118]  Theorem
      
      |- x − 1 = -1 + x
   
   [r119]  Theorem
      
      |- x + y − z = x + (y + -1 * z)
   
   [r120]  Theorem
      
      |- x + y − z = x + (-1 * z + y)
   
   [r121]  Theorem
      
      |- (0 = -u * x) ⇔ (u * x = 0)
   
   [r122]  Theorem
      
      |- (a = -u * x) ⇔ (u * x = -a)
   
   [r123]  Theorem
      
      |- (a = x + (y + z)) ⇔ (x + (y + (-1 * a + z)) = 0)
   
   [r124]  Theorem
      
      |- (a = x + (y + z)) ⇔ (x + (y + (z + -1 * a)) = 0)
   
   [r125]  Theorem
      
      |- (a = -u * y + v * z) ⇔ (u * y + (-v * z + a) = 0)
   
   [r126]  Theorem
      
      |- (a = -u * y + -v * z) ⇔ (u * y + (a + v * z) = 0)
   
   [r127]  Theorem
      
      |- (-a = -u * x + v * y) ⇔ (u * x + -v * y = a)
   
   [r128]  Theorem
      
      |- (a = -u * x + (-v * y + w * z)) ⇔ (u * x + (v * y + (-w * z + a)) = 0)
   
   [r129]  Theorem
      
      |- (a = -u * x + (v * y + w * z)) ⇔ (u * x + (-v * y + -w * z) = -a)
   
   [r130]  Theorem
      
      |- (a = -u * x + (v * y + -w * z)) ⇔ (u * x + (-v * y + w * z) = -a)
   
   [r131]  Theorem
      
      |- (a = -u * x + (-v * y + w * z)) ⇔ (u * x + (v * y + -w * z) = -a)
   
   [r132]  Theorem
      
      |- (a = -u * x + (-v * y + -w * z)) ⇔ (u * x + (v * y + w * z) = -a)
   
   [r133]  Theorem
      
      |- (-a = -u * x + (v * y + w * z)) ⇔ (u * x + (-v * y + -w * z) = a)
   
   [r134]  Theorem
      
      |- (-a = -u * x + (v * y + -w * z)) ⇔ (u * x + (-v * y + w * z) = a)
   
   [r135]  Theorem
      
      |- (-a = -u * x + (-v * y + w * z)) ⇔ (u * x + (v * y + -w * z) = a)
   
   [r136]  Theorem
      
      |- (-a = -u * x + (-v * y + -w * z)) ⇔ (u * x + (v * y + w * z) = a)
   
   [r137]  Theorem
      
      |- (a = -u * x + (-1 * y + w * z)) ⇔ (u * x + (y + -w * z) = -a)
   
   [r138]  Theorem
      
      |- (a = -u * x + (-1 * y + -w * z)) ⇔ (u * x + (y + w * z) = -a)
   
   [r139]  Theorem
      
      |- (-u * x + -v * y = -a) ⇔ (u * x + v * y = a)
   
   [r140]  Theorem
      
      |- (-1 * x + (-v * y + -w * z) = -a) ⇔ (x + (v * y + w * z) = a)
   
   [r141]  Theorem
      
      |- (-u * x + (v * y + w * z) = -a) ⇔ (u * x + (-v * y + -w * z) = a)
   
   [r142]  Theorem
      
      |- (-u * x + (-v * y + w * z) = -a) ⇔ (u * x + (v * y + -w * z) = a)
   
   [r143]  Theorem
      
      |- (-u * x + (-v * y + -w * z) = -a) ⇔ (u * x + (v * y + w * z) = a)
   
   [r144]  Theorem
      
      |- x + -1 * y ≥ 0 ⇔ y ≤ x
   
   [r145]  Theorem
      
      |- x ≥ y ⇔ x + -1 * y ≥ 0
   
   [r146]  Theorem
      
      |- x > y ⇔ ¬(x + -1 * y ≤ 0)
   
   [r147]  Theorem
      
      |- x ≤ y ⇔ x + -1 * y ≤ 0
   
   [r148]  Theorem
      
      |- x ≤ y + z ⇔ x + -1 * z ≤ y
   
   [r149]  Theorem
      
      |- -u * x ≤ a ⇔ u * x ≥ -a
   
   [r150]  Theorem
      
      |- -u * x ≤ -a ⇔ u * x ≥ a
   
   [r151]  Theorem
      
      |- -u * x + v * y ≤ 0 ⇔ u * x + -v * y ≥ 0
   
   [r152]  Theorem
      
      |- -u * x + v * y ≤ a ⇔ u * x + -v * y ≥ -a
   
   [r153]  Theorem
      
      |- -u * x + v * y ≤ -a ⇔ u * x + -v * y ≥ a
   
   [r154]  Theorem
      
      |- -u * x + -v * y ≤ a ⇔ u * x + v * y ≥ -a
   
   [r155]  Theorem
      
      |- -u * x + -v * y ≤ -a ⇔ u * x + v * y ≥ a
   
   [r156]  Theorem
      
      |- -u * x + (v * y + w * z) ≤ 0 ⇔ u * x + (-v * y + -w * z) ≥ 0
   
   [r157]  Theorem
      
      |- -u * x + (v * y + -w * z) ≤ 0 ⇔ u * x + (-v * y + w * z) ≥ 0
   
   [r158]  Theorem
      
      |- -u * x + (-v * y + w * z) ≤ 0 ⇔ u * x + (v * y + -w * z) ≥ 0
   
   [r159]  Theorem
      
      |- -u * x + (-v * y + -w * z) ≤ 0 ⇔ u * x + (v * y + w * z) ≥ 0
   
   [r160]  Theorem
      
      |- -u * x + (v * y + w * z) ≤ a ⇔ u * x + (-v * y + -w * z) ≥ -a
   
   [r161]  Theorem
      
      |- -u * x + (v * y + w * z) ≤ -a ⇔ u * x + (-v * y + -w * z) ≥ a
   
   [r162]  Theorem
      
      |- -u * x + (v * y + -w * z) ≤ a ⇔ u * x + (-v * y + w * z) ≥ -a
   
   [r163]  Theorem
      
      |- -u * x + (v * y + -w * z) ≤ -a ⇔ u * x + (-v * y + w * z) ≥ a
   
   [r164]  Theorem
      
      |- -u * x + (-v * y + w * z) ≤ a ⇔ u * x + (v * y + -w * z) ≥ -a
   
   [r165]  Theorem
      
      |- -u * x + (-v * y + w * z) ≤ -a ⇔ u * x + (v * y + -w * z) ≥ a
   
   [r166]  Theorem
      
      |- -u * x + (-v * y + -w * z) ≤ a ⇔ u * x + (v * y + w * z) ≥ -a
   
   [r167]  Theorem
      
      |- -u * x + (-v * y + -w * z) ≤ -a ⇔ u * x + (v * y + w * z) ≥ a
   
   [r168]  Theorem
      
      |- -1 * x + (v * y + w * z) ≤ -a ⇔ x + (-v * y + -w * z) ≥ a
   
   [r169]  Theorem
      
      |- x < y ⇔ ¬(x ≥ y)
   
   [r170]  Theorem
      
      |- -u * x < a ⇔ ¬(u * x ≤ -a)
   
   [r171]  Theorem
      
      |- -u * x < -a ⇔ ¬(u * x ≤ a)
   
   [r172]  Theorem
      
      |- -u * x + v * y < 0 ⇔ ¬(u * x + -v * y ≤ 0)
   
   [r173]  Theorem
      
      |- -u * x + -v * y < 0 ⇔ ¬(u * x + v * y ≤ 0)
   
   [r174]  Theorem
      
      |- -u * x + v * y < a ⇔ ¬(u * x + -v * y ≤ -a)
   
   [r175]  Theorem
      
      |- -u * x + v * y < -a ⇔ ¬(u * x + -v * y ≤ a)
   
   [r176]  Theorem
      
      |- -u * x + -v * y < a ⇔ ¬(u * x + v * y ≤ -a)
   
   [r177]  Theorem
      
      |- -u * x + -v * y < -a ⇔ ¬(u * x + v * y ≤ a)
   
   [r178]  Theorem
      
      |- -u * x + (v * y + w * z) < a ⇔ ¬(u * x + (-v * y + -w * z) ≤ -a)
   
   [r179]  Theorem
      
      |- -u * x + (v * y + w * z) < -a ⇔ ¬(u * x + (-v * y + -w * z) ≤ a)
   
   [r180]  Theorem
      
      |- -u * x + (v * y + -w * z) < a ⇔ ¬(u * x + (-v * y + w * z) ≤ -a)
   
   [r181]  Theorem
      
      |- -u * x + (v * y + -w * z) < -a ⇔ ¬(u * x + (-v * y + w * z) ≤ a)
   
   [r182]  Theorem
      
      |- -u * x + (-v * y + w * z) < a ⇔ ¬(u * x + (v * y + -w * z) ≤ -a)
   
   [r183]  Theorem
      
      |- -u * x + (-v * y + w * z) < -a ⇔ ¬(u * x + (v * y + -w * z) ≤ a)
   
   [r184]  Theorem
      
      |- -u * x + (-v * y + -w * z) < a ⇔ ¬(u * x + (v * y + w * z) ≤ -a)
   
   [r185]  Theorem
      
      |- -u * x + (-v * y + -w * z) < -a ⇔ ¬(u * x + (v * y + w * z) ≤ a)
   
   [r186]  Theorem
      
      |- -u * x + (-v * y + w * z) < 0 ⇔ ¬(u * x + (v * y + -w * z) ≤ 0)
   
   [r187]  Theorem
      
      |- -u * x + (-v * y + -w * z) < 0 ⇔ ¬(u * x + (v * y + w * z) ≤ 0)
   
   [r188]  Theorem
      
      |- -1 * x + (v * y + w * z) < a ⇔ ¬(x + (-v * y + -w * z) ≤ -a)
   
   [r189]  Theorem
      
      |- -1 * x + (v * y + w * z) < -a ⇔ ¬(x + (-v * y + -w * z) ≤ a)
   
   [r190]  Theorem
      
      |- -1 * x + (v * y + -w * z) < a ⇔ ¬(x + (-v * y + w * z) ≤ -a)
   
   [r191]  Theorem
      
      |- -1 * x + (v * y + -w * z) < -a ⇔ ¬(x + (-v * y + w * z) ≤ a)
   
   [r192]  Theorem
      
      |- -1 * x + (-v * y + w * z) < a ⇔ ¬(x + (v * y + -w * z) ≤ -a)
   
   [r193]  Theorem
      
      |- -1 * x + (-v * y + w * z) < -a ⇔ ¬(x + (v * y + -w * z) ≤ a)
   
   [r194]  Theorem
      
      |- -1 * x + (-v * y + -w * z) < a ⇔ ¬(x + (v * y + w * z) ≤ -a)
   
   [r195]  Theorem
      
      |- -1 * x + (-v * y + -w * z) < -a ⇔ ¬(x + (v * y + w * z) ≤ a)
   
   [r196]  Theorem
      
      |- -u * x + (-1 * y + -w * z) < -a ⇔ ¬(u * x + (y + w * z) ≤ a)
   
   [r197]  Theorem
      
      |- -u * x + (v * y + -1 * z) < -a ⇔ ¬(u * x + (-v * y + z) ≤ a)
   
   [r198]  Theorem
      
      |- 0 + x = x
   
   [r199]  Theorem
      
      |- x + 0 = x
   
   [r200]  Theorem
      
      |- x + y = y + x
   
   [r201]  Theorem
      
      |- x + x = 2 * x
   
   [r202]  Theorem
      
      |- x + y + z = x + (y + z)
   
   [r203]  Theorem
      
      |- x + y + z = x + (z + y)
   
   [r204]  Theorem
      
      |- x + (y + z) = y + (z + x)
   
   [r205]  Theorem
      
      |- x + (y + z) = y + (x + z)
   
   [r206]  Theorem
      
      |- 0 − x = -x
   
   [r207]  Theorem
      
      |- 0 − u * x = -u * x
   
   [r208]  Theorem
      
      |- x − 0 = x
   
   [r209]  Theorem
      
      |- x − y = x + -1 * y
   
   [r210]  Theorem
      
      |- x − y = -1 * y + x
   
   [r211]  Theorem
      
      |- x − u * y = x + -u * y
   
   [r212]  Theorem
      
      |- x − u * y = -u * y + x
   
   [r213]  Theorem
      
      |- x + y − z = x + (y + -1 * z)
   
   [r214]  Theorem
      
      |- x + y − z = x + (-1 * z + y)
   
   [r215]  Theorem
      
      |- x + y − u * z = -u * z + (x + y)
   
   [r216]  Theorem
      
      |- x + y − u * z = x + (-u * z + y)
   
   [r217]  Theorem
      
      |- x + y − u * z = x + (y + -u * z)
   
   [r218]  Theorem
      
      |- 0 * x = 0
   
   [r219]  Theorem
      
      |- 1 * x = x
   
   [r220]  Theorem
      
      |- 0w + x = x
   
   [r221]  Theorem
      
      |- x + y = y + x
   
   [r222]  Theorem
      
      |- 1w + (1w + x) = 2w + x
   
   [r223]  Theorem
      
      [oracles: DISK_THM] [axioms: ] [FINITE 𝕌(:α), x < dimword (:β)]
      |- 0w @@ n2w x = n2w x
   
   [r224]  Theorem
      
      [oracles: DISK_THM] [axioms: ] [x < dimword (:α)] |- w2w (n2w x) = n2w x
   
   [r225]  Theorem
      
      [oracles: DISK_THM] [axioms: ]
      [FINITE 𝕌(:α), y < dimword (:β), dimindex (:β) ≤ dimindex (:γ)]
      |- (0w @@ x = n2w y) ⇔ (x = n2w y)
   
   [r226]  Theorem
      
      [oracles: DISK_THM] [axioms: ]
      [FINITE 𝕌(:α), y < dimword (:β), dimindex (:β) ≤ dimindex (:γ)]
      |- (0w @@ x = n2w y) ⇔ (n2w y = x)
   
   [r227]  Theorem
      
      [oracles: DISK_THM] [axioms: ]
      [FINITE 𝕌(:α), y < dimword (:β), dimindex (:β) ≤ dimindex (:γ)]
      |- (n2w y = 0w @@ x) ⇔ (x = n2w y)
   
   [r228]  Theorem
      
      [oracles: DISK_THM] [axioms: ]
      [FINITE 𝕌(:α), y < dimword (:β), dimindex (:β) ≤ dimindex (:γ)]
      |- (n2w y = 0w @@ x) ⇔ (n2w y = x)
   
   [r229]  Theorem
      
      |- x && y = y && x
   
   [r230]  Theorem
      
      |- x && y && z = y && x && z
   
   [r231]  Theorem
      
      |- x && y && z = (x && y) && z
   
   [r232]  Theorem
      
      |- (1w = x && y) ⇔ (1w = x) ∧ (1w = y)
   
   [r233]  Theorem
      
      |- (1w = x && y) ⇔ (1w = y) ∧ (1w = x)
   
   [r234]  Theorem
      
      |- (7 >< 0) x = x
   
   [r235]  Theorem
      
      |- x <₊ y ⇔ ¬(y ≤₊ x)
   
   [r236]  Theorem
      
      |- x * y = y * x
   
   [r237]  Theorem
      
      |- (0 >< 0) x = x
   
   [r238]  Theorem
      
      |- (x && y) && z = x && y && z
   
   [r239]  Theorem
      
      |- 0w ‖ x = x
   
   [t001]  Theorem
      
      |- x ≠ y ∨ x ≤ y
   
   [t002]  Theorem
      
      |- x ≠ y ∨ x ≥ y
   
   [t003]  Theorem
      
      |- x ≠ y ∨ x + -1 * y ≥ 0
   
   [t004]  Theorem
      
      |- x ≠ y ∨ x + -1 * y ≤ 0
   
   [t005]  Theorem
      
      |- (x = y) ∨ ¬(x ≤ y) ∨ ¬(x ≥ y)
   
   [t006]  Theorem
      
      |- ¬(x ≤ 0) ∨ x ≤ 1
   
   [t007]  Theorem
      
      |- ¬(x ≤ -1) ∨ x ≤ 0
   
   [t008]  Theorem
      
      |- ¬(x ≥ 0) ∨ x ≥ -1
   
   [t009]  Theorem
      
      |- ¬(x ≥ 0) ∨ ¬(x ≤ -1)
   
   [t010]  Theorem
      
      |- x ≥ y ∨ x ≤ y
   
   [t011]  Theorem
      
      |- x ≠ y ∨ x + -1 * y ≥ 0
   
   [t012]  Theorem
      
      |- x ≠ ¬x
   
   [t013]  Theorem
      
      |- (x = y) ⇒ x ' i ⇒ y ' i
   
   [t014]  Theorem
      
      |- (1w = ¬x) ∨ x ' 0
   
   [t015]  Theorem
      
      |- x ' 0 ⇒ (0w = ¬x)
   
   [t016]  Theorem
      
      |- x ' 0 ⇒ (1w = x)
   
   [t017]  Theorem
      
      |- ¬x ' 0 ⇒ (0w = x)
   
   [t018]  Theorem
      
      |- ¬x ' 0 ⇒ (1w = ¬x)
   
   [t019]  Theorem
      
      |- (0w = ¬x) ∨ ¬x ' 0
   
   [t020]  Theorem
      
      |- (1w = ¬x ‖ ¬y) ∨ ¬(¬x ' 0 ∨ ¬y ' 0)
   
   [t021]  Theorem
      
      |- (0w = x) ∨ x ' 0 ∨ x ' 1 ∨ x ' 2 ∨ x ' 3 ∨ x ' 4 ∨ x ' 5 ∨ x ' 6 ∨ x ' 7
   
   [t022]  Theorem
      
      |- ((x = 1w) ⇔ p) ⇔ (x = if p then 1w else 0w)
   
   [t023]  Theorem
      
      |- ((1w = x) ⇔ p) ⇔ (x = if p then 1w else 0w)
   
   [t024]  Theorem
      
      |- (p ⇔ (x = 1w)) ⇔ (x = if p then 1w else 0w)
   
   [t025]  Theorem
      
      |- (p ⇔ (1w = x)) ⇔ (x = if p then 1w else 0w)
   
   [t026]  Theorem
      
      |- (0w = 0xFFFFFFFFw * sw2sw x) ⇒ ¬x ' 0
   
   [t027]  Theorem
      
      |- (0w = 0xFFFFFFFFw * sw2sw x) ⇒ (x ' 1 ⇎ ¬x ' 0)
   
   [t028]  Theorem
      
      |- (0w = 0xFFFFFFFFw * sw2sw x) ⇒ (x ' 2 ⇎ ¬x ' 0 ∧ ¬x ' 1)
   
   [t029]  Theorem
      
      [oracles: MK_THM] [axioms: ] [] |- (1w + x = y) ⇒ x ' 0 ⇒ ¬y ' 0
   
   
*)
end
