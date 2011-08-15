signature pattern_matchingTheory =
sig
  type thm = Thm.thm
  
  (*  Definitions  *)
    val f1_def : thm
    val f2_def : thm
    val f3_def : thm
    val f4_primitive_def : thm
    val f5_primitive_def : thm
    val f6_primitive_def : thm
    val f7_primitive_def : thm
    val f8_primitive_def : thm
    val f9_primitive_def : thm
    val f_def : thm
    val g10_primitive_def : thm
    val g1_primitive_def : thm
    val g2_primitive_def : thm
    val g3_primitive_def : thm
    val g4_primitive_def : thm
    val g5_primitive_def : thm
    val g6_primitive_def : thm
    val g7_primitive_def : thm
    val g8_primitive_def : thm
    val g9_primitive_def : thm
    val g_primitive_def : thm
    val h1_primitive_def : thm
    val h2_primitive_def : thm
    val h_primitive_def : thm
  
  val pattern_matching_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [list] Parent theory of "pattern_matching"
   
   [f1_def]  Definition
      
      |- (f1 0 = 1) ∧ ∀n. f1 (SUC n) = 2
   
   [f2_def]  Definition
      
      |- f2 0 = 1
   
   [f3_def]  Definition
      
      |- ∀h t. f3 (h::t) = h
   
   [f4_primitive_def]  Definition
      
      |- f4 =
         WFREC (@R. WF R)
           (λf4 a'.
              case a' of
                 [] -> ARB
              || [a] -> I a
              || [a; b] -> I a
              || a::b::v4::v5 -> ARB)
   
   [f5_primitive_def]  Definition
      
      |- f5 =
         WFREC (@R. WF R)
           (λf5 a.
              case a of
                 (0,0) -> I 0
              || (0,SUC v4) -> ARB
              || (SUC v2,v1) -> ARB)
   
   [f6_primitive_def]  Definition
      
      |- f6 =
         WFREC (@R. WF R)
           (λf6 a.
              case a of
                 (0,0) -> I 0
              || (0,SUC x) -> I x
              || (SUC x',y) -> I (y + x'))
   
   [f7_primitive_def]  Definition
      
      |- f7 =
         WFREC (@R. WF R)
           (λf7 a.
              case a of
                 (0,v1) -> ARB
              || (SUC 0,[]) -> ARB
              || (SUC 0,h::t) -> I 1
              || (SUC (SUC n),[]) -> ARB
              || (SUC (SUC n),[h1]) -> ARB
              || (SUC (SUC n),h1::h2::t') -> I h1)
   
   [f8_primitive_def]  Definition
      
      |- f8 =
         WFREC (@R. WF R)
           (λf8 a.
              case a of
                 (0,v1) -> ARB
              || (SUC 0,v1) -> ARB
              || (SUC (SUC n),[]) -> ARB
              || (SUC (SUC n),[h1]) -> ARB
              || (SUC (SUC n),h1::h2::t) -> I h1)
   
   [f9_primitive_def]  Definition
      
      |- f9 =
         WFREC (@R. WF R)
           (λf9 a.
              case a of [] -> I [] || [h1] -> I [h1] || h1::h2::t -> I t)
   
   [f_def]  Definition
      
      |- ∀x y. f (x,y) = x + y
   
   [g10_primitive_def]  Definition
      
      |- g10 =
         WFREC (@R. WF R)
           (λg10 a.
              case a of 0 -> I 3 || SUC 0 -> I 2 || SUC (SUC x) -> I 1)
   
   [g1_primitive_def]  Definition
      
      |- g1 =
         WFREC (@R. WF R)
           (λg1 a.
              case a of
                 (0,0) -> I 0
              || (0,SUC v5) -> I (SUC v5)
              || (SUC v3,0) -> I (SUC v3)
              || (SUC v3,SUC v6) -> ARB)
   
   [g2_primitive_def]  Definition
      
      |- g2 =
         WFREC (@R. WF R)
           (λg2 a'.
              case a' of
                 ([],[]) -> ARB
              || ([],[a]) -> I 3
              || ([],a::b::x) -> I 1
              || ([v4],[]) -> ARB
              || ([v4],v16::v17) -> I 3
              || (v4::v14::v15,[]) -> I 2
              || (v4::v14::v15,v20::v21) -> I 2)
   
   [g3_primitive_def]  Definition
      
      |- g3 =
         WFREC (@R. WF R)
           (λg3 a.
              case a of
                 (0,0,0) -> I 1
              || (0,0,SUC v12) -> I 2
              || (0,SUC v9,0) -> I 1
              || (0,SUC v9,SUC v14) -> I 3
              || (SUC v4,0,0) -> I 1
              || (SUC v4,0,SUC v20) -> I 2
              || (SUC v4,SUC v18,0) -> I 1
              || (SUC v4,SUC v18,SUC v21) -> ARB)
   
   [g4_primitive_def]  Definition
      
      |- g4 =
         WFREC (@R. WF R)
           (λg4 a.
              case a of
                 (0,0,0) -> I 1
              || (0,0,SUC v12) -> I 1
              || (0,SUC v9,0) -> I 1
              || (0,SUC v9,SUC v14) -> I 1
              || (SUC v4,0,0) -> I 2
              || (SUC v4,0,SUC v20) -> I 2
              || (SUC v4,SUC v18,0) -> I 3
              || (SUC v4,SUC v18,SUC v21) -> ARB)
   
   [g5_primitive_def]  Definition
      
      |- g5 =
         WFREC (@R. WF R)
           (λg5 a.
              case a of
                 (0,0,0,0) -> I 1
              || (0,0,0,SUC v21) -> I 1
              || (0,0,SUC v17,0) -> I 1
              || (0,0,SUC v17,SUC v24) -> I 1
              || (0,SUC v11,0,0) -> I 1
              || (0,SUC v11,0,SUC v32) -> I 1
              || (0,SUC v11,SUC v29,0) -> I 1
              || (0,SUC v11,SUC v29,SUC v34) -> I 1
              || (SUC v5,0,0,0) -> I 2
              || (SUC v5,0,0,SUC v47) -> I 2
              || (SUC v5,0,SUC v44,0) -> I 2
              || (SUC v5,0,SUC v44,SUC v49) -> I 2
              || (SUC v5,SUC v39,0,0) -> I 3
              || (SUC v5,SUC v39,0,SUC v55) -> I 3
              || (SUC v5,SUC v39,SUC v53,0) -> I 4
              || (SUC v5,SUC v39,SUC v53,SUC v56) -> ARB)
   
   [g6_primitive_def]  Definition
      
      |- g6 =
         WFREC (@R. WF R)
           (λg6 a.
              case a of
                 (0,0,0,0,0) -> I 1
              || (0,0,0,0,SUC v33) -> I 1
              || (0,0,0,SUC v28,0) -> I 1
              || (0,0,0,SUC v28,SUC v37) -> I 1
              || (0,0,SUC v21,0,0) -> I 1
              || (0,0,SUC v21,0,SUC v47) -> I 1
              || (0,0,SUC v21,SUC v43,0) -> I 1
              || (0,0,SUC v21,SUC v43,SUC v50) -> I 1
              || (0,SUC v14,0,0,0) -> I 1
              || (0,SUC v14,0,0,SUC v66) -> I 1
              || (0,SUC v14,0,SUC v62,0) -> I 1
              || (0,SUC v14,0,SUC v62,SUC v69) -> I 1
              || (0,SUC v14,SUC v56,0,0) -> I 1
              || (0,SUC v14,SUC v56,0,SUC v77) -> I 1
              || (0,SUC v14,SUC v56,SUC v74,0) -> I 1
              || (0,SUC v14,SUC v56,SUC v74,SUC v79) -> I 1
              || (SUC v7,0,0,0,0) -> I 2
              || (SUC v7,0,0,0,SUC v101) -> I 2
              || (SUC v7,0,0,SUC v97,0) -> I 2
              || (SUC v7,0,0,SUC v97,SUC v104) -> I 2
              || (SUC v7,0,SUC v91,0,0) -> I 2
              || (SUC v7,0,SUC v91,0,SUC v112) -> I 2
              || (SUC v7,0,SUC v91,SUC v109,0) -> I 2
              || (SUC v7,0,SUC v91,SUC v109,SUC v114) -> I 2
              || (SUC v7,SUC v85,0,0,0) -> I 3
              || (SUC v7,SUC v85,0,0,SUC v127) -> I 3
              || (SUC v7,SUC v85,0,SUC v124,0) -> I 3
              || (SUC v7,SUC v85,0,SUC v124,SUC v129) -> I 3
              || (SUC v7,SUC v85,SUC v119,0,0) -> I 4
              || (SUC v7,SUC v85,SUC v119,0,SUC v135) -> I 4
              || (SUC v7,SUC v85,SUC v119,SUC v133,0) -> I 5
              || (SUC v7,SUC v85,SUC v119,SUC v133,SUC v136) -> ARB)
   
   [g7_primitive_def]  Definition
      
      |- g7 =
         WFREC (@R. WF R)
           (λg7 a.
              case a of
                 [] -> I 2
              || [0] -> I 2
              || [0; 0] -> I 0
              || 0::0::v16::v17 -> I 2
              || 0::SUC v13::v11 -> I 2
              || [SUC v] -> I 1
              || [SUC v; 0] -> I (SUC v)
              || SUC v::0::v26::v27 -> I 2
              || SUC v::SUC v23::v21 -> I 2)
   
   [g8_primitive_def]  Definition
      
      |- g8 =
         WFREC (@R. WF R)
           (λg8 a.
              case a of
                 [] -> I [[]]
              || [h1] -> I [[h1]]
              || [h1; h2] -> I [[h1; h2]]
              || [h1; h2; h3] -> I [[h1; h2; h3]]
              || [h1; h2; h3; h4] -> I [[h1; h2; h3; h4]]
              || h1::h2::h3::h4::h5::h6 -> I [[h1; h2; h3; h4; h5]; h6])
   
   [g9_primitive_def]  Definition
      
      |- g9 =
         WFREC (@R. WF R)
           (λg9 a.
              case a of
                 [] -> I []
              || [h1] -> I [[h1]]
              || [h1; h2] -> I [[h1; h2]]
              || [h1; h2; h3] -> I [[h1; h2; h3]]
              || [h1; h2; h3; h4] -> I [[h1; h2; h3; h4]]
              || h1::h2::h3::h4::h5::h6 -> I [[h1; h2; h3; h4; h5]; h6])
   
   [g_primitive_def]  Definition
      
      |- g =
         WFREC (@R. WF R)
           (λg a.
              case a of
                 (0,0) -> I 1
              || (0,SUC v5) -> I 2
              || (SUC v3,0) -> I 1
              || (SUC v3,SUC v6) -> ARB)
   
   [h1_primitive_def]  Definition
      
      |- h1 =
         WFREC (@R. WF R)
           (λh1 a.
              case a of
                 (0,0) -> I 1
              || (0,SUC q) -> I 2
              || (SUC v5,0) -> I 1
              || (SUC v5,SUC v9) -> I 2)
   
   [h2_primitive_def]  Definition
      
      |- h2 =
         WFREC (@R. WF R)
           (λh2 a.
              case a of
                 (0,0) -> I 1
              || (0,SUC v7) -> I 2
              || (SUC v4,0) -> I 1
              || (SUC v4,SUC v9) -> I 4)
   
   [h_primitive_def]  Definition
      
      |- h = WFREC (@R. WF R) (λh x. I 1)
   
   
*)
end
