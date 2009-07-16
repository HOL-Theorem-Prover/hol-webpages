signature Omega_AutomataTheory =
sig
  type thm = Thm.thm
  
  (*  Theorems  *)
    val AUTOMATON_TEMP_CLOSURE : thm
    val BEFORE_AS_CO_BUECHI : thm
    val BOOLEAN_CLOSURE_F : thm
    val BOOLEAN_CLOSURE_FG : thm
    val BOOLEAN_CLOSURE_G : thm
    val BOOLEAN_CLOSURE_GF : thm
    val BOREL_HIERARCHY_F : thm
    val BOREL_HIERARCHY_FG : thm
    val BOREL_HIERARCHY_G : thm
    val BUECHI_PERIODIC_MODEL : thm
    val BUECHI_PERIODIC_REDUCTION_THM : thm
    val BUECHI_PROP_REDUCTION : thm
    val BUECHI_TRANSLATION : thm
    val CO_BUECHI_BEFORE_CLOSURE : thm
    val CO_BUECHI_CONJ_CLOSURE : thm
    val CO_BUECHI_DISJ_CLOSURE : thm
    val CO_BUECHI_NEXT_CLOSURE : thm
    val CO_BUECHI_SBEFORE_CLOSURE : thm
    val CO_BUECHI_SUNTIL_CLOSURE : thm
    val CO_BUECHI_SWHEN_CLOSURE : thm
    val CO_BUECHI_UNTIL_CLOSURE : thm
    val CO_BUECHI_WHEN_CLOSURE : thm
    val DET_OMEGA_EXISTS_FORALL_THEOREM : thm
    val ELGOT1_THM : thm
    val ELGOT2_THM : thm
    val ELGOT_LEMMA : thm
    val EQUALITY_THM : thm
    val EXISTS_FORALL_THM : thm
    val FORALL_EXISTS_THM : thm
    val LESS_THM : thm
    val NEG_DET_AUTOMATA : thm
    val NEXT_AS_CO_BUECHI : thm
    val OMEGA_CONJ_CLOSURE : thm
    val OMEGA_DISJ_CLOSURE : thm
    val SBEFORE_AS_CO_BUECHI : thm
    val SUNTIL_AS_CO_BUECHI : thm
    val SWHEN_AS_CO_BUECHI : thm
    val TEMP_OPS_DEFS_TO_OMEGA : thm
    val UNTIL_AS_CO_BUECHI : thm
    val WHEN_AS_CO_BUECHI : thm
  
  val Omega_Automata_grammars : type_grammar.grammar * term_grammar.grammar
  
  
(*
   [Past_Temporal_Logic] Parent theory of "Omega_Automata"
   
   [AUTOMATON_TEMP_CLOSURE]  Theorem
      
      |- ((?q1.
             Phi_I1 q1 /\ Phi_R1 q1 /\
             ?q2. Phi_I2 q2 /\ Phi_R2 (q2,q1) /\ Phi_F (q1,q2)) <=>
          ?q1 q2.
            (Phi_I1 q1 /\ Phi_I2 q2) /\ (Phi_R1 q1 /\ Phi_R2 (q2,q1)) /\
            Phi_F (q1,q2)) /\
         (Phi (NEXT phi) <=>
          ?q0 q1.
            T /\ (!t. (q0 t <=> phi t) /\ (q1 t <=> q0 (t + 1))) /\
            Phi q1) /\
         (Phi (PNEXT phi) <=>
          ?q. q 0 /\ (!t. q (t + 1) <=> phi t) /\ Phi q) /\
         (Phi (PSNEXT phi) <=>
          ?q. ~q 0 /\ (!t. q (t + 1) <=> phi t) /\ Phi q) /\
         (Phi (PNEXT (PALWAYS a)) <=>
          ?q. q 0 /\ (!t. q (t + 1) <=> a t /\ q t) /\ Phi q) /\
         (Phi (PSNEXT (PEVENTUAL a)) <=>
          ?q. ~q 0 /\ (!t. q (t + 1) <=> a t \/ q t) /\ Phi q) /\
         (Phi (PSNEXT (a PSUNTIL b)) <=>
          ?q. ~q 0 /\ (!t. q (t + 1) <=> b t \/ a t /\ q t) /\ Phi q) /\
         (Phi (PSNEXT (a PSWHEN b)) <=>
          ?q.
            ~q 0 /\ (!t. q (t + 1) <=> a t /\ b t \/ ~b t /\ q t) /\
            Phi q) /\
         (Phi (PSNEXT (a PSBEFORE b)) <=>
          ?q. ~q 0 /\ (!t. q (t + 1) <=> ~b t /\ (a t \/ q t)) /\ Phi q) /\
         (Phi (PNEXT (a PUNTIL b)) <=>
          ?q. q 0 /\ (!t. q (t + 1) <=> b t \/ a t /\ q t) /\ Phi q) /\
         (Phi (PNEXT (a PWHEN b)) <=>
          ?q.
            q 0 /\ (!t. q (t + 1) <=> a t /\ b t \/ ~b t /\ q t) /\
            Phi q) /\
         (Phi (PNEXT (a PBEFORE b)) <=>
          ?q. q 0 /\ (!t. q (t + 1) <=> ~b t /\ (a t \/ q t)) /\ Phi q)
   
   [BEFORE_AS_CO_BUECHI]  Theorem
      
      |- (a BEFORE b) t0 <=>
         ?q.
           ~q t0 /\
           (!t.
              ~q (t + t0) /\ ~a (t + t0) /\ ~b (t + t0) /\
              ~q (t + (1 + t0)) \/
              ~q (t + t0) /\ a (t + t0) /\ ~b (t + t0) /\
              q (t + (1 + t0)) \/ q (t + t0) /\ q (t + (1 + t0))) /\
           ?t1. !t2. ~q (t1 + (t2 + t0)) \/ q (t1 + (t2 + t0))
   
   [BOOLEAN_CLOSURE_F]  Theorem
      
      |- (~(?t. a (t + t0)) <=> !t. ~a (t + t0)) /\
         ((?t. a (t + t0)) \/ (?t. b (t + t0)) <=>
          ?t. a (t + t0) \/ b (t + t0)) /\
         ((?t. a (t + t0)) /\ (?t. b (t + t0)) <=>
          ?p q.
            (~p t0 /\ ~q t0) /\
            (!t.
               (p (t + (t0 + 1)) <=> p (t + t0) \/ a (t + t0)) /\
               (q (t + (t0 + 1)) <=> q (t + t0) \/ b (t + t0))) /\
            ?t. p (t + t0) /\ q (t + t0))
   
   [BOOLEAN_CLOSURE_FG]  Theorem
      
      |- (~(?t1. !t2. a (t1 + (t2 + t0))) <=>
          !t1. ?t2. ~a (t1 + (t2 + t0))) /\
         ((?t1. !t2. a (t1 + (t2 + t0))) /\
          (?t1. !t2. b (t1 + (t2 + t0))) <=>
          ?t1. !t2. a (t1 + (t2 + t0)) /\ b (t1 + (t2 + t0))) /\
         ((?t1. !t2. a (t1 + (t2 + t0))) \/
          (?t1. !t2. b (t1 + (t2 + t0))) <=>
          ?q.
            ~q t0 /\
            (!t.
               q (t + (t0 + 1)) <=>
               if q (t + t0) then b (t + t0) else ~a (t + t0)) /\
            ?t1. !t2. ~q (t1 + (t2 + t0)) \/ b (t1 + (t2 + t0)))
   
   [BOOLEAN_CLOSURE_G]  Theorem
      
      |- (~(!t. a (t + t0)) <=> ?t. ~a (t + t0)) /\
         ((!t. a (t + t0)) /\ (!t. b (t + t0)) <=>
          !t. a (t + t0) /\ b (t + t0)) /\
         ((!t. a (t + t0)) \/ (!t. b (t + t0)) <=>
          ?p q.
            (~p t0 /\ ~q t0) /\
            (!t.
               (p (t + (t0 + 1)) <=> p (t + t0) \/ ~a (t + t0)) /\
               (q (t + (t0 + 1)) <=> q (t + t0) \/ ~b (t + t0))) /\
            !t. ~p (t + t0) \/ ~q (t + t0))
   
   [BOOLEAN_CLOSURE_GF]  Theorem
      
      |- (~(!t1. ?t2. a (t1 + (t2 + t0))) <=>
          ?t1. !t2. ~a (t1 + (t2 + t0))) /\
         ((!t1. ?t2. a (t1 + (t2 + t0))) \/
          (!t1. ?t2. b (t1 + (t2 + t0))) <=>
          !t1. ?t2. a (t1 + (t2 + t0)) \/ b (t1 + (t2 + t0))) /\
         ((!t1. ?t2. a (t1 + (t2 + t0))) /\
          (!t1. ?t2. b (t1 + (t2 + t0))) <=>
          ?q.
            ~q t0 /\
            (!t.
               q (t + (t0 + 1)) <=>
               if q (t + t0) then ~b (t + t0) else a (t + t0)) /\
            !t1. ?t2. q (t1 + (t2 + t0)) /\ b (t1 + (t2 + t0)))
   
   [BOREL_HIERARCHY_F]  Theorem
      
      |- ((?t. a (t + t0)) <=>
          ?q.
            ~q t0 /\ (!t. q (SUC (t + t0)) <=> q (t + t0) \/ a (t + t0)) /\
            ?t1. !t2. q (t1 + (t2 + t0))) /\
         ((?t. a (t + t0)) <=>
          ?q.
            ~q t0 /\ (!t. q (SUC (t + t0)) <=> q (t + t0) \/ a (t + t0)) /\
            !t1. ?t2. q (t1 + (t2 + t0)))
   
   [BOREL_HIERARCHY_FG]  Theorem
      
      |- ((?t1. !t2. a (t1 + (t2 + t0))) <=>
          ?q.
            ~q t0 /\ (!t. q (t + t0) ==> a (t + t0) /\ q (SUC (t + t0))) /\
            ?t. q (t + t0)) /\
         ((?t1. !t2. a (t1 + (t2 + t0))) <=>
          ?p q.
            (~p t0 /\ ~q t0) /\
            (!t.
               (p (t + t0) ==> p (SUC (t + t0))) /\
               (p (SUC (t + t0)) ==> p (t + t0) \/ ~q (t + t0)) /\
               (q (SUC (t + t0)) <=>
                p (t + t0) /\ ~q (t + t0) /\ ~a (t + t0) \/
                p (t + t0) /\ q (t + t0))) /\
            !t1. ?t2. p (t1 + (t2 + t0)) /\ ~q (t1 + (t2 + t0)))
   
   [BOREL_HIERARCHY_G]  Theorem
      
      |- ((!t. a (t + t0)) <=>
          ?q.
            q t0 /\ (!t. q (t + t0) /\ a (t + t0) /\ q (SUC (t + t0))) /\
            ?t. q (t + t0)) /\
         ((!t. a (t + t0)) <=>
          ?q.
            q t0 /\ (!t. q (SUC (t + t0)) <=> q (t + t0) /\ a (t + t0)) /\
            ?t1. !t2. q (t1 + (t2 + t0))) /\
         ((!t. a (t + t0)) <=>
          ?q.
            q t0 /\ (!t. q (SUC (t + t0)) <=> q (t + t0) /\ a (t + t0)) /\
            !t1. ?t2. q (t1 + (t2 + t0)))
   
   [BUECHI_PERIODIC_MODEL]  Theorem
      
      |- (!s. ?x0 l. 0 < l /\ (s x0 = s (x0 + l))) ==>
         ((?i q.
             InitState (q 0) /\ (!t. TransRel (i t,q t,q (t + 1))) /\
             !t1. ?t2. Accept (q (t1 + t2))) <=>
          ?x0 l j p.
            0 < l /\ (!t2. j (x0 + t2) = j (x0 + t2 MOD l)) /\
            (!t2. p (x0 + t2) = p (x0 + t2 MOD l)) /\ InitState (p 0) /\
            (!t. TransRel (j t,p t,p (t + 1))) /\
            !t1. ?t2. Accept (p (t1 + t2)))
   
   [BUECHI_PERIODIC_REDUCTION_THM]  Theorem
      
      |- (!s. ?x0 l. 0 < l /\ (s x0 = s (x0 + l))) ==>
         ((?i q.
             InitState (q 0) /\ (!t. TransRel (i t,q t,q (t + 1))) /\
             !t1. ?t2. Accept (q (t1 + t2))) <=>
          ?x0 l j p.
            0 < l /\ (!t2. j (x0 + t2) = j (x0 + t2 MOD l)) /\
            (!t2. p (x0 + t2) = p (x0 + t2 MOD l)) /\ InitState (p 0) /\
            (!t. t < x0 + l ==> TransRel (j t,p t,p (t + 1))) /\
            ?t. t < l /\ Accept (p (x0 + t)))
   
   [BUECHI_PROP_REDUCTION]  Theorem
      
      |- (!s. ?x0 l. 0 < l /\ (s x0 = s (x0 + l))) ==>
         ((?i q.
             InitState (q 0) /\ (!t. TransRel (i t,q t,q (t + 1))) /\
             !t1. ?t2. Accept (q (t1 + t2))) <=>
          ?x0 l j p.
            0 < l /\ InitState (p 0) /\
            (!t. t < x0 + l ==> TransRel (j t,p t,p (t + 1))) /\
            (?t. t < l /\ Accept (p (x0 + t))) /\ (p x0 = p (x0 + l)))
   
   [BUECHI_TRANSLATION]  Theorem
      
      |- (Phi (NEXT phi) <=>
          ?q0 q1.
            T /\ (!t. (q0 t <=> phi t) /\ (q1 t <=> q0 (t + 1))) /\
            Phi q1) /\
         (Phi (ALWAYS a) <=>
          ?q.
            T /\ (!t. q t <=> a t /\ q (t + 1)) /\
            (!t1. ?t2. a (t1 + t2) ==> q (t1 + t2)) /\ Phi q) /\
         (Phi (EVENTUAL a) <=>
          ?q.
            T /\ (!t. q t <=> a t \/ q (t + 1)) /\
            (!t1. ?t2. q (t1 + t2) ==> a (t1 + t2)) /\ Phi q) /\
         (Phi (a SUNTIL b) <=>
          ?q.
            T /\ (!t. q t <=> b t \/ a t /\ q (t + 1)) /\
            (!t1. ?t2. q (t1 + t2) ==> ~a (t1 + t2) \/ b (t1 + t2)) /\
            Phi q) /\
         (Phi (a UNTIL b) <=>
          ?q.
            T /\ (!t. q t <=> b t \/ a t /\ q (t + 1)) /\
            (!t1. ?t2. ~q (t1 + t2) ==> ~a (t1 + t2) \/ b (t1 + t2)) /\
            Phi q) /\
         (Phi (a SWHEN b) <=>
          ?q.
            T /\ (!t. q t <=> if b t then a t else q (t + 1)) /\
            (!t1. ?t2. q (t1 + t2) ==> b (t1 + t2)) /\ Phi q) /\
         (Phi (a WHEN b) <=>
          ?q.
            T /\ (!t. q t <=> if b t then a t else q (t + 1)) /\
            (!t1. ?t2. q (t1 + t2) \/ b (t1 + t2)) /\ Phi q) /\
         (Phi (a SBEFORE b) <=>
          ?q.
            T /\ (!t. q t <=> ~b t /\ (a t \/ q (t + 1))) /\
            (!t1. ?t2. q (t1 + t2) ==> a (t1 + t2) \/ b (t1 + t2)) /\
            Phi q) /\
         (Phi (a BEFORE b) <=>
          ?q.
            T /\ (!t. q t <=> ~b t /\ (a t \/ q (t + 1))) /\
            (!t1. ?t2. ~q (t1 + t2) ==> a (t1 + t2) \/ b (t1 + t2)) /\
            Phi q)
   
   [CO_BUECHI_BEFORE_CLOSURE]  Theorem
      
      |- ((\t0.
             ?q.
               Phi_I (q t0) /\ (!t. Phi_R (i (t + t0),q (t + t0))) /\
               ?t1.
                 !t2. Psi (i (t1 + (t2 + t0)),q (t1 + (t2 + t0)))) BEFORE
          phi) t0 <=>
         ?p1 p2 q.
           (~p1 t0 /\ ~p2 t0 /\ (q t0 = c) \/
            p1 t0 /\ ~p2 t0 /\ Phi_I (q t0)) /\
           (!t.
              ~p1 (t + t0) /\ ~p2 (t + t0) /\ (q (t + t0) = c) /\
              ~phi (t + t0) /\ ~p1 (t + (t0 + 1)) /\ ~p2 (t + (t0 + 1)) /\
              (q (t + (t0 + 1)) = c) \/
              ~p1 (t + t0) /\ ~p2 (t + t0) /\ (q (t + t0) = c) /\
              ~phi (t + t0) /\ p1 (t + (t0 + 1)) /\ ~p2 (t + (t0 + 1)) /\
              Phi_I (q (t + (t0 + 1))) \/
              p1 (t + t0) /\ ~p2 (t + t0) /\ ~phi (t + t0) /\
              Phi_I (q (t + t0)) /\ Phi_R (i (t + t0),q (t + t0)) /\
              p1 (t + (t0 + 1)) /\ p2 (t + (t0 + 1)) \/
              p1 (t + t0) /\ p2 (t + t0) /\
              Phi_R (i (t + t0),q (t + t0)) /\ p1 (t + (t0 + 1)) /\
              p2 (t + (t0 + 1))) /\
           ?t1.
             !t2.
               ~p1 (t1 + (t2 + t0)) \/
               Psi (i (t1 + (t2 + t0)),q (t1 + (t2 + t0)))
   
   [CO_BUECHI_CONJ_CLOSURE]  Theorem
      
      |- (?q1.
            Phi_I1 (q1 t0) /\ (!t. Phi_R1 (i (t + t0),q1 (t + t0))) /\
            ?t1. !t2. Psi1 (i (t1 + (t2 + t0)),q1 (t1 + (t2 + t0)))) /\
         (?q2.
            Phi_I2 (q2 t0) /\ (!t. Phi_R2 (i (t + t0),q2 (t + t0))) /\
            ?t1. !t2. Psi2 (i (t1 + (t2 + t0)),q2 (t1 + (t2 + t0)))) <=>
         ?q1 q2.
           (Phi_I1 (q1 t0) /\ Phi_I2 (q2 t0)) /\
           (!t.
              Phi_R1 (i (t + t0),q1 (t + t0)) /\
              Phi_R2 (i (t + t0),q2 (t + t0))) /\
           ?t1.
             !t2.
               Psi1 (i (t1 + (t2 + t0)),q1 (t1 + (t2 + t0))) /\
               Psi2 (i (t1 + (t2 + t0)),q2 (t1 + (t2 + t0)))
   
   [CO_BUECHI_DISJ_CLOSURE]  Theorem
      
      |- (?q1.
            Phi_I1 (q1 t0) /\ (!t. Phi_R1 (i (t + t0),q1 (t + t0))) /\
            ?t1. !t2. Psi1 (i (t1 + (t2 + t0)),q1 (t1 + (t2 + t0)))) \/
         (?q2.
            Phi_I2 (q2 t0) /\ (!t. Phi_R2 (i (t + t0),q2 (t + t0))) /\
            ?t1. !t2. Psi2 (i (t1 + (t2 + t0)),q2 (t1 + (t2 + t0)))) <=>
         ?p q1 q2.
           (~p t0 /\ Phi_I1 (q1 t0) \/ p t0 /\ Phi_I2 (q2 t0)) /\
           (!t.
              ~p (t + t0) /\ Phi_R1 (i (t + t0),q1 (t + t0)) /\
              ~p (t + (t0 + 1)) \/
              p (t + t0) /\ Phi_R2 (i (t + t0),q2 (t + t0)) /\
              p (t + (t0 + 1))) /\
           ?t1.
             !t2.
               ~p (t + t0) /\
               Psi1 (i (t1 + (t2 + t0)),q1 (t1 + (t2 + t0))) \/
               p (t + t0) /\ Psi2 (i (t1 + (t2 + t0)),q2 (t1 + (t2 + t0)))
   
   [CO_BUECHI_NEXT_CLOSURE]  Theorem
      
      |- NEXT
           (\t0.
              ?q.
                Phi_I (q t0) /\ (!t. Phi_R (i (t + t0),q (t + t0))) /\
                ?t1. !t2. Psi (i (t1 + (t2 + t0)),q (t1 + (t2 + t0))))
           t0 <=>
         ?p q.
           ((p t0 <=> F) /\ (q t0 = c)) /\
           (!t.
              ~p (t + t0) /\ (q (t + t0) = c) /\ p (t + (t0 + 1)) /\
              Phi_I (q (t + (t0 + 1))) \/
              p (t + t0) /\ Phi_R (i (t + t0),q (t + t0)) /\
              p (t + (t0 + 1))) /\
           ?t1. !t2. Psi (i (t1 + (t2 + t0)),q (t1 + (t2 + t0)))
   
   [CO_BUECHI_SBEFORE_CLOSURE]  Theorem
      
      |- ((\t0.
             ?q.
               Phi_I (q t0) /\ (!t. Phi_R (i (t + t0),q (t + t0))) /\
               ?t1.
                 !t2. Psi (i (t1 + (t2 + t0)),q (t1 + (t2 + t0)))) SBEFORE
          phi) t0 <=>
         ?p1 p2 q.
           (~p1 t0 /\ ~p2 t0 /\ (q t0 = c) \/
            p1 t0 /\ ~p2 t0 /\ Phi_I (q t0)) /\
           (!t.
              ~p1 (t + t0) /\ ~p2 (t + t0) /\ (q (t + t0) = c) /\
              ~phi (t + t0) /\ ~p1 (t + (t0 + 1)) /\ ~p2 (t + (t0 + 1)) /\
              (q (t + (t0 + 1)) = c) \/
              ~p1 (t + t0) /\ ~p2 (t + t0) /\ (q (t + t0) = c) /\
              ~phi (t + t0) /\ p1 (t + (t0 + 1)) /\ ~p2 (t + (t0 + 1)) /\
              Phi_I (q (t + (t0 + 1))) \/
              p1 (t + t0) /\ ~p2 (t + t0) /\ ~phi (t + t0) /\
              Phi_I (q (t + t0)) /\ Phi_R (i (t + t0),q (t + t0)) /\
              p1 (t + (t0 + 1)) /\ p2 (t + (t0 + 1)) \/
              p1 (t + t0) /\ p2 (t + t0) /\
              Phi_R (i (t + t0),q (t + t0)) /\ p1 (t + (t0 + 1)) /\
              p2 (t + (t0 + 1))) /\
           ?t1.
             !t2.
               p1 (t1 + (t2 + t0)) /\
               Psi (i (t1 + (t2 + t0)),q (t1 + (t2 + t0)))
   
   [CO_BUECHI_SUNTIL_CLOSURE]  Theorem
      
      |- (phi SUNTIL
          (\t0.
             ?q.
               Phi_I (q t0) /\ (!t. Phi_R (i (t + t0),q (t + t0))) /\
               ?t1. !t2. Psi (i (t1 + (t2 + t0)),q (t1 + (t2 + t0)))))
           t0 <=>
         ?p q.
           (if p t0 then Phi_I (q t0) else q t0 = c) /\
           (!t.
              ~p (t + t0) /\ (q (t + t0) = c) /\ phi (t + t0) /\
              ~p (t + (t0 + 1)) /\ (q (t + (t0 + 1)) = c) \/
              ~p (t + t0) /\ (q (t + t0) = c) /\ phi (t + t0) /\
              p (t + (t0 + 1)) /\ Phi_I (q (t + (t0 + 1))) \/
              p (t + t0) /\ Phi_R (i (t + t0),q (t + t0)) /\
              p (t + (t0 + 1))) /\
           ?t1.
             !t2.
               p (t1 + (t2 + t0)) /\
               Psi (i (t1 + (t2 + t0)),q (t1 + (t2 + t0)))
   
   [CO_BUECHI_SWHEN_CLOSURE]  Theorem
      
      |- ((\t0.
             ?q.
               Phi_I (q t0) /\ (!t. Phi_R (i (t + t0),q (t + t0))) /\
               ?t1. !t2. Psi (i (t1 + (t2 + t0)),q (t1 + (t2 + t0)))) SWHEN
          phi) t0 <=>
         ?p1 p2 q.
           (~p1 t0 /\ ~p2 t0 /\ (q t0 = c) \/
            p1 t0 /\ ~p2 t0 /\ Phi_I (q t0)) /\
           (!t.
              ~p1 (t + t0) /\ ~p2 (t + t0) /\ (q (t + t0) = c) /\
              ~phi (t + t0) /\ ~p1 (t + (t0 + 1)) /\ ~p2 (t + (t0 + 1)) /\
              (q (t + (t0 + 1)) = c) \/
              ~p1 (t + t0) /\ ~p2 (t + t0) /\ (q (t + t0) = c) /\
              ~phi (t + t0) /\ p1 (t + (t0 + 1)) /\ ~p2 (t + (t0 + 1)) /\
              Phi_I (q (t + (t0 + 1))) \/
              p1 (t + t0) /\ ~p2 (t + t0) /\ phi (t + t0) /\
              Phi_I (q (t + t0)) /\ Phi_R (i (t + t0),q (t + t0)) /\
              p1 (t + (t0 + 1)) /\ p2 (t + (t0 + 1)) \/
              p1 (t + t0) /\ p2 (t + t0) /\
              Phi_R (i (t + t0),q (t + t0)) /\ p1 (t + (t0 + 1)) /\
              p2 (t + (t0 + 1))) /\
           ?t1.
             !t2.
               p1 (t1 + (t2 + t0)) /\
               Psi (i (t1 + (t2 + t0)),q (t1 + (t2 + t0)))
   
   [CO_BUECHI_UNTIL_CLOSURE]  Theorem
      
      |- (phi UNTIL
          (\t0.
             ?q.
               Phi_I (q t0) /\ (!t. Phi_R (i (t + t0),q (t + t0))) /\
               ?t1. !t2. Psi (i (t1 + (t2 + t0)),q (t1 + (t2 + t0)))))
           t0 <=>
         ?p q.
           (if p t0 then Phi_I (q t0) else q t0 = c) /\
           (!t.
              ~p (t + t0) /\ (q (t + t0) = c) /\ phi (t + t0) /\
              ~p (t + (t0 + 1)) /\ (q (t + (t0 + 1)) = c) \/
              ~p (t + t0) /\ (q (t + t0) = c) /\ phi (t + t0) /\
              p (t + (t0 + 1)) /\ Phi_I (q (t + (t0 + 1))) \/
              p (t + t0) /\ Phi_R (i (t + t0),q (t + t0)) /\
              p (t + (t0 + 1))) /\
           ?t1.
             !t2.
               ~p (t1 + (t2 + t0)) \/
               Psi (i (t1 + (t2 + t0)),q (t1 + (t2 + t0)))
   
   [CO_BUECHI_WHEN_CLOSURE]  Theorem
      
      |- ((\t0.
             ?q.
               Phi_I (q t0) /\ (!t. Phi_R (i (t + t0),q (t + t0))) /\
               ?t1. !t2. Psi (i (t1 + (t2 + t0)),q (t1 + (t2 + t0)))) WHEN
          phi) t0 <=>
         ?p1 p2 q.
           (~p1 t0 /\ ~p2 t0 /\ (q t0 = c) \/
            p1 t0 /\ ~p2 t0 /\ Phi_I (q t0)) /\
           (!t.
              ~p1 (t + t0) /\ ~p2 (t + t0) /\ (q (t + t0) = c) /\
              ~phi (t + t0) /\ ~p1 (t + (t0 + 1)) /\ ~p2 (t + (t0 + 1)) /\
              (q (t + (t0 + 1)) = c) \/
              ~p1 (t + t0) /\ ~p2 (t + t0) /\ (q (t + t0) = c) /\
              ~phi (t + t0) /\ p1 (t + (t0 + 1)) /\ ~p2 (t + (t0 + 1)) /\
              Phi_I (q (t + (t0 + 1))) \/
              p1 (t + t0) /\ ~p2 (t + t0) /\ phi (t + t0) /\
              Phi_I (q (t + t0)) /\ Phi_R (i (t + t0),q (t + t0)) /\
              p1 (t + (t0 + 1)) /\ p2 (t + (t0 + 1)) \/
              p1 (t + t0) /\ p2 (t + t0) /\
              Phi_R (i (t + t0),q (t + t0)) /\ p1 (t + (t0 + 1)) /\
              p2 (t + (t0 + 1))) /\
           ?t1.
             !t2.
               ~p1 (t1 + (t2 + t0)) \/
               Psi (i (t1 + (t2 + t0)),q (t1 + (t2 + t0)))
   
   [DET_OMEGA_EXISTS_FORALL_THEOREM]  Theorem
      
      |- (?q.
            (q t0 = InitVal) /\
            (!t. q (t + (t0 + 1)) = TransRel (i (t + t0),q (t + t0))) /\
            Accept (i,(\t. q (t + t0)))) <=>
         !q.
           (q t0 = InitVal) /\
           (!t. q (t + (t0 + 1)) = TransRel (i (t + t0),q (t + t0))) ==>
           Accept (i,(\t. q (t + t0)))
   
   [ELGOT1_THM]  Theorem
      
      |- !PHI. (?x. !p. PHI p x) <=> ?q. !p x. ?z. (q x ==> PHI p x) /\ q z
   
   [ELGOT2_THM]  Theorem
      
      |- !PHI. (!x. ?p. PHI p x) <=> !q. ?p x. !z. q z ==> PHI p x /\ q x
   
   [ELGOT_LEMMA]  Theorem
      
      |- !PHI.
           (?x. !p. PHI p x) <=> ?q. (!x. q x ==> !p. PHI p x) /\ ?z. q z
   
   [EQUALITY_THM]  Theorem
      
      |- !x y. (x = y) <=> !P. P x <=> P y
   
   [EXISTS_FORALL_THM]  Theorem
      
      |- !P. (?t1. !t2. P (t1 + t2)) <=> ?t1. !t2. t1 < t2 ==> P t2
   
   [FORALL_EXISTS_THM]  Theorem
      
      |- !P. (!t1. ?t2. P (t1 + t2)) <=> !t1. ?t2. t1 < t2 /\ P t2
   
   [LESS_THM]  Theorem
      
      |- !x y. x < y <=> ?P. P x /\ ~P y /\ !z. P (SUC z) ==> P z
   
   [NEG_DET_AUTOMATA]  Theorem
      
      |- ~(?q.
             (q t0 = InitVal) /\
             (!t. q (t + (t0 + 1)) = TransRel (i (t + t0),q (t + t0))) /\
             Accept (i,(\t. q (t + t0)))) <=>
         ?q.
           (q t0 = InitVal) /\
           (!t. q (t + (t0 + 1)) = TransRel (i (t + t0),q (t + t0))) /\
           ~Accept (i,(\t. q (t + t0)))
   
   [NEXT_AS_CO_BUECHI]  Theorem
      
      |- NEXT a t0 <=>
         ?p q.
           (~p t0 /\ ~q t0) /\
           (!t.
              ~p (t + t0) /\ ~q (t + t0) /\ p (t + (1 + t0)) /\
              ~q (t + (1 + t0)) \/
              p (t + t0) /\ ~q (t + t0) /\ a (t + t0) /\
              p (t + (1 + t0)) /\ q (t + (1 + t0)) \/
              p (t + t0) /\ q (t + t0) /\ p (t + (1 + t0)) /\
              q (t + (1 + t0))) /\ ?t1. !t2. q (t1 + (t2 + t0))
   
   [OMEGA_CONJ_CLOSURE]  Theorem
      
      |- (?q1.
            Phi_I1 (q1 t0) /\ (!t. Phi_R1 (i (t + t0),q1 (t + t0))) /\
            Psi1 (i,q1)) /\
         (?q2.
            Phi_I2 (q2 t0) /\ (!t. Phi_R2 (i (t + t0),q2 (t + t0))) /\
            Psi2 (i,q2)) <=>
         ?q1 q2.
           (Phi_I1 (q1 t0) /\ Phi_I2 (q2 t0)) /\
           (!t.
              Phi_R1 (i (t + t0),q1 (t + t0)) /\
              Phi_R2 (i (t + t0),q2 (t + t0))) /\ Psi1 (i,q1) /\
           Psi2 (i,q2)
   
   [OMEGA_DISJ_CLOSURE]  Theorem
      
      |- (?q1.
            Phi_I1 (q1 t0) /\ (!t. Phi_R1 (i (t + t0),q1 (t + t0))) /\
            Psi1 (i,q1)) \/
         (?q2.
            Phi_I2 (q2 t0) /\ (!t. Phi_R2 (i (t + t0),q2 (t + t0))) /\
            Psi2 (i,q2)) <=>
         ?p q1 q2.
           (~p t0 /\ Phi_I1 (q1 t0) \/ p t0 /\ Phi_I2 (q2 t0)) /\
           (!t.
              ~p (t + t0) /\ Phi_R1 (i (t + t0),q1 (t + t0)) /\
              ~p (t + (t0 + 1)) \/
              p (t + t0) /\ Phi_R2 (i (t + t0),q2 (t + t0)) /\
              p (t + (t0 + 1))) /\
           (~p t0 /\ Psi1 (i,q1) \/ p t0 /\ Psi2 (i,q2))
   
   [SBEFORE_AS_CO_BUECHI]  Theorem
      
      |- (a SBEFORE b) t0 <=>
         ?q.
           ~q t0 /\
           (!t.
              ~q (t + t0) /\ ~a (t + t0) /\ ~b (t + t0) /\
              ~q (t + (1 + t0)) \/
              ~q (t + t0) /\ a (t + t0) /\ ~b (t + t0) /\
              q (t + (1 + t0)) \/ q (t + t0) /\ q (t + (1 + t0))) /\
           ?t1. !t2. q (t1 + (t2 + t0))
   
   [SUNTIL_AS_CO_BUECHI]  Theorem
      
      |- (a SUNTIL b) t0 <=>
         ?q.
           ~q t0 /\
           (!t.
              ~q (t + t0) /\ a (t + t0) /\ ~b (t + t0) /\
              ~q (t + (1 + t0)) \/
              ~q (t + t0) /\ b (t + t0) /\ q (t + (1 + t0)) \/
              q (t + t0) /\ q (t + (1 + t0))) /\
           ?t1. !t2. q (t1 + (t2 + t0))
   
   [SWHEN_AS_CO_BUECHI]  Theorem
      
      |- (a SWHEN b) t0 <=>
         ?q.
           ~q t0 /\
           (!t.
              ~q (t + t0) /\ ~b (t + t0) /\ ~q (t + (1 + t0)) \/
              ~q (t + t0) /\ a (t + t0) /\ b (t + t0) /\
              q (t + (1 + t0)) \/ q (t + t0) /\ q (t + (1 + t0))) /\
           ?t1. !t2. q (t1 + (t2 + t0))
   
   [TEMP_OPS_DEFS_TO_OMEGA]  Theorem
      
      |- ((l = NEXT a) <=> T /\ (!t. l t <=> a (SUC t)) /\ T) /\
         ((l = ALWAYS a) <=>
          T /\ (!t. l t <=> a t /\ l (SUC t)) /\
          !t1. ?t2. a (t1 + t2) ==> l (t1 + t2)) /\
         ((l = EVENTUAL a) <=>
          T /\ (!t. l t <=> a t \/ l (SUC t)) /\
          !t1. ?t2. l (t1 + t2) ==> a (t1 + t2)) /\
         ((l = a SUNTIL b) <=>
          T /\ (!t. l t <=> ~b t ==> a t /\ l (SUC t)) /\
          !t1. ?t2. l (t1 + t2) ==> ~a (t1 + t2) \/ b (t1 + t2)) /\
         ((l = a SWHEN b) <=>
          T /\ (!t. l t <=> if b t then a t else l (SUC t)) /\
          !t1. ?t2. l (t1 + t2) ==> b (t1 + t2)) /\
         ((l = a SBEFORE b) <=>
          T /\ (!t. l t <=> ~b t /\ (a t \/ l (SUC t))) /\
          !t1. ?t2. l (t1 + t2) ==> a (t1 + t2) \/ b (t1 + t2)) /\
         ((l = a UNTIL b) <=>
          T /\ (!t. l t <=> ~b t ==> a t /\ l (SUC t)) /\
          !t1. ?t2. ~l (t1 + t2) ==> ~a (t1 + t2) \/ b (t1 + t2)) /\
         ((l = a WHEN b) <=>
          T /\ (!t. l t <=> if b t then a t else l (SUC t)) /\
          !t1. ?t2. l (t1 + t2) \/ b (t1 + t2)) /\
         ((l = a BEFORE b) <=>
          T /\ (!t. l t <=> ~b t /\ (a t \/ l (SUC t))) /\
          !t1. ?t2. ~l (t1 + t2) ==> a (t1 + t2) \/ b (t1 + t2)) /\
         ((l = PNEXT a) <=> (l 0 <=> T) /\ (!t. l (SUC t) <=> a t) /\ T) /\
         ((l = PSNEXT a) <=>
          (l 0 <=> F) /\ (!t. l (SUC t) <=> a t) /\ T) /\
         ((l = PNEXT (PALWAYS a)) <=>
          (l 0 <=> T) /\ (!t. l (SUC t) <=> a t /\ l t) /\ T) /\
         ((l = PSNEXT (PEVENTUAL a)) <=>
          (l 0 <=> F) /\ (!t. l (SUC t) <=> a t \/ l t) /\ T) /\
         ((l = PSNEXT (a PSUNTIL b)) <=>
          (l 0 <=> F) /\ (!t. l (SUC t) <=> b t \/ a t /\ l t) /\ T) /\
         ((l = PSNEXT (a PSWHEN b)) <=>
          (l 0 <=> F) /\ (!t. l (SUC t) <=> a t /\ b t \/ ~b t /\ l t) /\
          T) /\
         ((l = PSNEXT (a PSBEFORE b)) <=>
          (l 0 <=> F) /\ (!t. l (SUC t) <=> ~b t /\ (a t \/ l t)) /\ T) /\
         ((l = PNEXT (a PUNTIL b)) <=>
          (l 0 <=> T) /\ (!t. l (SUC t) <=> b t \/ a t /\ l t) /\ T) /\
         ((l = PNEXT (a PWHEN b)) <=>
          (l 0 <=> T) /\ (!t. l (SUC t) <=> a t /\ b t \/ ~b t /\ l t) /\
          T) /\
         ((l = PNEXT (a PBEFORE b)) <=>
          (l 0 <=> T) /\ (!t. l (SUC t) <=> ~b t /\ (a t \/ l t)) /\ T)
   
   [UNTIL_AS_CO_BUECHI]  Theorem
      
      |- (a UNTIL b) t0 <=>
         ?q.
           ~q t0 /\
           (!t.
              ~q (t + t0) /\ a (t + t0) /\ ~b (t + t0) /\
              ~q (t + (1 + t0)) \/
              ~q (t + t0) /\ b (t + t0) /\ q (t + (1 + t0)) \/
              q (t + t0) /\ q (t + (1 + t0))) /\
           ?t1. !t2. ~q (t1 + (t2 + t0)) \/ q (t1 + (t2 + t0))
   
   [WHEN_AS_CO_BUECHI]  Theorem
      
      |- (a WHEN b) t0 <=>
         ?q.
           ~q t0 /\
           (!t.
              ~q (t + t0) /\ ~b (t + t0) /\ ~q (t + (1 + t0)) \/
              ~q (t + t0) /\ a (t + t0) /\ b (t + t0) /\
              q (t + (1 + t0)) \/ q (t + t0) /\ q (t + (1 + t0))) /\
           ?t1. !t2. ~q (t1 + (t2 + t0)) \/ q (t1 + (t2 + t0))
   
   
*)
end
