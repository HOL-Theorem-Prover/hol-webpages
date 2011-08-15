signature tfl_examplesTheory =
sig
  type thm = Thm.thm
  
  (*  Definitions  *)
    val AND_primitive_def : thm
    val Divide_AUX_def : thm
    val Divide_primitive_def : thm
    val Ffact_def : thm
    val Ffib_primitive_def : thm
    val Fib_primitive_def : thm
    val Map2_primitive_def : thm
    val Mmap2_primitive_def : thm
    val Qsort_primitive_def : thm
    val acc1_primitive_def : thm
    val div_primitive_def : thm
    val fact_cond_primitive_def : thm
    val fact_pattern_def : thm
    val fin_primitive_def : thm
    val foo_primitive_def : thm
    val gcd_primitive_def : thm
    val map2_primitive_def : thm
    val nested_if_primitive_def : thm
    val qsort_primitive_def : thm
    val sorted_primitive_def : thm
    val variant_primitive_def : thm
    val vary1_primitive_def : thm
    val vary2_primitive_def : thm
    val vary_primitive_def : thm
  
  (*  Theorems  *)
    val AND_def : thm
    val AND_ind : thm
    val Divide_def : thm
    val Divide_ind : thm
    val Ffib_def : thm
    val Ffib_ind : thm
    val Fib_def : thm
    val Fib_ind : thm
    val Map2_def : thm
    val Map2_ind : thm
    val Mmap2_def : thm
    val Mmap2_ind : thm
    val div_def : thm
    val div_ind : thm
    val fact_cond_def : thm
    val fact_cond_ind : thm
    val fin_def : thm
    val fin_ind : thm
    val foo_def : thm
    val foo_ind : thm
    val gcd_def : thm
    val gcd_ind : thm
    val map2_def : thm
    val map2_ind : thm
    val nested_if_def : thm
    val nested_if_ind : thm
    val sorted_def : thm
    val sorted_ind : thm
  
  val tfl_examples_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [list] Parent theory of "tfl_examples"
   
   [AND_primitive_def]  Definition
      
      |- AND =
         WFREC (@R. WF R ∧ ∀t h y. R (y ∧ h,t) (y,h::t))
           (λAND a.
              case a of (x,[]) -> I x || (x,h::t) -> I (AND (x ∧ h,t)))
   
   [Divide_AUX_def]  Definition
      
      |- ∀R.
           Divide_aux R =
           WFREC R
             (λDivide a.
                case a of
                   (0,x) -> I (0,0)
                || (SUC x',x) ->
                     I
                       (let q = FST (Divide (x',x)) in
                        let r = SND (Divide (x',x))
                        in
                          if x ≤ SUC r then (SUC q,0) else (q,SUC r)))
   
   [Divide_primitive_def]  Definition
      
      |- Divide =
         Divide_aux
           (@R.
              WF R ∧
              (∀y x q.
                 (q = FST (Divide_aux R (x,y))) ⇒ R (x,y) (SUC x,y)) ∧
              ∀y x. R (x,y) (SUC x,y))
   
   [Ffact_def]  Definition
      
      |- ∀x. Ffact (SUC x) = Ffact x * SUC x
   
   [Ffib_primitive_def]  Definition
      
      |- Ffib =
         WFREC (@R. WF R ∧ ∀x. R x (SUC (SUC x)))
           (λFfib a.
              case a of
                 0 -> ARB
              || SUC 0 -> ARB
              || SUC (SUC x) -> I (Ffib x + Fib (SUC x)))
   
   [Fib_primitive_def]  Definition
      
      |- Fib =
         WFREC
           (@R.
              WF R ∧ (∀x. R x (SUC (SUC x))) ∧ ∀x. R (SUC x) (SUC (SUC x)))
           (λFib a.
              case a of
                 0 -> I 1
              || SUC 0 -> I 1
              || SUC (SUC x) -> I (Fib x + Fib (SUC x)))
   
   [Map2_primitive_def]  Definition
      
      |- Map2 =
         WFREC
           (@R. WF R ∧ ∀h2 h1 f t2 t1. R ((t1,t2),f) ((h1::t1,h2::t2),f))
           (λMap2 a.
              case a of
                 (([],L),f) -> I []
              || ((h::t,[]),f) -> I []
              || ((h::t,h2::t2),f) -> I (f h h2::Map2 ((t,t2),f)))
   
   [Mmap2_primitive_def]  Definition
      
      |- Mmap2 =
         WFREC
           (@R. WF R ∧ ∀h2 h1 t2 t1 fn. R (fn,t1,t2) (fn,h1::t1,h2::t2))
           (λMmap2 a.
              case a of
                 (fn,[],[]) -> I []
              || (fn,[],v6::v7) -> ARB
              || (fn,h1::t1,[]) -> ARB
              || (fn,h1::t1,h2::t2) -> I (fn h1 h2::Mmap2 (fn,t1,t2)))
   
   [Qsort_primitive_def]  Definition
      
      |- Qsort =
         WFREC
           (@R.
              WF R ∧
              (∀rst x ord L1 L2 P lower upper.
                 (((L1,L2),P) =
                  ((filter ($~ o ord x) rst,filter (ord x) rst),x,rst)) ∧
                 ((lower,upper) = ((ord,L1),ord,L2)) ⇒
                 R upper (ord,x::rst)) ∧
              ∀rst x ord L1 L2 P lower upper.
                (((L1,L2),P) =
                 ((filter ($~ o ord x) rst,filter (ord x) rst),x,rst)) ∧
                ((lower,upper) = ((ord,L1),ord,L2)) ⇒
                R lower (ord,x::rst))
           (λQsort a.
              case a of
                 (ord,[]) -> I []
              || (ord,x::rst) ->
                   I
                     (let ((L1,L2),P) =
                            ((filter ($~ o ord x) rst,filter (ord x) rst),
                             x,rst)
                      in
                      let (lower,upper) = ((ord,L1),ord,L2)
                      in
                        Qsort lower ++ [x] ++ Qsort upper))
   
   [acc1_primitive_def]  Definition
      
      |- acc1 =
         WFREC
           (@R.
              WF R ∧
              (∀xss s zs p f xs.
                 xs ≠ [] ⇒
                 R ((f,p),zs,s,xss ++ [xs],[],[]) ((f,p),[],s,xss,zs,xs)) ∧
              ∀xss ys p xs y zs f s s' zs'' xs'.
                (s' = s) ∧ (zs'' = if f s' then [] else zs ++ [y]) ∧
                (xs' = if f s' then xs ++ zs ++ [y] else xs) ⇒
                R ((f,p),ys,s',xss,zs'',xs') ((f,p),y::ys,s,xss,zs,xs))
           (λacc1 a.
              case a of
                 ((f,p),[],s,xss,zs,xs) ->
                   I
                     (if xs = [] then
                        (xss,zs)
                      else
                        acc1 ((f,p),zs,s,xss ++ [xs],[],[]))
              || ((f,p),y::ys,s',xss',zs',xs') ->
                   I
                     (let s' = s' in
                      let zs'' = if f s' then [] else zs' ++ [y] in
                      let xs' = if f s' then xs' ++ zs' ++ [y] else xs'
                      in
                        acc1 ((f,p),ys,s',xss',zs'',xs')))
   
   [div_primitive_def]  Definition
      
      |- Div =
         WFREC (@R. WF R ∧ ∀y x. R (x,y) (SUC x,y))
           (λDiv a.
              case a of
                 (0,x) -> I (0,0)
              || (SUC x',x) ->
                   I
                     (let (q,r) = Div (x',x) in
                      let (s,t) = (x',x)
                      in
                        if x ≤ SUC r then (SUC q,0) else (q,SUC r)))
   
   [fact_cond_primitive_def]  Definition
      
      |- fact =
         WFREC (@R. WF R ∧ ∀x. x ≠ 0 ⇒ R (x − 1) x)
           (λfact x. I (if x = 0 then 1 else x * fact (x − 1)))
   
   [fact_pattern_def]  Definition
      
      |- (Fact 0 = 1) ∧ ∀x. Fact (SUC x) = Fact x * SUC x
   
   [fin_primitive_def]  Definition
      
      |- fin =
         WFREC (@R'. WF R')
           (λfin a.
              case a of
                 (R,[]) -> ARB
              || (R,[x]) -> I T
              || (R,x::v4::v5) -> ARB)
   
   [foo_primitive_def]  Definition
      
      |- foo =
         WFREC (@R. WF R ∧ ∀x. (λx. x) x ⇒ R F x)
           (λfoo x. I (if (λx. x) x then foo F else ()))
   
   [gcd_primitive_def]  Definition
      
      |- gcd =
         WFREC
           (@R.
              WF R ∧ (∀x y. ¬(y ≤ x) ⇒ R (SUC x,y − x) (SUC x,SUC y)) ∧
              ∀x y. y ≤ x ⇒ R (x − y,SUC y) (SUC x,SUC y))
           (λgcd a.
              case a of
                 (0,y) -> I y
              || (SUC x,0) -> I (SUC x)
              || (SUC x,SUC y') ->
                   I
                     (if y' ≤ x then
                        gcd (x − y',SUC y')
                      else
                        gcd (SUC x,y' − x)))
   
   [map2_primitive_def]  Definition
      
      |- map2 =
         WFREC (@R. WF R ∧ ∀h2 h1 t2 t1 f. R (f,t1,t2) (f,h1::t1,h2::t2))
           (λmap2 a.
              case a of
                 (f,[],L) -> I []
              || (f,h::t,[]) -> I []
              || (f,h::t,h2::t2) -> I (f h h2::map2 (f,t,t2)))
   
   [nested_if_primitive_def]  Definition
      
      |- f =
         WFREC (@R. WF R ∧ ∀x y. (y = x) ∧ ¬(0 < y) ⇒ R (x,y) (SUC x,y))
           (λf a.
              case a of
                 (0,x) -> I (0,0)
              || (SUC x',x) ->
                   I
                     (if x = x' then
                        if 0 < x then (0,0) else f (x',x)
                      else
                        (x',x)))
   
   [qsort_primitive_def]  Definition
      
      |- qsort =
         WFREC
           (@R.
              WF R ∧
              (∀rst x ord. R (ord,filter (ord x) rst) (ord,x::rst)) ∧
              ∀rst x ord. R (ord,filter ($~ o ord x) rst) (ord,x::rst))
           (λqsort a.
              case a of
                 (ord,[]) -> I []
              || (ord,x::rst) ->
                   I
                     (qsort (ord,filter ($~ o ord x) rst) ++ [x] ++
                      qsort (ord,filter (ord x) rst)))
   
   [sorted_primitive_def]  Definition
      
      |- sorted =
         WFREC (@R'. WF R' ∧ ∀x rst y R. R' (R,y::rst) (R,x::y::rst))
           (λsorted a.
              case a of
                 (R,[]) -> I T
              || (R,[x]) -> I T
              || (R,x::y::rst) -> I (R x y ∧ sorted (R,y::rst)))
   
   [variant_primitive_def]  Definition
      
      |- variant =
         WFREC (@R. WF R ∧ ∀L x. mem x L ⇒ R (SUC x,L) (x,L))
           (λvariant a.
              case a of
                 (x,L) -> I (if mem x L then variant (SUC x,L) else x))
   
   [vary1_primitive_def]  Definition
      
      |- vary1 =
         WFREC
           (@R.
              WF R ∧
              ∀L x x' x''.
                mem x L ∧ (x' = SUC x) ∧ (x'' = x') ⇒ R (x'',L) (x,L))
           (λvary1 a.
              case a of
                 (x,L) ->
                   I
                     (if mem x L then
                        (let x = SUC x in let x = x in vary1 (x,L))
                      else
                        x))
   
   [vary2_primitive_def]  Definition
      
      |- vary2 =
         WFREC
           (@R.
              WF R ∧
              ∀L x x' y x'' y'.
                mem x L ∧ ((x',y) = (SUC x,x)) ∧ ((x'',y') = (x',y)) ⇒
                R (x'',L) (x,L))
           (λvary2 a.
              case a of
                 (x,L) ->
                   I
                     (if mem x L then
                        (let (x,y) = (SUC x,x) in
                         let (x,y) = (x,y)
                         in
                           vary2 (x,L))
                      else
                        x))
   
   [vary_primitive_def]  Definition
      
      |- vary =
         WFREC
           (@R. WF R ∧ ∀L x x'. mem x L ∧ (x' = SUC x) ⇒ R (x',L) (x,L))
           (λvary a.
              case a of
                 (x,L) ->
                   I
                     (if mem x L then
                        (let x = SUC x in vary (x,L))
                      else
                        x))
   
   [AND_def]  Theorem
      
      |- (∀x. AND (x,[]) ⇔ x) ∧ ∀y t h. AND (y,h::t) ⇔ AND (y ∧ h,t)
   
   [AND_ind]  Theorem
      
      |- ∀P.
           (∀x. P (x,[])) ∧ (∀y h t. P (y ∧ h,t) ⇒ P (y,h::t)) ⇒
           ∀v v1. P (v,v1)
   
   [Divide_def]  Theorem
      
      |- (∀x. Divide (0,x) = (0,0)) ∧
         ∀y x.
           Divide (SUC x,y) =
           (let q = FST (Divide (x,y)) in
            let r = SND (Divide (x,y))
            in
              if y ≤ SUC r then (SUC q,0) else (q,SUC r))
   
   [Divide_ind]  Theorem
      
      |- ∀P.
           (∀x. P (0,x)) ∧
           (∀x y.
              (∀q. (q = FST (Divide (x,y))) ⇒ P (x,y)) ∧ P (x,y) ⇒
              P (SUC x,y)) ⇒
           ∀v v1. P (v,v1)
   
   [Ffib_def]  Theorem
      
      |- ∀x. Ffib (SUC (SUC x)) = Ffib x + Fib (SUC x)
   
   [Ffib_ind]  Theorem
      
      |- ∀P. (∀x. P x ⇒ P (SUC (SUC x))) ∧ P 0 ∧ P (SUC 0) ⇒ ∀v. P v
   
   [Fib_def]  Theorem
      
      |- (Fib 0 = 1) ∧ (Fib (SUC 0) = 1) ∧
         ∀x. Fib (SUC (SUC x)) = Fib x + Fib (SUC x)
   
   [Fib_ind]  Theorem
      
      |- ∀P.
           P 0 ∧ P (SUC 0) ∧ (∀x. P x ∧ P (SUC x) ⇒ P (SUC (SUC x))) ⇒
           ∀v. P v
   
   [Map2_def]  Theorem
      
      |- (∀f L. Map2 (([],L),f) = []) ∧ (∀t h f. Map2 ((h::t,[]),f) = []) ∧
         ∀t2 t1 h2 h1 f.
           Map2 ((h1::t1,h2::t2),f) = f h1 h2::Map2 ((t1,t2),f)
   
   [Map2_ind]  Theorem
      
      |- ∀P.
           (∀L f. P (([],L),f)) ∧ (∀h t f. P ((h::t,[]),f)) ∧
           (∀h1 t1 h2 t2 f. P ((t1,t2),f) ⇒ P ((h1::t1,h2::t2),f)) ⇒
           ∀v v1 v2. P ((v,v1),v2)
   
   [Mmap2_def]  Theorem
      
      |- (∀fn. Mmap2 (fn,[],[]) = []) ∧
         ∀t2 t1 h2 h1 fn.
           Mmap2 (fn,h1::t1,h2::t2) = fn h1 h2::Mmap2 (fn,t1,t2)
   
   [Mmap2_ind]  Theorem
      
      |- ∀P.
           (∀fn. P (fn,[],[])) ∧
           (∀fn h1 t1 h2 t2. P (fn,t1,t2) ⇒ P (fn,h1::t1,h2::t2)) ∧
           (∀fn v8 v9. P (fn,[],v8::v9)) ∧ (∀fn h1 t1. P (fn,h1::t1,[])) ⇒
           ∀v v1 v2. P (v,v1,v2)
   
   [div_def]  Theorem
      
      |- (∀x. Div (0,x) = (0,0)) ∧
         ∀y x.
           Div (SUC x,y) =
           (let (q,r) = Div (x,y) in
            let (s,t) = (x,y)
            in
              if y ≤ SUC r then (SUC q,0) else (q,SUC r))
   
   [div_ind]  Theorem
      
      |- ∀P.
           (∀x. P (0,x)) ∧ (∀x y. P (x,y) ⇒ P (SUC x,y)) ⇒ ∀v v1. P (v,v1)
   
   [fact_cond_def]  Theorem
      
      |- ∀x. fact x = if x = 0 then 1 else x * fact (x − 1)
   
   [fact_cond_ind]  Theorem
      
      |- ∀P. (∀x. (x ≠ 0 ⇒ P (x − 1)) ⇒ P x) ⇒ ∀v. P v
   
   [fin_def]  Theorem
      
      |- fin (R,[x]) ⇔ T
   
   [fin_ind]  Theorem
      
      |- ∀P.
           (∀R x. P (R,[x])) ∧ (∀R. P (R,[])) ∧
           (∀R x v6 v7. P (R,x::v6::v7)) ⇒
           ∀v v1. P (v,v1)
   
   [foo_def]  Theorem
      
      |- foo x = if (λx. x) x then foo F else ()
   
   [foo_ind]  Theorem
      
      |- ∀P. (∀x. ((λx. x) x ⇒ P F) ⇒ P x) ⇒ ∀v. P v
   
   [gcd_def]  Theorem
      
      |- (∀y. gcd (0,y) = y) ∧ (∀x. gcd (SUC x,0) = SUC x) ∧
         ∀y x.
           gcd (SUC x,SUC y) =
           if y ≤ x then gcd (x − y,SUC y) else gcd (SUC x,y − x)
   
   [gcd_ind]  Theorem
      
      |- ∀P.
           (∀y. P (0,y)) ∧ (∀x. P (SUC x,0)) ∧
           (∀x y.
              (¬(y ≤ x) ⇒ P (SUC x,y − x)) ∧ (y ≤ x ⇒ P (x − y,SUC y)) ⇒
              P (SUC x,SUC y)) ⇒
           ∀v v1. P (v,v1)
   
   [map2_def]  Theorem
      
      |- (∀f L. map2 (f,[],L) = []) ∧ (∀t h f. map2 (f,h::t,[]) = []) ∧
         ∀t2 t1 h2 h1 f. map2 (f,h1::t1,h2::t2) = f h1 h2::map2 (f,t1,t2)
   
   [map2_ind]  Theorem
      
      |- ∀P.
           (∀f L. P (f,[],L)) ∧ (∀f h t. P (f,h::t,[])) ∧
           (∀f h1 t1 h2 t2. P (f,t1,t2) ⇒ P (f,h1::t1,h2::t2)) ⇒
           ∀v v1 v2. P (v,v1,v2)
   
   [nested_if_def]  Theorem
      
      |- (∀x. f (0,x) = (0,0)) ∧
         ∀y x.
           f (SUC x,y) =
           if y = x then if 0 < y then (0,0) else f (x,y) else (x,y)
   
   [nested_if_ind]  Theorem
      
      |- ∀P.
           (∀x. P (0,x)) ∧
           (∀x y. ((y = x) ∧ ¬(0 < y) ⇒ P (x,y)) ⇒ P (SUC x,y)) ⇒
           ∀v v1. P (v,v1)
   
   [sorted_def]  Theorem
      
      |- (∀R. sorted (R,[]) ⇔ T) ∧ (∀x R. sorted (R,[x]) ⇔ T) ∧
         ∀y x rst R. sorted (R,x::y::rst) ⇔ R x y ∧ sorted (R,y::rst)
   
   [sorted_ind]  Theorem
      
      |- ∀P.
           (∀R. P (R,[])) ∧ (∀R x. P (R,[x])) ∧
           (∀R x y rst. P (R,y::rst) ⇒ P (R,x::y::rst)) ⇒
           ∀v v1. P (v,v1)
   
   
*)
end
