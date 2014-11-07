open HolKernel Parse boolLib bossLib;

open stringTheory

val _ = new_theory "stringDict";

(* completely made up; probably bogus *)
val sdhash_def = Define`
  (sdhash acc [] = acc MOD 1009) /\
  (sdhash acc (c :: cs) = sdhash (acc + 3 * ORD c) cs)
`


val _ = export_theory();
