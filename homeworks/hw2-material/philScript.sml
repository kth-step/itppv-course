open HolKernel Parse boolLib bossLib;

val _ = new_theory "phil";

val _ = Datatype `Philosopher = diogenes | platon | euklid`;
val Philosopher_nchotomy = DB.fetch "-" "Philosopher_nchotomy";
val Philosopher_distinct = DB.fetch "-" "Philosopher_distinct";


val PHIL_KNOWLEDGE = new_specification ("PHIL_KNOWLEDGE", ["At", "Sp", "W", "B"],
prove (``?At Sp W B. 
    (!p. (Sp p ==> B p)) /\
    (!p. (At p ==> W p)) /\
    (!p. ~(Sp p) \/ ~(At p)) /\
    (!p. (Sp p) \/ (At p)) /\
    ((Sp platon) ==> ~(W diogenes)) /\
    ((Sp euklid) ==> ~(B diogenes)) /\
    ((At diogenes) ==> ~(B euklid)) /\
    ((At platon) ==> ~(W euklid))``,

Q.EXISTS_TAC `\p. Philosopher_CASE p F F T` THEN
Q.EXISTS_TAC `\p. Philosopher_CASE p T T F` THEN
Q.EXISTS_TAC `\p. Philosopher_CASE p F T T` THEN
Q.EXISTS_TAC `\p. Philosopher_CASE p T T F` THEN
SIMP_TAC (srw_ss()++DatatypeSimps.expand_type_quants_ss [``:Philosopher``]) []));


val PHIL_KNOWLEDGE_a = store_thm ("PHIL_KNOWLEDGE_a", ``!p. Sp p ==> B p``,
  REWRITE_TAC[PHIL_KNOWLEDGE]);

val PHIL_KNOWLEDGE_b = store_thm ("PHIL_KNOWLEDGE_b", ``!p. At p ==> W p``,
  REWRITE_TAC[PHIL_KNOWLEDGE]);

val PHIL_KNOWLEDGE_c = store_thm ("PHIL_KNOWLEDGE_c", ``!p. ~(Sp p) \/ ~(At p)``,
  REWRITE_TAC[PHIL_KNOWLEDGE]);

val PHIL_KNOWLEDGE_c1 = store_thm ("PHIL_KNOWLEDGE_c1", ``!p. Sp p ==> ~(At p)``,
  PROVE_TAC[PHIL_KNOWLEDGE]);

val PHIL_KNOWLEDGE_c2 = store_thm ("PHIL_KNOWLEDGE_c2", ``!p. At p ==> ~(Sp p)``,
  PROVE_TAC[PHIL_KNOWLEDGE]);

val PHIL_KNOWLEDGE_d = store_thm ("PHIL_KNOWLEDGE_d", ``!p. (Sp p) \/ (At p)``,
  REWRITE_TAC[PHIL_KNOWLEDGE]);

val PHIL_KNOWLEDGE_d1 = store_thm ("PHIL_KNOWLEDGE_d1", ``!p. ~(Sp p) ==> At p``,
  PROVE_TAC[PHIL_KNOWLEDGE]);

val PHIL_KNOWLEDGE_d2 = store_thm ("PHIL_KNOWLEDGE_d2", ``!p. ~(At p) ==> Sp p``,
  PROVE_TAC[PHIL_KNOWLEDGE]);

val PHIL_KNOWLEDGE_e = store_thm ("PHIL_KNOWLEDGE_e", ``(Sp platon) ==> ~(W diogenes)``,
  REWRITE_TAC[PHIL_KNOWLEDGE]);

val PHIL_KNOWLEDGE_f = store_thm ("PHIL_KNOWLEDGE_f", ``(Sp euklid) ==> ~(B diogenes)``,
  REWRITE_TAC[PHIL_KNOWLEDGE]);

val PHIL_KNOWLEDGE_g = store_thm ("PHIL_KNOWLEDGE_g", ``(At diogenes) ==> ~(B euklid)``,
  REWRITE_TAC[PHIL_KNOWLEDGE]);

val PHIL_KNOWLEDGE_h = store_thm ("PHIL_KNOWLEDGE_h", ``(At platon) ==> ~(W euklid)``,
  REWRITE_TAC[PHIL_KNOWLEDGE]);

val _ = export_theory();

