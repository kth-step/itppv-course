open HolKernel boolLib Parse bossLib;
open stringTheory listTheory finite_mapTheory;

val _ = new_theory "proof";

val clause_name = Define `clause_name (x:string) = T`;

val _ = type_abbrev("p", ``:bool``); (* atomic proposition *)
val _ = type_abbrev("l", ``:num``); (* proof entry label *)
val _ = type_abbrev("n", ``:num``); (* index variable (subscript) *)
val _ = Hol_datatype ` 
justification =  (* derivation justification *)
   justification_premise (* premise *)
 | justification_lem (* law of excluded middle *)
 | justification_copy of l (* copying *)
 | justification_andi of l => l (* conjunction introduction *)
 | justification_ande1 of l (* conjunction elimination *)
 | justification_ande2 of l (* conjunction elimination *)
 | justification_ori1 of l (* disjunction introduction *)
 | justification_ori2 of l (* disjunction introduction *)
 | justification_impe of l => l (* implication elimination *)
 | justification_nege of l => l (* negation elimination *)
 | justification_conte of l (* contradiction elimination *)
 | justification_negnegi of l (* double negation introduction *)
 | justification_negnege of l (* double negation elimination *)
 | justification_mt of l => l (* modus tollens *)
 | justification_impi of l => l (* implication introduction *)
 | justification_negi of l => l (* negation introduction *)
 | justification_ore of l => l => l => l => l (* disjunction elimination *)
 | justification_pbc of l => l (* proof by contraduction *)
`;
val _ = Hol_datatype ` 
prop =  (* proposition *)
   prop_p of p (* atomic *)
 | prop_neg of prop (* negation *)
 | prop_and of prop => prop (* conjunction *)
 | prop_or of prop => prop (* disjunction *)
 | prop_imp of prop => prop (* implication *)
 | prop_cont (* contradiction *)
`;
val _ = Hol_datatype ` 
reason = 
   reason_assumption
 | reason_justification of justification
`;
val _ = type_abbrev("proplist", ``:prop list``);
val _ = Hol_datatype ` 
derivation =  (* derivation in proof *)
   derivation_deriv of l => prop => reason
`;
val _ = Hol_datatype ` 
judgment =  (* judgment *)
   judgment_follows of proplist => prop
`;
val _ = Hol_datatype ` 
proof =  (* proof *)
   proof_entries of entry list
;
entry =  (* proof entry *)
   entry_derivation of derivation (* line *)
 | entry_box of proof (* box *)
 | entry_invalid
`;
val _ = Hol_datatype ` 
claim =  (* claim *)
   claim_judgment_proof of judgment => proof
`;
val _ = type_abbrev("G", ``:((num + (num # num)) |-> (prop + (prop # prop)))``);
val _ = type_abbrev("dyadicprop", ``:(prop + (prop # prop))``);

Definition LAST_DEFAULT:
 (LAST_DEFAULT [] default = default) /\
 (LAST_DEFAULT (e::el) default = LAST (e::el))
End

Definition proof_list_entry:
 proof_list_entry (proof_entries l) = l
End

(** definitions *)
(* defns validity *)

val (validity_rules, validity_ind, validity_cases) = Hol_reln`
(* defn valid_claim *)

( (* vc_claim *) ! (proplist:proplist) (prop:prop) (proof:proof) (l:l) (justification:justification) . (clause_name "vc_claim") /\
((  (LAST_DEFAULT (proof_list_entry  proof ) entry_invalid)   =  (entry_derivation (derivation_deriv l prop (reason_justification justification))) ) /\
( ( valid_proof  FEMPTY  proplist proof )))
 ==> 
( ( valid_claim (claim_judgment_proof (judgment_follows proplist prop) proof) )))

/\(* defn valid_proof *)

( (* vp_empty *) ! (G:G) (proplist:proplist) . (clause_name "vp_empty") ==> 
( ( valid_proof G proplist  (proof_entries [])  )))

/\ ( (* vp_derivation *) ! (G:G) (proplist:proplist) (l:l) (prop:prop) (justification:justification) (proof:proof) . (clause_name "vp_derivation") /\
(( ( valid_derivation G proplist (derivation_deriv l prop (reason_justification justification)) )) /\
( ( valid_proof  (FUPDATE  G  (INL  l , INL  prop ))  proplist proof )))
 ==> 
( ( valid_proof G proplist  (proof_entries ( (entry_derivation (derivation_deriv l prop (reason_justification justification)))  :: (proof_list_entry  proof )))  )))

/\ ( (* vp_box *) ! (G:G) (proplist:proplist) (l:l) (prop:prop) (proof:proof) (proof':proof) (l':l) (prop':prop) (reason:reason) . (clause_name "vp_box") /\
((  (LAST_DEFAULT (proof_list_entry   (proof_entries ( (entry_derivation (derivation_deriv l prop reason_assumption))  :: (proof_list_entry  proof )))  ) entry_invalid)   =  (entry_derivation (derivation_deriv l' prop' reason)) ) /\
( ( valid_proof  (FUPDATE  G  (INL  l , INL  prop ))  proplist proof )) /\
( ( valid_proof  (FUPDATE  G  (INR ( l ,  l' ), INR ( prop ,  prop' )))  proplist proof' )))
 ==> 
( ( valid_proof G proplist  (proof_entries ( (entry_box  (proof_entries ( (entry_derivation (derivation_deriv l prop reason_assumption))  :: (proof_list_entry  proof ))) )  :: (proof_list_entry  proof' )))  )))

/\(* defn valid_derivation *)

( (* vd_premise *) ! (G:G) (proplist:proplist) (l:l) (prop:prop) . (clause_name "vd_premise") /\
(( (MEM  prop   proplist ) ))
 ==> 
( ( valid_derivation G proplist (derivation_deriv l prop (reason_justification justification_premise)) )))

/\ ( (* vd_andi *) ! (G:G) (proplist:proplist) (l:l) (prop:prop) (prop':prop) (l1:l) (l2:l) . (clause_name "vd_andi") /\
(( (FLOOKUP  G  (INL  l1 ) = SOME (INL  prop )) ) /\
( (FLOOKUP  G  (INL  l2 ) = SOME (INL  prop' )) ))
 ==> 
( ( valid_derivation G proplist (derivation_deriv l (prop_and prop prop') (reason_justification (justification_andi l1 l2))) )))

/\ ( (* vd_ande1 *) ! (G:G) (proplist:proplist) (l:l) (prop:prop) (l':l) (prop':prop) . (clause_name "vd_ande1") /\
(( (FLOOKUP  G  (INL  l' ) = SOME (INL  (prop_and prop prop') )) ))
 ==> 
( ( valid_derivation G proplist (derivation_deriv l prop (reason_justification (justification_ande1 l'))) )))

/\ ( (* vd_ande2 *) ! (G:G) (proplist:proplist) (l:l) (prop':prop) (l':l) (prop:prop) . (clause_name "vd_ande2") /\
(( (FLOOKUP  G  (INL  l' ) = SOME (INL  (prop_and prop prop') )) ))
 ==> 
( ( valid_derivation G proplist (derivation_deriv l prop' (reason_justification (justification_ande2 l'))) )))

/\ ( (* vd_impe *) ! (G:G) (proplist:proplist) (l:l) (prop:prop) (l1:l) (l2:l) (prop':prop) . (clause_name "vd_impe") /\
(( (FLOOKUP  G  (INL  l1 ) = SOME (INL  prop' )) ) /\
( (FLOOKUP  G  (INL  l2 ) = SOME (INL  (prop_imp prop' prop) )) ))
 ==> 
( ( valid_derivation G proplist (derivation_deriv l prop (reason_justification (justification_impe l1 l2))) )))

/\ ( (* vd_impi *) ! (G:G) (proplist:proplist) (l:l) (prop:prop) (prop':prop) (l1:l) (l2:l) . (clause_name "vd_impi") /\
(( (FLOOKUP  G  (INR ( l1 ,  l2 )) = SOME (INR ( prop ,  prop' ))) ))
 ==> 
( ( valid_derivation G proplist (derivation_deriv l (prop_imp prop prop') (reason_justification (justification_impi l1 l2))) )))

`;

val _ = export_theory ();
