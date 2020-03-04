open HolKernel boolLib Parse bossLib pairTheory optionTheory stringTheory;
open relationTheory listTheory rich_listTheory finite_mapTheory pred_setTheory;
open IndDefLib IndDefRules proofTheory;

val _ = new_theory "proofMeta";

(* key semantic definitions *)

Definition prop_of:
 (prop_of (prop_p b) = b) /\
 (prop_of (prop_neg p) = ~(prop_of p)) /\
 (prop_of (prop_and p1 p2) = ((prop_of p1) /\ (prop_of p2))) /\
 (prop_of (prop_or p1 p2) = ((prop_of p1) \/ (prop_of p2))) /\
 (prop_of (prop_imp p1 p2) = ((prop_of p1) ==> (prop_of p2))) /\
 (prop_of prop_cont = F)
End

Definition premises_admitted:
 premises_admitted pl = (!p. MEM p pl ==> prop_of p)
End

Definition map_line_admitted:
 map_line_admitted G = (!l p. FLOOKUP G (INL l) = SOME (INL p) ==> prop_of p)
End

Definition map_box_admitted:
 map_box_admitted G =
  (!l1 l2 p1 p2. FLOOKUP G (INR (l1, l2)) = SOME (INR (p1, p2)) ==>
  (prop_of p1 ==> prop_of p2))
End

(* useful induction principle *)

Theorem valid_proof_ind:
 !P. ((!G pl. P G pl (proof_entries []))
 /\
 (!G pl l p j pr. valid_derivation G pl (derivation_deriv l p (reason_justification j)) /\
 valid_proof (FUPDATE G (INL l, INL p)) pl pr /\
 P (FUPDATE G (INL l, INL p)) pl pr ==>
 P G pl (proof_entries ((entry_derivation (derivation_deriv l p (reason_justification j))) :: proof_list_entry pr)))
 /\
 (!G pl l p pr pr' l' p' r.
 LAST_DEFAULT (proof_list_entry (proof_entries
  (entry_derivation (derivation_deriv l p reason_assumption) :: proof_list_entry pr))) entry_invalid =
   entry_derivation (derivation_deriv l' p' r) /\
  valid_proof (FUPDATE G (INL l, INL p)) pl pr /\
  P (FUPDATE G (INL l, INL p)) pl pr /\
  valid_proof (FUPDATE G (INR (l,l'),INR (p,p'))) pl pr' /\
  P (FUPDATE G (INR (l,l'),INR (p,p'))) pl pr' ==>
  P G pl (proof_entries (entry_box (proof_entries
   (entry_derivation (derivation_deriv l p reason_assumption) :: proof_list_entry pr)):: proof_list_entry pr')))) ==>
 (!G pl pr. valid_proof G pl pr ==> P G pl pr)
Proof
 GEN_TAC >> STRIP_TAC >>
 `((!c. valid_claim c ==> (\_. T) c) /\
  (!G pl pr. valid_proof G pl pr ==> (\G0 pl0 pr0. P G0 pl0 pr0 /\ valid_proof G0 pl0 pr0) G pl pr) /\
  (!G pl d. valid_derivation G pl d ==> valid_derivation G pl d))` suffices_by METIS_TAC [] >>
 MATCH_MP_TAC valid_claim_ind >> RW_TAC list_ss [valid_claim_rules]
QED

(* soundness of line rules *)

Theorem soundness_premise:
 !G pl p l. premises_admitted pl ==>
  valid_derivation G pl (derivation_deriv l p (reason_justification justification_premise)) ==>
  prop_of p
Proof
 RW_TAC list_ss [premises_admitted, valid_claim_cases]
QED

Theorem soundness_andi:
 !G pl p l l1 l2. map_line_admitted G ==>
  valid_derivation G pl (derivation_deriv l p (reason_justification (justification_andi l1 l2))) ==>
  prop_of p
Proof
 RW_TAC list_ss [map_line_admitted, valid_claim_cases] >>
 FULL_SIMP_TAC list_ss [prop_of, FLOOKUP_DEF] >> METIS_TAC []
QED

Theorem soundness_ande1:
 !G pl p l1 l2. map_line_admitted G ==>
  valid_derivation G pl (derivation_deriv l1 p (reason_justification (justification_ande1 l2))) ==>
  prop_of p
Proof
 RW_TAC list_ss [map_line_admitted, valid_claim_cases] >>
 FULL_SIMP_TAC list_ss [prop_of, FLOOKUP_DEF] >> METIS_TAC [prop_of]
QED

Theorem soundness_ande2:
 !G pl p l1 l2. map_line_admitted G ==>
  valid_derivation G pl (derivation_deriv l1 p (reason_justification (justification_ande2 l2))) ==>
  prop_of p
Proof
 RW_TAC list_ss [map_line_admitted, valid_claim_cases] >>
 FULL_SIMP_TAC list_ss [prop_of, FLOOKUP_DEF] >> METIS_TAC [prop_of]
QED

Theorem soundness_impe:
 !G pl p l l1 l2. map_line_admitted G ==>
  valid_derivation G pl (derivation_deriv l p (reason_justification (justification_impe l1 l2))) ==>
  prop_of p
Proof
 RW_TAC list_ss [map_line_admitted, valid_claim_cases] >>
 FULL_SIMP_TAC list_ss [prop_of, FLOOKUP_DEF] >> METIS_TAC [prop_of]
QED

Theorem soundness_impi:
 !G pl p l l1 l2. map_box_admitted G ==>
  valid_derivation G pl (derivation_deriv l p (reason_justification (justification_impi l1 l2))) ==>
  prop_of p
Proof
 RW_TAC list_ss [map_box_admitted, valid_claim_cases] >>
 FULL_SIMP_TAC list_ss [prop_of, FLOOKUP_DEF] >> METIS_TAC []
QED

Theorem soundness_copy:
 !G pl p l1 l2. map_line_admitted G ==>
  valid_derivation G pl (derivation_deriv l1 p (reason_justification (justification_copy l2))) ==>
  prop_of p
Proof
 cheat
QED

Theorem soundness_lem:
 !G pl p l. valid_derivation G pl (derivation_deriv l p (reason_justification justification_lem)) ==>
  prop_of p
Proof
 cheat
QED

Theorem soundness_ori1:
 !G pl p l1 l2. map_line_admitted G ==>
  valid_derivation G pl (derivation_deriv l1 p (reason_justification (justification_ori1 l2))) ==>
  prop_of p
Proof
 cheat
QED

Theorem soundness_ori2:
 !G pl p l l1 l2. map_line_admitted G ==>
  valid_derivation G pl (derivation_deriv l1 p (reason_justification (justification_ori2 l2))) ==>
  prop_of p
Proof
 cheat
QED

Theorem soundness_nege:
 !G pl p l l1 l2. map_line_admitted G ==>
  valid_derivation G pl (derivation_deriv l p (reason_justification (justification_nege l1 l2))) ==>
  prop_of p
Proof
 cheat
QED

Theorem soundness_conte:
 !G pl p l1 l2. map_line_admitted G ==>
  valid_derivation G pl (derivation_deriv l1 p (reason_justification (justification_conte l2))) ==>
  prop_of p
Proof
 cheat
QED

Theorem soundness_negnegi:
 !G pl p l1 l2. map_line_admitted G ==>
  valid_derivation G pl (derivation_deriv l1 p (reason_justification (justification_negnegi l2))) ==>
  prop_of p
Proof
 cheat
QED

Theorem soundness_negnege:
 !G pl p l1 l2. map_line_admitted G ==>
  valid_derivation G pl (derivation_deriv l1 p (reason_justification (justification_negnege l2))) ==>
  prop_of p
Proof
 cheat
QED

Theorem soundness_mt:
 !G pl p l l1 l2. map_line_admitted G ==>
  valid_derivation G pl (derivation_deriv l p (reason_justification (justification_mt l1 l2))) ==>
  prop_of p
Proof
 cheat
QED

Theorem soundness_negi:
 !G pl p l l1 l2. map_box_admitted G ==>
  valid_derivation G pl (derivation_deriv l p (reason_justification (justification_negi l1 l2))) ==>
  prop_of p
Proof
 cheat
QED

Theorem soundness_pbc:
 !G pl p l l1 l2. map_box_admitted G ==>
  valid_derivation G pl (derivation_deriv l p (reason_justification (justification_pbc l1 l2))) ==>
  prop_of p
Proof
 cheat
QED

Theorem soundness_ore:
 !G pl p l l1 l2 l3 l4 l5. map_line_admitted G ==> map_box_admitted G ==>
  valid_derivation G pl (derivation_deriv l p (reason_justification (justification_ore l1 l2 l3 l4 l5))) ==>
  prop_of p
Proof
 cheat
QED

Theorem soundness_derivations:
 !G pl p l j. premises_admitted pl ==> map_line_admitted G ==> map_box_admitted G ==>
  valid_derivation G pl (derivation_deriv l p (reason_justification j)) ==>
  prop_of p
Proof
Cases_on `j` >| 
[
  PROVE_TAC [soundness_premise],
  RW_TAC std_ss [valid_claim_cases],
  RW_TAC std_ss [valid_claim_cases],
  PROVE_TAC [soundness_andi],
  PROVE_TAC [soundness_ande1],
  PROVE_TAC [soundness_ande2],
  RW_TAC std_ss [valid_claim_cases],
  RW_TAC std_ss [valid_claim_cases],
  PROVE_TAC [soundness_impe],
  RW_TAC std_ss [valid_claim_cases],
  RW_TAC std_ss [valid_claim_cases],
  RW_TAC std_ss [valid_claim_cases],
  RW_TAC std_ss [valid_claim_cases],
  RW_TAC std_ss [valid_claim_cases],
  PROVE_TAC [soundness_impi],
  RW_TAC std_ss [valid_claim_cases],
  RW_TAC std_ss [valid_claim_cases],
  RW_TAC std_ss [valid_claim_cases]
]
QED

(* soundness of system  *)

Definition soundness_prop:
 soundness_prop (G:G) pl pr = !l j p. premises_admitted pl ==>
  map_line_admitted G ==> map_box_admitted G ==>
  MEM (entry_derivation (derivation_deriv l p (reason_justification j))) (proof_list_entry pr) ==>
  prop_of p
End

Theorem soundness_empty:
 !G pl. soundness_prop G pl (proof_entries [])
Proof
 RW_TAC list_ss [soundness_prop, proof_list_entry]
QED

Theorem soundness_derivation:
 !G pl l p j pr. valid_derivation G pl (derivation_deriv l p (reason_justification j)) ==>
  valid_proof (FUPDATE G (INL l, INL p)) pl pr ==>
  soundness_prop (FUPDATE G (INL l, INL p)) pl pr ==>
  soundness_prop G pl (proof_entries (entry_derivation
   (derivation_deriv l p (reason_justification j)) :: proof_list_entry pr))
Proof
 RW_TAC list_ss [soundness_prop, proof_list_entry] >- METIS_TAC [soundness_derivations] >>
 SUBGOAL_THEN ``map_line_admitted (FUPDATE (G:G) (INL l, INL p))`` ASSUME_TAC THEN RW_TAC list_ss [map_line_admitted]
 >- ( Cases_on `l = l''` >> RW_TAC list_ss [map_line_admitted] >>
      FULL_SIMP_TAC list_ss [FLOOKUP_DEF, FAPPLY_FUPDATE_THM, FDOM_FUPDATE]
      >- METIS_TAC [soundness_derivations]
      >- METIS_TAC [map_line_admitted, FLOOKUP_DEF] )
 >- ( SUBGOAL_THEN ``map_box_admitted (FUPDATE (G:G) (INL l, INL p))`` ASSUME_TAC
     >- ( FULL_SIMP_TAC list_ss [map_box_admitted, FAPPLY_FUPDATE_THM, FDOM_FUPDATE, FLOOKUP_DEF] >>
          METIS_TAC [map_box_admitted] )
     >- METIS_TAC [] )
QED

Theorem justification_valid_in:
 !G pl pr. valid_proof G pl pr ==>
  !l p r. MEM (entry_derivation (derivation_deriv l p r)) (proof_list_entry pr) ==> r <> reason_assumption
Proof
 HO_MATCH_MP_TAC valid_proof_ind THEN RW_TAC list_ss [proof_list_entry]
QED

Theorem soundness_box:
 !G pl l1 l2 p1 p2 pr1 pr2 r. LAST_DEFAULT (proof_list_entry (proof_entries (entry_derivation
   (derivation_deriv l1 p1 reason_assumption) :: proof_list_entry pr1))) entry_invalid =
   entry_derivation (derivation_deriv l2 p2 r) ==>
  valid_proof (FUPDATE G (INL l1, INL p1)) pl pr1 ==>
  soundness_prop (FUPDATE G (INL l1, INL p1)) pl pr1 ==>
  valid_proof (FUPDATE G (INR (l1, l2), INR (p1, p2))) pl pr2 ==>
  soundness_prop (FUPDATE G (INR (l1, l2), INR (p1, p2))) pl pr2 ==>
  soundness_prop G pl (proof_entries (entry_box (proof_entries (entry_derivation
   (derivation_deriv l1 p1 reason_assumption) :: proof_list_entry pr1)) :: proof_list_entry pr2))
Proof
RW_TAC list_ss [soundness_prop, proof_list_entry] THEN
FULL_SIMP_TAC list_ss [] THEN
Q.PAT_ASSUM `!l' j' p'. map_line_admitted (G |+ (INR (l1,l2),INR (p1,p2))) ==> Q` (MP_TAC o Q.SPECL [`l`, `j`, `p`]) THEN
RW_TAC bool_ss [] THEN
`map_line_admitted (G |+ (INR (l1,l2),INR (p1,p2))) /\ map_box_admitted (G |+ (INR (l1,l2),INR (p1,p2)))` suffices_by METIS_TAC [] THEN
RW_TAC bool_ss [] THEN1
(FULL_SIMP_TAC bool_ss [map_line_admitted] THEN
RW_TAC bool_ss [FLOOKUP_DEF] THEN
Q.PAT_ASSUM `!l p. FLOOKUP G (INL l) = SOME (INL p) ==> Q` (MP_TAC o Q.SPECL [`l'`, `p'`]) THEN
`FLOOKUP G (INL l') = SOME (INL p')` suffices_by METIS_TAC [] THEN
FULL_SIMP_TAC list_ss [FLOOKUP_DEF, FAPPLY_FUPDATE_THM, FDOM_FUPDATE]) THEN
FULL_SIMP_TAC bool_ss [map_box_admitted] THEN
RW_TAC bool_ss [] THEN
Cases_on `proof_list_entry pr1` THEN RW_TAC bool_ss [] THEN1
(FULL_SIMP_TAC bool_ss [LAST_DEFAULT, LAST_DEF] THEN
 RW_TAC bool_ss [] THEN
 Cases_on `(l1,l1) = (l1',l2')` THEN1
 (RW_TAC bool_ss [] THEN
  FULL_SIMP_TAC std_ss [FLOOKUP_DEF, FAPPLY_FUPDATE_THM, FDOM_FUPDATE] THEN
  RW_TAC bool_ss []) THEN
 RW_TAC bool_ss [] THEN
 FULL_SIMP_TAC std_ss [FLOOKUP_DEF, FAPPLY_FUPDATE_THM, FDOM_FUPDATE, IN_INSERT] THEN
 METIS_TAC []) THEN

`LAST_DEFAULT (proof_list_entry pr1) entry_invalid = entry_derivation (derivation_deriv l2 p2 r)` by FULL_SIMP_TAC list_ss [LAST_DEFAULT, LAST_DEF] THEN
`MEM (entry_derivation (derivation_deriv l2 p2 r)) (proof_list_entry pr1)` by METIS_TAC [LAST_DEFAULT, MEM_LAST] THEN
`r <> reason_assumption` by METIS_TAC [justification_valid_in] THEN
Cases_on `r` THEN1 RW_TAC bool_ss [] THEN
Cases_on `(l1',l2') <> (l1,l2)` THEN1
  (FULL_SIMP_TAC std_ss [FLOOKUP_DEF, FAPPLY_FUPDATE_THM, FDOM_FUPDATE, IN_INSERT] THEN 
  RW_TAC bool_ss [] THEN FULL_SIMP_TAC bool_ss [] THEN METIS_TAC []) THEN
FULL_SIMP_TAC std_ss [FLOOKUP_DEF, FAPPLY_FUPDATE_THM, FDOM_FUPDATE, IN_INSERT] THEN RW_TAC bool_ss [] THEN
`map_line_admitted (G |+ (INL l1,INL p1)) /\ map_box_admitted (G |+ (INL l1,INL p1))` suffices_by METIS_TAC [map_box_admitted] THEN
CONJ_TAC THEN1
(RW_TAC bool_ss [map_line_admitted] THEN
Cases_on `l1 = l'` THEN FULL_SIMP_TAC std_ss [FLOOKUP_DEF, FAPPLY_FUPDATE_THM, FDOM_FUPDATE, IN_INSERT] THEN
`FLOOKUP G (INL l') = SOME (INL p')` suffices_by METIS_TAC [map_line_admitted] THEN
RW_TAC bool_ss [FLOOKUP_DEF]) THEN
RW_TAC bool_ss [map_box_admitted] THEN
FULL_SIMP_TAC std_ss [FLOOKUP_DEF, FAPPLY_FUPDATE_THM, FDOM_FUPDATE, IN_INSERT] THEN
`FLOOKUP G (INR (l1',l2')) = SOME (INR (p1',p2'))` suffices_by METIS_TAC [map_box_admitted] THEN
RW_TAC bool_ss [FLOOKUP_DEF]
QED

Theorem soundness_proof_aux[local]:
 !G pl pr. valid_proof G pl pr ==> soundness_prop G pl pr
Proof
MATCH_MP_TAC valid_proof_ind >> RW_TAC list_ss [] >| [
 PROVE_TAC [soundness_empty],
 PROVE_TAC [soundness_derivation],
 PROVE_TAC [soundness_box]
]
QED

Theorem soundness_proof:
 !G pl pr p l j. premises_admitted pl ==>
  map_line_admitted G ==>
  map_box_admitted G ==>
  valid_proof G pl pr ==>
  MEM (entry_derivation (derivation_deriv l p (reason_justification j))) (proof_list_entry pr) ==>
  prop_of p
Proof
 METIS_TAC [soundness_proof_aux,soundness_prop]
QED

Theorem soundness_claim:
 !p pl pr. premises_admitted pl ==>
 valid_claim (claim_judgment_proof (judgment_follows pl p) pr) ==>
 prop_of p
Proof
 SUBGOAL_THEN ``(!a0. valid_claim a0 <=>
  ?proplist prop proof l j. a0 = claim_judgment_proof (judgment_follows proplist prop) proof /\
  clause_name "vc_claim" /\
  LAST_DEFAULT (proof_list_entry proof) entry_invalid =
   entry_derivation (derivation_deriv l prop (reason_justification j)) /\
  valid_proof FEMPTY proplist proof)`` ASSUME_TAC THEN1 METIS_TAC [valid_claim_cases] THEN
 RW_TAC list_ss [] THEN
 SUBGOAL_THEN ``map_line_admitted (FEMPTY:num + num # num |-> prop + prop # prop)`` ASSUME_TAC THEN1
 RW_TAC list_ss [map_line_admitted, FLOOKUP_DEF, FDOM_FEMPTY] THEN
 SUBGOAL_THEN ``map_box_admitted (FEMPTY:num + num # num |-> prop + prop # prop)`` ASSUME_TAC THEN1
 RW_TAC list_ss [map_box_admitted, FLOOKUP_DEF, FDOM_FEMPTY] THEN
 SUBGOAL_THEN ``?e el. proof_list_entry pr = e::el`` ASSUME_TAC THEN1
 (Cases_on `pr` THEN RW_TAC list_ss [proof_list_entry] THEN Cases_on `l'` THEN RW_TAC list_ss [] THEN
 FULL_SIMP_TAC list_ss [proof_list_entry, LAST_DEFAULT] THEN
 `entry_invalid <> entry_derivation (derivation_deriv l p (reason_justification j))` by RW_TAC list_ss [fetch "proof" "entry_distinct"] THEN
 RW_TAC list_ss []) THEN
 RW_TAC list_ss [] THEN FULL_SIMP_TAC list_ss [LAST_DEFAULT] THEN
 SUBGOAL_THEN ``MEM (entry_derivation (derivation_deriv l p (reason_justification j))) (proof_list_entry pr)`` ASSUME_TAC THEN1
 (RW_TAC bool_ss [] THEN METIS_TAC [MEM_LAST]) THEN
 METIS_TAC [soundness_proof]
QED

val _ = export_theory();
