open HolKernel boolLib Parse bossLib;
open arithmeticTheory stringTheory containerTheory pred_setTheory listTheory;

val _ = new_theory "lambda";

val clause_name = Define `clause_name (x:string) = T`;

val _ = type_abbrev("var", ``:string``); (* term variable *)
val _ = Hol_datatype ` 
term =  (* term *)
   t_var of var (* variable *)
 | t_lam of var => term (* lambda *)
 | t_app of term => term (* app *)
`;

(** subrules *)
val _ = Define `
    ( is_val_of_term (t_var x) = F)
/\  ( is_val_of_term (t_lam x t) = (T))
/\  ( is_val_of_term (t_app t t') = F)
`;

(** substitutions *)
val _ = Define `
    ( tsubst_term t5 x5 (t_var x) = (if x=x5 then t5 else (t_var x)))
/\  ( tsubst_term t5 x5 (t_lam x t) = t_lam x (if MEM x5 [x] then t else (tsubst_term t5 x5 t)))
/\  ( tsubst_term t5 x5 (t_app t t') = t_app (tsubst_term t5 x5 t) (tsubst_term t5 x5 t'))
`;
(** definitions *)
(* defns Jop *)

val (Jop_rules, Jop_ind, Jop_cases) = Hol_reln`
(* defn reduce *)

( (* ax_app *) ! (x:var) (t1:term) (v2:term) . (clause_name "ax_app") /\
((is_val_of_term v2))
 ==> 
( ( reduce (t_app  (t_lam x t1)  v2)  (tsubst_term v2 x t1)  )))

/\ ( (* ctx_app_fun *) ! (t1:term) (t:term) (t1':term) . (clause_name "ctx_app_fun") /\
(( ( reduce t1 t1' )))
 ==> 
( ( reduce (t_app t1 t) (t_app t1' t) )))

/\ ( (* ctx_app_arg *) ! (v:term) (t1:term) (t1':term) . (clause_name "ctx_app_arg") /\
((is_val_of_term v) /\
( ( reduce t1 t1' )))
 ==> 
( ( reduce (t_app v t1) (t_app v t1') )))

`;

val _ = export_theory ();



