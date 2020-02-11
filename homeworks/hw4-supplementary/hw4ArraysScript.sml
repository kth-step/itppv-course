open HolKernel Parse boolLib bossLib;

val _ = new_theory "hw4Arrays";


(**************************************************)
(* Provided part                                  *)
(**************************************************)

val num2boolList_def = Define `
  (num2boolList 0 = []) /\
  (num2boolList 1 = []) /\
  (num2boolList n = (EVEN n) :: num2boolList (n DIV 2))`

(* The resulting definition is hard to apply and
   rewriting with it loops easily. So let's provide
   a decent lemma capturing the semantics *)

val num2boolList_REWRS = store_thm ("num2boolList_REWRS",
 ``(num2boolList 0 = []) /\
   (num2boolList 1 = []) /\
   (!n. 2 <= n ==> ((num2boolList n = (EVEN n) :: num2boolList (n DIV 2))))``,
REPEAT STRIP_TAC >| [
  METIS_TAC[num2boolList_def],
  METIS_TAC[num2boolList_def],

  `n <> 0 /\ n <> 1` by DECIDE_TAC >>
  METIS_TAC[num2boolList_def]
]);


(* It is aslo useful to show when the list is empty *)
val num2boolList_EQ_NIL = store_thm ("num2boolList_EQ_NIL",
  ``!n. (num2boolList n = []) <=> ((n = 0) \/ (n = 1))``,
GEN_TAC >> EQ_TAC >| [
  REPEAT STRIP_TAC >>
  CCONTR_TAC >>
  FULL_SIMP_TAC list_ss [num2boolList_REWRS],

  REPEAT STRIP_TAC >> (
    ASM_SIMP_TAC std_ss [num2boolList_REWRS]
  )
]);


(* Now the awkward arithmetic part. Let's show that num2boolList is injective *)

(* For demonstration, let's define our own induction theorem *)
val MY_NUM_INDUCT = store_thm ("MY_NUM_INDUCT",
  ``!P. P 1 /\ (!n. (2 <= n /\ (!m. (m < n /\ m <> 0) ==> P m)) ==> P n) ==> (!n. n <> 0 ==> P n)``,
REPEAT STRIP_TAC >>
completeInduct_on `n` >>
Cases_on `n` >> FULL_SIMP_TAC arith_ss [] >>
Cases_on `n'` >> ASM_SIMP_TAC arith_ss [])

val num2boolList_INJ = store_thm ("num2boolList_INJ",
  ``!n. n <> 0 ==> !m. m <> 0 ==> (num2boolList n = num2boolList m) ==> (n = m)``,

HO_MATCH_MP_TAC MY_NUM_INDUCT >>
CONJ_TAC >- (
  SIMP_TAC list_ss [num2boolList_REWRS, num2boolList_EQ_NIL]
) >>
GEN_TAC >> STRIP_TAC >> GEN_TAC >> STRIP_TAC >>
Cases_on `m = 1` >- (
  ASM_SIMP_TAC list_ss [num2boolList_REWRS]
) >>
ASM_SIMP_TAC list_ss [num2boolList_REWRS] >>
REPEAT STRIP_TAC >>
`n DIV 2 = m DIV 2` by (
  `(m DIV 2 <> 0) /\ (n DIV 2 <> 0) /\ (n DIV 2 < n)` suffices_by METIS_TAC[] >>

  ASM_SIMP_TAC arith_ss [arithmeticTheory.NOT_ZERO_LT_ZERO,
    arithmeticTheory.X_LT_DIV]
) >>
`n MOD 2 = m MOD 2` by (
  ASM_SIMP_TAC std_ss [arithmeticTheory.MOD_2]
) >>
`0 < 2` by DECIDE_TAC >>
METIS_TAC[arithmeticTheory.DIVISION]);




(* Shifting the keys by one is trivial and by this we get rid of the
   preconditions of the injectivity theorem *)
val num2arrayIndex_def = Define `num2arrayIndex n = (num2boolList (SUC n))`
val num2arrayIndex_INJ = store_thm ("num2arrayIndex_INJ",
  ``!n m. (num2arrayIndex n = num2arrayIndex m) <=> (n = m)``,

SIMP_TAC list_ss [num2arrayIndex_def] >>
METIS_TAC [numTheory.NOT_SUC, num2boolList_INJ, numTheory.INV_SUC]);


(* Now let's define the inverse operation *)
val boolList2num_def = Define `
  (boolList2num [] = 1) /\
  (boolList2num (F::idx) = 2 * boolList2num idx + 1) /\
  (boolList2num (T::idx) = 2 * boolList2num idx)`

(* We can show that the inverse is never 0 ... *)
val boolList2num_GT_0 = prove (``!idx. 0 < boolList2num idx``,
Induct >- SIMP_TAC arith_ss [boolList2num_def] >>
Cases >> ASM_SIMP_TAC arith_ss [boolList2num_def]);

(* ... so we can subtract 1 for the index shift *)
val arrayIndex2num_def = Define `arrayIndex2num idx = PRE (boolList2num idx)`



(* Now a fiddly prove that we indeed defined the inverse *)
val boolList2num_inv = prove (``!idx. num2boolList (boolList2num idx) = idx``,
Induct >- (
  SIMP_TAC arith_ss [boolList2num_def, num2boolList_REWRS]
) >>
`0 < boolList2num idx` by METIS_TAC[boolList2num_GT_0] >>
`0 < 2` by DECIDE_TAC >>
Cases >| [
  `!x. (2 * x) MOD 2 = 0` by
     METIS_TAC[arithmeticTheory.MOD_EQ_0, arithmeticTheory.MULT_COMM] >>
  `!x. (2 * x) DIV 2 = x` by
     METIS_TAC[arithmeticTheory.MULT_DIV, arithmeticTheory.MULT_COMM] >>
  ASM_SIMP_TAC list_ss [boolList2num_def, num2boolList_REWRS,
    arithmeticTheory.EVEN_MOD2],

  `!x y. (2 * x + y) MOD 2 = (y MOD 2)` by
     METIS_TAC[arithmeticTheory.MOD_TIMES, arithmeticTheory.MULT_COMM] >>
  `!x y. (2 * x + y) DIV 2 = x + y DIV 2` by
     METIS_TAC[arithmeticTheory.ADD_DIV_ADD_DIV, arithmeticTheory.MULT_COMM] >>
  ASM_SIMP_TAC list_ss [boolList2num_def, num2boolList_REWRS,
    arithmeticTheory.EVEN_MOD2]
]);

(* Shifting is easy then *)
val arrayIndex2num_inv = store_thm ("arrayIndex2num_inv",
  ``!idx. num2arrayIndex (arrayIndex2num idx) = idx``,
GEN_TAC >>
REWRITE_TAC[num2arrayIndex_def, arrayIndex2num_def] >>
`0 < boolList2num idx` by METIS_TAC[boolList2num_GT_0] >>
FULL_SIMP_TAC arith_ss [arithmeticTheory.SUC_PRE] >>
ASM_SIMP_TAC std_ss [boolList2num_inv]);


(* It is also very easy to derive other useful properties. *)
val num2arrayIndex_inv = store_thm ("num2arrayIndex_inv",
  ``!n. arrayIndex2num (num2arrayIndex n) = n``,
METIS_TAC[ num2arrayIndex_INJ, arrayIndex2num_inv]);

val arrayIndex2num_INJ = store_thm ("arrayIndex2num_INJ",
  ``!idx1 idx2. (arrayIndex2num idx1 = arrayIndex2num idx2) <=> (idx1 = idx2)``,
METIS_TAC[ num2arrayIndex_INJ, arrayIndex2num_inv]);


(* A rewrite for the top-level inverse might be handy *)
val num2arrayIndex_REWRS = store_thm ("num2arrayIndex_REWRS", ``
!n. num2arrayIndex n =
    if (n = 0) then [] else
      ODD n :: num2arrayIndex ((n - 1) DIV 2)``,

REWRITE_TAC[num2arrayIndex_def] >>
Cases >> SIMP_TAC arith_ss [num2boolList_REWRS] >>
SIMP_TAC arith_ss [arithmeticTheory.ODD, arithmeticTheory.EVEN,
  arithmeticTheory.ODD_EVEN] >>
`(!x r. (2 * x + r) DIV 2 = x + r DIV 2) /\ (!x. (2*x) DIV 2 = x)` by (
  `0 < 2` by DECIDE_TAC >>
  METIS_TAC[arithmeticTheory.ADD_DIV_ADD_DIV, arithmeticTheory.MULT_COMM,
    arithmeticTheory.MULT_DIV]
) >>
Cases_on `EVEN n'` >> ASM_REWRITE_TAC[] >| [
  `?m. n' = 2* m` by METIS_TAC[arithmeticTheory.EVEN_ODD_EXISTS] >>
  ASM_SIMP_TAC arith_ss [arithmeticTheory.ADD1],

  `?m. n' = SUC (2* m)` by METIS_TAC[arithmeticTheory.EVEN_ODD_EXISTS,
    arithmeticTheory.ODD_EVEN] >>
  ASM_SIMP_TAC arith_ss [arithmeticTheory.ADD1]
]);


(**************************************************)
(* YOU SHOULD WORK FROM HERE ON                   *)
(**************************************************)

(* TODO: Define a datatype for arrays storing values of type 'a. *)
val _ = Datatype `array = DUMMY 'a`


(* TODO: Define a new, empty array *)
val EMPTY_ARRAY_def = Define `EMPTY_ARRAY : 'a array = ARB`

(* TODO: define ILOOKUP, IUPDATE and IREMOVE *)
val IUPDATE_def = Define `IUPDATE (v : 'a) (a : 'a array) (k : bool list) = a:'a array`
val ILOOKUP_def = Define `ILOOKUP (a : 'a array) (k : bool list) = NONE:'a option`
val IREMOVE_def = Define `IREMOVE (a : 'a array) (k : bool list) = a:'a array`


(* With these, we can define the lifted operations *)
val LOOKUP_def = Define `LOOKUP a n = ILOOKUP a (num2arrayIndex n)`
val UPDATE_def = Define `UPDATE v a n = IUPDATE v a (num2arrayIndex n)`
val REMOVE_def = Define `REMOVE a n = IREMOVE a (num2arrayIndex n)`


(* TODO: show a few properties *)
val LOOKUP_EMPTY = store_thm ("LOOKUP_EMPTY",
  ``!k. LOOKUP EMPTY_ARRAY k = NONE``,
cheat);

val LOOKUP_UPDATE = store_thm ("LOOKUP_UPDATE",
  ``!v n n' a. LOOKUP (UPDATE v a n) n' =
       (if (n = n') then SOME v else LOOKUP a n')``,
cheat);

val LOOKUP_REMOVE = store_thm ("LOOKUP_REMOVE",
  ``!n n' a. LOOKUP (REMOVE a n) n' =
       (if (n = n') then NONE else LOOKUP a n')``,
cheat);


val UPDATE_REMOVE_EQ = store_thm ("UPDATE_REMOVE_EQ", ``
  (!v1 v2 n a. UPDATE v1 (UPDATE v2 a n) n = UPDATE v1 a n) /\
  (!v n a. UPDATE v (REMOVE a n) n = UPDATE v a n) /\
  (!v n a. REMOVE (UPDATE v a n) n = REMOVE a n)
``,
cheat);


val UPDATE_REMOVE_NEQ = store_thm ("UPDATE_REMOVE_NEQ", ``
  (!v1 v2 a n1 n2. n1 <> n2 ==>
     ((UPDATE v1 (UPDATE v2 a n2) n1) = (UPDATE v2 (UPDATE v1 a n1) n2))) /\
  (!v a n1 n2. n1 <> n2 ==>
     ((UPDATE v (REMOVE a n2) n1) = (REMOVE (UPDATE v a n1) n2))) /\
  (!a n1 n2. n1 <> n2 ==>
     ((REMOVE (REMOVE a n2) n1) = (REMOVE (REMOVE a n1) n2)))``,
cheat);


val _ = export_theory();
