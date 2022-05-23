(* ========================= *)
(* General utility functions *)
(* ========================= *)

structure milLib :> milLib =
struct

open HolKernel Parse boolLib bossLib;
open markerTheory markerSyntax markerLib;
open milExecutableExamplesTheory milExecutableUtilityTheory;

(* ----------------- *)
(* Auxiliary tactics *)
(* ----------------- *)

val ERR = mk_HOL_ERR "milLib"

fun Abbrev_wrap eqth =
  EQ_MP (SYM (Thm.SPEC (concl eqth) Abbrev_def)) eqth

(* Adds an assumption Abbrev(v = e) without replacing the term e in the goal. *)
fun AB_TAC eq =
let val (l, r) = dest_eq eq
in
  CHOOSE_THEN (fn th => ASSUME_TAC (Abbrev_wrap (SYM th)))
              (Thm.EXISTS (mk_exists (l, mk_eq (r, l)), r) (Thm.REFL r))
end

(* ---------------------------------------- *)
(* Auxiliary functions for proof automation *)
(* ---------------------------------------- *)

(* FIXME: should be a library theorem *)
val str_act_addr_list_correct_to_set = prove (
  ``!stl t r a l.
    sem_expr = sem_expr_exe ==>
    State_st_list_ok stl ==>
    str_act_addr_list sem_expr_exe stl t r a = l ==>
    str_act_addr (state_list_to_state stl) t r a = set l``,
  METIS_TAC [str_act_addr_list_correct]
)

fun compute_str_act_addr stl stl_ok (t, r, a) =
DISCH_ALL (
  SIMP_RULE list_ss [] (
    MATCH_MP (
      MATCH_MP (
        UNDISCH (SPEC_ALL str_act_addr_list_correct_to_set))
      (SPEC_ALL stl_ok))
    (EVAL ``str_act_addr_list sem_expr_exe ^stl ^t ^r ^a``)))


end
