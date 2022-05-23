open HolKernel boolLib Parse bossLib wordsLib optionTheory wordsTheory pred_setTheory listTheory rich_listTheory finite_mapTheory sortingTheory milUtilityTheory milTheory milSemanticsUtilityTheory ottTheory milMetaTheory milCompositionalTheory milTracesTheory milExecutableUtilityTheory milExecutableTransitionTheory milExecutableIOTraceTheory;

(* ============================================ *)
(* Basic composition of MIL executable programs *)
(* ============================================ *)

val _ = new_theory "milExecutableCompositional";

Theorem compositional_program_state_list_lt_bound_name_instr:
 !il0 il1 t i.
  compositional_program (set il1) (max_bound_name_list il0) ==>
  MEM t (bound_names_program_list il0) ==>
  MEM i il1 ==>
  t < bound_name_instr i
Proof
 rw [] >>
 `max_bound_name_list il0 = MAX_SET (bound_names_program (set il0))`
  by METIS_TAC [max_bound_name_list_correct] >>
 fs [] >>
 `FINITE (set il0)` by rw [FINITE_LIST_TO_SET] >>
 METIS_TAC [
  compositional_program_state_lt_bound_name_instr,
  bound_names_program_list_correct
 ]
QED

Theorem compositional_program_state_list_neq_bound_name_instr:
 !il0 il1 t i.
  compositional_program (set il1) (max_bound_name_list il0) ==>
  MEM t (bound_names_program_list il0) ==>
  MEM i il1 ==>
  t <> bound_name_instr i
Proof
 rw [] >> strip_tac >>
 `t < bound_name_instr i` suffices_by DECIDE_TAC >>
 METIS_TAC [compositional_program_state_list_lt_bound_name_instr]
QED

Theorem compositional_program_append_program_state_list_well_formed_ok:
 !stl il. NO_DUPLICATES il ==>
  State_st_list_well_formed_ok stl ==>
  compositional_program (set il) (max_name_in_state_list stl) ==>
  State_st_list_well_formed_ok (append_program_state_list stl il)
Proof
 rw [GSYM max_name_in_state_list_correct] >>
 `well_formed_state (state_list_to_state stl)`
  by (Cases_on `stl` >> fs [State_st_list_well_formed_ok]) >>
 `well_formed_state (union_program_state (state_list_to_state stl) (set il))`
  by fs [compositional_program_union_program_state_well_formed] >>
 fs [GSYM append_program_state_list_correct] >>
 Cases_on `stl` >>
 rename1 `State_st_list il0 s0 cl0 fl0` >>  
 fs [State_st_list_well_formed_ok,state_list_to_state,append_program_state_list] >>
 once_rewrite_tac [NO_DUPLICATES] >>
 `!i i'. MEM i il0 ==> MEM i' il ==> bound_name_instr i <> bound_name_instr i'`
  suffices_by METIS_TAC [ALL_DISTINCT_MAP_APPEND,NO_DUPLICATES] >>
 rw [] >>
 `compositional_program (set il) (max_name_in_state_list (State_st_list il0 s0 cl0 fl0))`
  by METIS_TAC [max_name_in_state_list_correct,state_list_to_state] >>
 fs [max_name_in_state_list] >>
 `MEM (bound_name_instr i) (bound_names_program_list il0)`
  by (rw [bound_names_program_list_correct,bound_names_program] >> METIS_TAC []) >>
 METIS_TAC [compositional_program_state_list_neq_bound_name_instr]
QED

Theorem compositional_program_append_program_state_list_SORTED:
 !stl il.
  compositional_program (set il) (max_name_in_state_list stl) ==>
  SORTED bound_name_instr_le (state_program_list stl) ==>
  SORTED bound_name_instr_le il ==>
  SORTED bound_name_instr_le (state_program_list (append_program_state_list stl il))
Proof
 Cases_on `stl` >>
 rename1 `State_st_list il0 s0 cl0 fl0` >>
 rw [state_program_list,append_program_state_list] >>
 MATCH_MP_TAC SORTED_APPEND_IMP >> rw [] >-
 rw [transitive_bound_name_instr_le] >>
 rw [bound_name_instr_le,name_le] >>
 `MEM (bound_name_instr x) (bound_names_program_list il0)`
  by (rw [bound_names_program_list_correct,bound_names_program] >> METIS_TAC []) >>
 `bound_name_instr x < bound_name_instr y`
  suffices_by DECIDE_TAC >>
 METIS_TAC [compositional_program_state_list_lt_bound_name_instr,max_name_in_state_list]
QED

(* FIXME: move to better location, check duplication *)
Theorem step_execution_out_of_order_step_list_has_execution_l_trace:
!pi stl tr. State_st_list_well_formed_ok stl ==>
 FST (HD pi) = stl ==>
 step_execution out_of_order_step_list pi ==>
 trace obs_of_ll obs_visible pi = tr ==>
 ?pi'. FST (HD pi') = state_list_to_state stl /\
  step_execution out_of_order_step pi' /\
  trace obs_of_l obs_visible pi' = tr
Proof
 rw [] >>
 Q.EXISTS_TAC `MAP step_list_to_step pi` >> rw [] >| [
   `pi <> []` by METIS_TAC [step_execution_not_empty_list] >>
   Cases_on `pi` >> rw [] >>
   Cases_on `h` >> Cases_on `r` >> fs [step_list_to_step],
   rw [step_execution_out_of_order_step_list_step],
   METIS_TAC [trace_obs_of_ll_obs_of_l_MAP_step_list_to_step]
 ]
QED

(* FIXME: move to better location, check duplication *)
Theorem step_execution_in_order_step_list_has_execution_l_trace:
!pi stl tr. State_st_list_well_formed_ok stl ==>
 FST (HD pi) = stl ==>
 step_execution in_order_step_list pi ==>
 trace obs_of_ll obs_visible pi = tr ==>
 ?pi'. FST (HD pi') = state_list_to_state stl /\
  step_execution in_order_step pi' /\
  trace obs_of_l obs_visible pi' = tr
Proof
 rw [] >>
 Q.EXISTS_TAC `MAP step_list_to_step pi` >> rw [] >| [
   `pi <> []` by METIS_TAC [step_execution_not_empty_list] >>
   Cases_on `pi` >> rw [] >>
   Cases_on `h` >> Cases_on `r` >> fs [step_list_to_step],
   rw [step_execution_in_order_step_list_step],
   METIS_TAC [trace_obs_of_ll_obs_of_l_MAP_step_list_to_step]
 ]
QED

val _ = export_theory ();
