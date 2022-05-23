open HolKernel boolLib Parse bossLib wordsLib wordsTheory finite_mapTheory pred_setTheory relationTheory listTheory rich_listTheory pairTheory milUtilityTheory milTheory milSemanticsUtilityTheory milMetaTheory milTracesTheory milMetaIOTheory milExecutableUtilityTheory milExecutableTransitionTheory milExecutableIOTheory milExecutableIOTraceTheory milExecutableIOCompletenessTheory milExecutableExamplesTheory milNoninterferenceTheory milMaxExeTraceUtilityTheory;

(* =================================================== *)
(*  Maximal execution and trace of example conditional *)
(* =================================================== *)

val _ = new_theory "milMaxExeTraceExampleConditional";

(* example conditional after initialization *)
Definition example_conditional_exe_init:
  example_conditional_exe_init b c z a t =
  [i_assign (t+1) (e_val 1w) (o_internal (e_val z));
   i_assign (t+2) (e_val 1w) (o_internal (e_val c));
   i_assign (t+3) (e_val 1w) (o_store res_REG (t+1) (t+2));
   i_assign (t+4) (e_val 1w) (o_internal (e_val 0w));
   i_assign (t+5) (e_val 1w) (o_internal (e_val b));
   i_assign (t+6) (e_val 1w) (o_store res_PC (t+4) (t+5));
   i_assign (t+7) (e_val 1w) (o_internal (e_val 0w));
   i_assign (t+8) (e_val 1w) (o_internal (e_val z));
   i_assign (t+9) (e_val 1w) (o_load res_REG (t+8));
   i_assign (t+10) (e_val 1w) (o_internal (e_eq (e_name (t+9)) (e_val 1w)));
   i_assign (t+11) (e_val 1w) (o_load res_PC (t+7));
   i_assign (t+12) (e_val 1w) (o_internal (e_val a));
   i_assign (t+13) (e_name (t+10)) (o_store res_PC (t+7) (t+12));
   i_assign (t+14) (e_val 1w) (o_internal (e_add (e_name (t+11)) (e_val 4w)));
   i_assign (t+15) (e_not (e_name (t+10))) (o_store res_PC (t+7) (t+14))]
End

Definition example_conditional_list:
  example_conditional_list b c z a = example_conditional_exe_init b c z a 0
End

Definition example_conditional_store:
  example_conditional_store b c z :num |-> v =
  (FEMPTY |+ (1,z) |+ (2,c) |+ (3,c) |+ (4,0w) |+ (5,b) |+ (6,b))
End

Definition example_conditional_state_st_list:
  example_conditional_state_st_list b c z a =
  State_st_list (example_conditional_list b c z a) (example_conditional_store b c z) [] [6]
End

Definition example_conditional_maximal_execution:
  example_conditional_maximal_execution b c z a =
  IO_bounded_execution (\v t. []) sem_expr_exe (example_conditional_state_st_list b c z a) 7 9
End

Definition example_conditional_maximal_trace_aux:
  example_conditional_maximal_trace_aux b c z a =
  IO_bounded_trace_aux (\v t. []) sem_expr_exe (example_conditional_state_st_list b c z a) 7 9
End

Definition example_conditional_maximal_trace:
  example_conditional_maximal_trace b c z a =
  IO_bounded_trace (\v t. []) sem_expr_exe (example_conditional_state_st_list b c z a) 7 9
End

Theorem example_conditional_maximal_trace_aux_val_true_last_state_all_completed[local]:
  !a b z.
    all_instructions_completed_list sem_expr_exe
    ((FST o THE) (example_conditional_maximal_trace_aux b val_true z a))
Proof
  rw [] >> EVAL_TAC >> rw [] >> EVAL_TAC
QED

Theorem example_conditional_maximal_trace_aux_not_val_true_last_state_all_completed[local]:
  !a b c z.
     c <> val_true ==>
     all_instructions_completed_list sem_expr_exe
     ((FST o THE) (example_conditional_maximal_trace_aux b c z a))
Proof
  rw [] >> EVAL_TAC >> fs [val_true] >> EVAL_TAC >> rw [] >> EVAL_TAC
QED

Theorem example_conditional_maximal_trace_val_true[local]:
  !a b z.
    example_conditional_maximal_trace b val_true z a = SOME [obs_il a]
Proof
  rw [val_true] >> EVAL_TAC
QED

Theorem example_conditional_maximal_trace_not_val_true[local]:
  !a b c z.
    c <> val_true ==>
    example_conditional_maximal_trace b c z a = SOME [obs_il (b + 4w)]
Proof
  rw [] >> EVAL_TAC >> fs [val_true] >> EVAL_TAC
QED

Theorem example_conditional_trace_equivalence_implies_four_conditions[local]:
  !a1 a2 b1 b2 c1 c2 z1 z2.
    (example_conditional_maximal_trace b1 c1 z1 a1) =
    (example_conditional_maximal_trace b2 c2 z2 a2) ==>
    (c1 = val_true ==> c2 = val_true ==> a1 = a2) /\
    (c1 = val_true ==> c2 <> val_true ==> a1 = b2 + 4w) /\
    (c1 <> val_true ==> c2 = val_true ==> b1 + 4w = a2) /\
    (c1 <> val_true ==> c2 <> val_true ==> b1 = b2)
Proof
  rw [] >> fs [example_conditional_maximal_trace_val_true,example_conditional_maximal_trace_not_val_true]
QED

Theorem State_st_list_well_formed_ok_example_conditional_state_st_list:
  sem_expr = sem_expr_exe ==>
  !a b c z.
    State_st_list_well_formed_ok (example_conditional_state_st_list b c z a)
Proof
  rw [State_st_list_well_formed_ok,example_conditional_state_st_list,
      example_conditional_list,example_conditional_exe_init,example_conditional_store] >-
   EVAL_TAC >>
  rw [state_list_to_state] >>
  SIMP_TAC std_ss [well_formed_state] >>
  REPEAT STRIP_TAC >|[
    EVAL_TAC,
    EVAL_TAC,
    rw [bound_names_program] >> METIS_TAC [bound_name_instr],
    fs [bound_name_instr] >> rw [] >>
    fs [free_names_instr,names_e,names_o],
    fs [] >> rw [] >> fs [bound_name_instr],
    fs [] >> rw [] >>
    fs [free_names_instr,names_e,names_o] >> METIS_TAC [bound_name_instr],
    fs [],
    fs [],
    fs [map_down,FLOOKUP_DEF],
    fs [map_down,FLOOKUP_DEF] >> rw [] >> fs [] >> EVAL_TAC,
    fs [map_down,FLOOKUP_DEF] >> rw [] >> fs [sem_expr_correct,val_false,sem_expr_exe],
    fs [val_true,val_zero],
    fs [val_true] >> rw [] >> fs [names_e],
    fs [] >> rw [] >> fs [names_o,names_e,sem_expr_correct,val_false],
    fs [sem_instr,sem_expr_correct,FLOOKUP_DEF] >> rw [] >> fs [] >> EVAL_TAC,
    fs [val_true,val_zero],
    fs [],
    `NO_DUPLICATES (example_conditional_list b c z a)` by EVAL_TAC >>
    `State_st_list_ok (example_conditional_state_st_list b c z a)`
      by fs [example_conditional_state_st_list,State_st_list_ok] >>
    `str_may_list sem_expr_exe (example_conditional_state_st_list b c z a) 6 = []` by EVAL_TAC >>
    `str_may (state_list_to_state (example_conditional_state_st_list b c z a)) 6 =
     LIST_TO_SET (str_may_list sem_expr (example_conditional_state_st_list b c z a) 6)`
      by METIS_TAC [str_may_list_correct] >>
    `str_may (state_list_to_state (example_conditional_state_st_list b c z a)) 6 = {}`
      by METIS_TAC [LIST_TO_SET] >>
    fs [state_list_to_state,example_conditional_state_st_list,
        example_conditional_list,example_conditional_exe_init,
        example_conditional_store,bound_names_program]
  ]
QED

Theorem example_conditional_maximal_execution_correct[local]:
  sem_expr = sem_expr_exe ==>
  translate_val_list = (\v t. []) ==>
  !a b c z pi.
    example_conditional_maximal_execution b c z a = SOME pi ==>
    maximal_execution_form in_order_step (state_list_to_state (example_conditional_state_st_list b c z a))
    (MAP step_list_to_step pi)
Proof
  rw [maximal_execution_form] >>
  `State_st_list_well_formed_ok (example_conditional_state_st_list b c z a)`
    by rw [State_st_list_well_formed_ok_example_conditional_state_st_list] >|[
    `translate_val_list_SORTED` by fs [translate_val_list_SORTED] >>
    fs [example_conditional_maximal_execution,example_conditional_state_st_list] >>
    `SORTED bound_name_instr_le (example_conditional_list b c z a)` by (fs [] >> EVAL_TAC) >>
    `Completed_list_up_to sem_expr (State_st_list (example_conditional_list b c z a)
    (example_conditional_store b c z) [] [6]) (PRE 7)`
      by (fs [example_conditional_list,example_conditional_exe_init,example_conditional_store] >>
          EVAL_TAC >> rw [] >> EVAL_TAC) >>
    `DROP (PRE 7) (example_conditional_list b c z a) =
    [i_assign 7 (e_val 1w) (o_internal (e_val 0w));
     i_assign 8 (e_val 1w) (o_internal (e_val z));
     i_assign 9 (e_val 1w) (o_load res_REG 8);
     i_assign 10 (e_val 1w) (o_internal (e_eq (e_name 9) (e_val 1w)));
     i_assign 11 (e_val 1w) (o_load res_PC 7);
     i_assign 12 (e_val 1w) (o_internal (e_val a));
     i_assign 13 (e_name 10) (o_store res_PC 7 12);
     i_assign 14 (e_val 1w) (o_internal (e_add (e_name 11) (e_val 4w)));
     i_assign 15 (e_not (e_name 10)) (o_store res_PC 7 14)]`
      by (fs [example_conditional_list,example_conditional_exe_init] >> EVAL_TAC) >>
    Q.ABBREV_TAC `i = i_assign 7 (e_val 1w) (o_internal (e_val 0w))` >>
    Q.ABBREV_TAC `il = [i_assign 8 (e_val 1w) (o_internal (e_val z));
                        i_assign 9 (e_val 1w) (o_load res_REG 8);
                        i_assign 10 (e_val 1w) (o_internal (e_eq (e_name 9) (e_val 1w)));
                        i_assign 11 (e_val 1w) (o_load res_PC 7);
                        i_assign 12 (e_val 1w) (o_internal (e_val a));
                        i_assign 13 (e_name 10) (o_store res_PC 7 12);
                        i_assign 14 (e_val 1w) (o_internal (e_add (e_name 11) (e_val 4w)));
                        i_assign 15 (e_not (e_name 10)) (o_store res_PC 7 14)]` >>
    `~(Completed_list sem_expr (State_st_list (example_conditional_list b c z a)
    (example_conditional_store b c z) [] [6]) i)`
      by (fs [example_conditional_list,example_conditional_exe_init,example_conditional_store,Abbr `i`] >> EVAL_TAC) >>
    `IO_bounded_execution translate_val_list sem_expr (State_st_list (example_conditional_list b c z a)
    (example_conditional_store b c z) [] [6]) 7 (SUC 8) = SOME pi` by fs [] >>
    PROVE_TAC [IO_bounded_execution_in_order_step_sound],

    UNDISCH_TAC ``example_conditional_maximal_execution b c z a = SOME pi`` >>
    EVAL_TAC >> Cases_on `c = 1w` >> fs [IO_bounded_execution_acc] >>
    rw [] >> fs [step_list_to_step,state_list_to_state],

    `SND (SND (LAST (MAP step_list_to_step (THE (example_conditional_maximal_execution b c z a))))) =
    state_list_to_state (SND (SND (LAST (THE (example_conditional_maximal_execution b c z a)))))`
     by (EVAL_TAC >> Cases_on `c = 1w` >> fs [] >> EVAL_TAC) >>
    rw [] >>
    `all_instructions_completed_list sem_expr_exe
     (SND (SND (LAST (THE (example_conditional_maximal_execution b c z a)))))`
     by (EVAL_TAC >> Cases_on `c = 1w` >> rw [] >> EVAL_TAC >> rw [] >> EVAL_TAC) >>
    `THE (example_conditional_maximal_execution b c z a) = pi` by fs [] >>
    `all_instructions_completed_list sem_expr (SND (SND (LAST pi)))` by fs [] >>
    `?stl'.(SND (SND (LAST pi))) = stl'` by fs [] >>
    `well_formed_state (state_list_to_state stl')`
      by (fs [example_conditional_maximal_execution,example_conditional_state_st_list] >>
          `DROP (PRE 7) (example_conditional_list b c z a) =
          [i_assign 7 (e_val 1w) (o_internal (e_val 0w));
           i_assign 8 (e_val 1w) (o_internal (e_val z));
           i_assign 9 (e_val 1w) (o_load res_REG 8);
           i_assign 10 (e_val 1w) (o_internal (e_eq (e_name 9) (e_val 1w)));
           i_assign 11 (e_val 1w) (o_load res_PC 7);
           i_assign 12 (e_val 1w) (o_internal (e_val a));
           i_assign 13 (e_name 10) (o_store res_PC 7 12);
           i_assign 14 (e_val 1w) (o_internal (e_add (e_name 11) (e_val 4w)));
           i_assign 15 (e_not (e_name 10)) (o_store res_PC 7 14)]`
            by (fs [example_conditional_list,example_conditional_exe_init] >> EVAL_TAC) >>
          Q.ABBREV_TAC `i = i_assign 7 (e_val 1w) (o_internal (e_val 0w))` >>
          Q.ABBREV_TAC `il = [i_assign 8 (e_val 1w) (o_internal (e_val z));
                              i_assign 9 (e_val 1w) (o_load res_REG 8);
                              i_assign 10 (e_val 1w) (o_internal (e_eq (e_name 9) (e_val 1w)));
                              i_assign 11 (e_val 1w) (o_load res_PC 7);
                              i_assign 12 (e_val 1w) (o_internal (e_val a));
                              i_assign 13 (e_name 10) (o_store res_PC 7 12);
                              i_assign 14 (e_val 1w) (o_internal (e_add (e_name 11) (e_val 4w)));
                              i_assign 15 (e_not (e_name 10)) (o_store res_PC 7 14)]` >>
          `~(Completed_list sem_expr (State_st_list (example_conditional_list b c z a)
          (example_conditional_store b c z) [] [6]) i)`
            by (fs [example_conditional_list,example_conditional_exe_init,example_conditional_store,Abbr `i`] >> EVAL_TAC) >>
          `IO_bounded_execution translate_val_list sem_expr (State_st_list (example_conditional_list b c z a)
          (example_conditional_store b c z) [] [6]) 7 (SUC 8) = SOME pi` by fs [] >>
          PROVE_TAC [State_st_list_well_formed_ok_IO_bounded_execution_last_state]) >>
    fs [all_instructions_completed_list_implies_termination_IO]
  ]
QED

Theorem noninterference_example_conditional_trace:
  sem_expr = sem_expr_exe ==>
  translate_val_list = (\v t. []) ==>
  !a1 b1 c1 z1 a2 b2 c2 z2 s1 s2.
    state_list_to_state (example_conditional_state_st_list b1 c1 z1 a1) = s1 ==>
    state_list_to_state (example_conditional_state_st_list b2 c2 z2 a2) = s2 ==>
    trace_indist_IO s1 s2 ==>
    (c1 = val_true ==> c2 = val_true ==> a1 = a2) /\
    (c1 = val_true ==> c2 <> val_true ==> a1 = b2 + 4w) /\
    (c1 <> val_true ==> c2 = val_true ==> b1 + 4w = a2) /\
    (c1 <> val_true ==> c2 <> val_true ==> b1 = b2)
Proof
  REWRITE_TAC [trace_indist_IO,trace_indist] >>
  NTAC 2 STRIP_TAC >>
  REPEAT GEN_TAC >> (NTAC 3 DISCH_TAC) >> fs [] >>
  `?p1. example_conditional_maximal_execution b1 c1 z1 a1 = SOME p1`
    by (EVAL_TAC >> Cases_on `c1 = 1w` >> fs [IO_bounded_execution_acc]) >>
  `?p2. example_conditional_maximal_execution b2 c2 z2 a2 = SOME p2`
    by (EVAL_TAC >> Cases_on `c2 = 1w` >> fs [IO_bounded_execution_acc]) >>
  `maximal_execution_form in_order_step (state_list_to_state
   (example_conditional_state_st_list b1 c1 z1 a1)) (MAP step_list_to_step p1) /\
  maximal_execution_form in_order_step (state_list_to_state
   (example_conditional_state_st_list b2 c2 z2 a2)) (MAP step_list_to_step p2)`
    by fs [example_conditional_maximal_execution_correct] >>
  Q.ABBREV_TAC `stl1 = example_conditional_state_st_list b1 c1 z1 a1` >>
  Q.ABBREV_TAC `stl2 = example_conditional_state_st_list b2 c2 z2 a2` >>
  `State_st_list_well_formed_ok stl1 /\ State_st_list_well_formed_ok stl2`
    by fs [Abbr `stl1`,Abbr `stl2`,State_st_list_well_formed_ok_example_conditional_state_st_list] >>
  `well_formed_state (state_list_to_state stl1) /\ well_formed_state (state_list_to_state stl2)`
    by (Cases_on `stl1` >> Cases_on `stl2` >> fs [State_st_list_well_formed_ok]) >>
  `well_formed_state s1 /\ well_formed_state s2` by METIS_TAC [] >>
  Q.ABBREV_TAC `max_org_pi1 = MAP step_list_to_step p1` >>
  Q.ABBREV_TAC `max_org_pi2 = MAP step_list_to_step p2` >>
  `maximal_execution_form in_order_step s1 max_org_pi1 /\
  maximal_execution_form in_order_step s2 max_org_pi2`  by METIS_TAC [] >>
  `maximal_execution_form in_order_step' s1 (MAP update_lbl max_org_pi1) /\
  maximal_execution_form in_order_step' s2 (MAP update_lbl max_org_pi2)`
    by fs [max_execution_format_step_and_step'] >>
  Q.ABBREV_TAC `max_pi1 = MAP update_lbl max_org_pi1` >>
  Q.ABBREV_TAC `max_pi2 = MAP update_lbl max_org_pi2` >>
  `trace obs_of_l obs_visible max_pi1 = trace obs_of_l obs_visible max_pi2`
    by REWRITE_TAC [UNDISCH_ALL (SPEC_ALL noninterference_implies_maximal_execution_form_in_order_step')] >>
  `trace obs_of_l obs_visible max_org_pi1 = trace obs_of_l obs_visible max_org_pi2` by METIS_TAC [MAP_update_lbl_same_obs,Abbr `max_pi1`,Abbr `max_pi2`] >>
  `example_conditional_maximal_trace b1 c1 z1 a1 <> NONE` by (EVAL_TAC >> Cases_on `c1 = 1w` >> fs [IO_bounded_trace_acc]) >>
  `example_conditional_maximal_trace b2 c2 z2 a2 <> NONE` by (EVAL_TAC >> Cases_on `c2 = 1w` >> fs [IO_bounded_trace_acc]) >>
  `?tr1 tr2.example_conditional_maximal_trace b1 c1 z1 a1 = SOME tr1 /\
  example_conditional_maximal_trace b2 c2 z2 a2 = SOME tr2`
    by (Cases_on `example_conditional_maximal_trace b1 c1 z1 a1` >>
        Cases_on `example_conditional_maximal_trace b2 c2 z2 a2` >> fs []) >>
  `(trace obs_of_l obs_visible max_org_pi1 = tr1) /\ (trace obs_of_l obs_visible max_org_pi2 = tr2)`
    by METIS_TAC [example_conditional_maximal_execution,example_conditional_maximal_trace,
                  IO_bounded_execution_and_trace,Abbr `max_org_pi1`,Abbr `max_org_pi2`] >>
  `example_conditional_maximal_trace b1 c1 z1 a1 = example_conditional_maximal_trace b2 c2 z2 a2` by fs [] >>
  METIS_TAC [example_conditional_trace_equivalence_implies_four_conditions]
QED

val _ = export_theory ();
