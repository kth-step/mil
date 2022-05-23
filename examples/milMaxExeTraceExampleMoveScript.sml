open HolKernel boolLib Parse bossLib wordsLib wordsTheory finite_mapTheory pred_setTheory relationTheory listTheory rich_listTheory pairTheory milUtilityTheory milTheory milSemanticsUtilityTheory milMetaTheory milTracesTheory milMetaIOTheory milExecutableUtilityTheory milExecutableTransitionTheory milExecutableIOTheory milExecutableIOTraceTheory milExecutableIOCompletenessTheory milExecutableExamplesTheory milNoninterferenceTheory milMaxExeTraceUtilityTheory;

(* ============================================ *)
(*  Maximal execution and trace of example move *)
(* ============================================ *)

val _ = new_theory "milMaxExeTraceExampleMove";

(* example move value after initialization *)
Definition example_mov_exe_init:
  example_mov_exe_init a b r1 r5 t =
  [i_assign (t+1) (e_val 1w) (o_internal (e_val r5));
   i_assign (t+2) (e_val 1w) (o_internal (e_val a));
   i_assign (t+3) (e_val 1w) (o_store res_REG (t+1) (t+2));
   i_assign (t+4) (e_val 1w) (o_internal (e_val 0w));
   i_assign (t+5) (e_val 1w) (o_internal (e_val b));
   i_assign (t+6) (e_val 1w) (o_store res_PC (t+4) (t+5));
   i_assign (t+7) (e_val 1w) (o_internal (e_val 0w));
   i_assign (t+8) (e_val 1w) (o_internal (e_val r1));
   i_assign (t+9) (e_val 1w) (o_internal (e_val r5));
   i_assign (t+10) (e_val 1w) (o_load res_REG (t+9));
   i_assign (t+11) (e_val 1w) (o_store res_REG (t+8) (t+10));
   i_assign (t+12) (e_val 1w) (o_load res_PC (t+7));
   i_assign (t+13) (e_val 1w) (o_internal (e_add (e_name (t+12)) (e_val 4w)));
   i_assign (t+14) (e_val 1w) (o_store res_PC (t+7) (t+13))]
End

Definition example_mov_list:
  example_mov_list a b r1 r5 = example_mov_exe_init a b r1 r5 0
End

Definition example_mov_store:
  example_mov_store a b r5 :num |-> v =
  (FEMPTY |+ (1,r5) |+ (2,a) |+ (3,a) |+ (4,0w) |+ (5,b) |+ (6,b))
End

Definition example_mov_state_st_list:
 example_mov_state_st_list a b r1 r5 =
 State_st_list (example_mov_list a b r1 r5) (example_mov_store a b r5) [] [6]
End

Definition example_mov_maximal_execution:
  example_mov_maximal_execution a b r1 r5 =
  IO_bounded_execution (\v t. []) sem_expr_exe (example_mov_state_st_list a b r1 r5) 7 8
End

Definition example_mov_maximal_trace_aux:
  example_mov_maximal_trace_aux a b r1 r5 =
  IO_bounded_trace_aux (\v t. []) sem_expr_exe (example_mov_state_st_list a b r1 r5) 7 8
End

Definition example_mov_maximal_trace:
  example_mov_maximal_trace a b r1 r5 =
  IO_bounded_trace (\v t. []) sem_expr_exe (example_mov_state_st_list a b r1 r5) 7 8
End

Theorem example_mov_maximal_trace_aux_last_state_all_completed[local]:
  !a b r1 r5.
    all_instructions_completed_list sem_expr_exe
    ((FST o THE) (example_mov_maximal_trace_aux a b r1 r5))
Proof
  rw [] >> EVAL_TAC >> rw [] >> EVAL_TAC
QED

Theorem example_mov_trace_equivalence_implies_same_pc[local]:
  !a1 b1 r1 r5 a1' b1' r1' r5'.
    (example_mov_maximal_trace a1 b1 r1 r5) =
    (example_mov_maximal_trace a1' b1' r1' r5') ==>
    b1 = b1'
Proof
  REPEAT GEN_TAC >> EVAL_TAC >> rw []
QED

Theorem State_st_list_well_formed_ok_example_mov_state_st_list:
  sem_expr = sem_expr_exe ==>
  !a b r1 r5.
    State_st_list_well_formed_ok (example_mov_state_st_list a b r1 r5)
Proof
  rw [State_st_list_well_formed_ok,example_mov_state_st_list,
      example_mov_list,example_mov_exe_init,example_mov_store] >-
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
    fs [val_true],
    fs [] >> rw [] >> fs [names_o],
    fs [sem_instr,sem_expr_correct,FLOOKUP_DEF] >> rw [] >> fs [] >> EVAL_TAC,
    fs [val_true,val_zero],
    fs [],
    `NO_DUPLICATES (example_mov_list a b r1 r5)` by EVAL_TAC >>
    `State_st_list_ok (example_mov_state_st_list a b r1 r5)`
      by fs [example_mov_state_st_list,State_st_list_ok] >>
    `str_may_list sem_expr_exe (example_mov_state_st_list a b r1 r5) 6 = []` by EVAL_TAC >>
    `str_may (state_list_to_state (example_mov_state_st_list a b r1 r5)) 6 =
     LIST_TO_SET (str_may_list sem_expr (example_mov_state_st_list a b r1 r5) 6)`
      by METIS_TAC [str_may_list_correct] >>
    `str_may (state_list_to_state (example_mov_state_st_list a b r1 r5)) 6 = {}`
      by METIS_TAC [LIST_TO_SET] >>
    fs [state_list_to_state,example_mov_state_st_list,
        example_mov_list,example_mov_exe_init,
        example_mov_store,bound_names_program]
  ]
QED

Theorem example_mov_maximal_execution_correct[local]:
  sem_expr = sem_expr_exe ==>
  translate_val_list = (\v t. []) ==>
  !a b r1 r5 pi.
    example_mov_maximal_execution a b r1 r5 = SOME pi ==>
    maximal_execution_form in_order_step (state_list_to_state (example_mov_state_st_list a b r1 r5))
    (MAP step_list_to_step pi)
Proof
  rw [maximal_execution_form] >>
  `State_st_list_well_formed_ok (example_mov_state_st_list a b r1 r5)`
    by rw [State_st_list_well_formed_ok_example_mov_state_st_list] >|[
    `translate_val_list_SORTED` by fs [translate_val_list_SORTED] >>
    fs [example_mov_maximal_execution,example_mov_state_st_list] >>
    `SORTED bound_name_instr_le (example_mov_list a b r1 r5)`
      by (fs [example_mov_list,example_mov_exe_init] >> EVAL_TAC) >>
    `Completed_list_up_to sem_expr (State_st_list (example_mov_list a b r1 r5)
    (example_mov_store a b r5) [] [6]) (PRE 7)`
      by (fs [example_mov_list,example_mov_exe_init,example_mov_store] >>
          EVAL_TAC >> rw [] >> EVAL_TAC) >>
    `DROP (PRE 7) (example_mov_list a b r1 r5) =
    [i_assign 7 (e_val 1w) (o_internal (e_val 0w));
     i_assign 8 (e_val 1w) (o_internal (e_val r1));
     i_assign 9 (e_val 1w) (o_internal (e_val r5));
     i_assign 10 (e_val 1w) (o_load res_REG 9);
     i_assign 11 (e_val 1w) (o_store res_REG 8 10);
     i_assign 12 (e_val 1w) (o_load res_PC 7);
     i_assign 13 (e_val 1w) (o_internal (e_add (e_name 12) (e_val 4w)));
     i_assign 14 (e_val 1w) (o_store res_PC 7 13)]`
      by (fs [example_mov_list,example_mov_exe_init] >> EVAL_TAC) >>
    Q.ABBREV_TAC `i = i_assign 7 (e_val 1w) (o_internal (e_val 0w))` >>
    Q.ABBREV_TAC `il = [i_assign 8 (e_val 1w) (o_internal (e_val r1));
                        i_assign 9 (e_val 1w) (o_internal (e_val r5));
                        i_assign 10 (e_val 1w) (o_load res_REG 9);
                        i_assign 11 (e_val 1w) (o_store res_REG 8 10);
                        i_assign 12 (e_val 1w) (o_load res_PC 7);
                        i_assign 13 (e_val 1w) (o_internal (e_add (e_name 12) (e_val 4w)));
                        i_assign 14 (e_val 1w) (o_store res_PC 7 13)]` >>
    `~(Completed_list sem_expr (State_st_list (example_mov_list a b r1 r5)
    (example_mov_store a b r5) [] [6]) i)`
      by (fs [example_mov_list,example_mov_exe_init,example_mov_store,Abbr `i`] >> EVAL_TAC) >>
    `IO_bounded_execution translate_val_list sem_expr (State_st_list (example_mov_list a b r1 r5)
    (example_mov_store a b r5) [] [6]) 7 (SUC 7) = SOME pi` by fs [] >>
    PROVE_TAC [IO_bounded_execution_in_order_step_sound],

    UNDISCH_TAC ``example_mov_maximal_execution a b r1 r5 = SOME pi`` >>
    EVAL_TAC >> rw [] >> fs [step_list_to_step,state_list_to_state],

    `SND (SND (LAST (MAP step_list_to_step (THE (example_mov_maximal_execution a b r1 r5))))) =
     state_list_to_state (SND (SND (LAST (THE (example_mov_maximal_execution a b r1 r5)))))` by EVAL_TAC >>
    rw [] >>
    `all_instructions_completed_list sem_expr_exe
     (SND (SND (LAST (THE (example_mov_maximal_execution a b r1 r5)))))` by (EVAL_TAC >> rw [] >> EVAL_TAC) >>
    `THE (example_mov_maximal_execution a b r1 r5) = pi` by fs [] >>
    `all_instructions_completed_list sem_expr (SND (SND (LAST pi)))` by fs [] >>
    `?stl'.(SND (SND (LAST pi))) = stl'` by fs [] >>
    `well_formed_state (state_list_to_state stl')`
      by (fs [example_mov_maximal_execution,example_mov_state_st_list] >>
          `DROP (PRE 7) (example_mov_list a b r1 r5) =
          [i_assign 7 (e_val 1w) (o_internal (e_val 0w));
           i_assign 8 (e_val 1w) (o_internal (e_val r1));
           i_assign 9 (e_val 1w) (o_internal (e_val r5));
           i_assign 10 (e_val 1w) (o_load res_REG 9);
           i_assign 11 (e_val 1w) (o_store res_REG 8 10);
           i_assign 12 (e_val 1w) (o_load res_PC 7);
           i_assign 13 (e_val 1w) (o_internal (e_add (e_name 12) (e_val 4w)));
           i_assign 14 (e_val 1w) (o_store res_PC 7 13)]`
            by (fs [example_mov_list,example_mov_exe_init] >> EVAL_TAC) >>
          Q.ABBREV_TAC `i = i_assign 7 (e_val 1w) (o_internal (e_val 0w))` >>
          Q.ABBREV_TAC `il = [i_assign 8 (e_val 1w) (o_internal (e_val r1));
                              i_assign 9 (e_val 1w) (o_internal (e_val r5));
                              i_assign 10 (e_val 1w) (o_load res_REG 9);
                              i_assign 11 (e_val 1w) (o_store res_REG 8 10);
                              i_assign 12 (e_val 1w) (o_load res_PC 7);
                              i_assign 13 (e_val 1w) (o_internal (e_add (e_name 12) (e_val 4w)));
                              i_assign 14 (e_val 1w) (o_store res_PC 7 13)]` >>
          `~(Completed_list sem_expr (State_st_list (example_mov_list a b r1 r5)
          (example_mov_store a b r5) [] [6]) i)`
            by (fs [example_mov_list,example_mov_exe_init,example_mov_store,Abbr `i`] >> EVAL_TAC) >>
          `IO_bounded_execution translate_val_list sem_expr (State_st_list (example_mov_list a b r1 r5)
          (example_mov_store a b r5) [] [6]) 7 (SUC 7) = SOME pi` by fs [] >>
          PROVE_TAC [State_st_list_well_formed_ok_IO_bounded_execution_last_state]) >>
    fs [all_instructions_completed_list_implies_termination_IO]
  ]
QED

Theorem noninterference_example_mov_trace:
  sem_expr = sem_expr_exe ==>
  translate_val_list = (\v t. []) ==>
  !a1 b1 r1 r5 a1' b1' r1' r5' s1 s2.
    state_list_to_state (example_mov_state_st_list a1 b1 r1 r5) = s1 ==>
    state_list_to_state (example_mov_state_st_list a1' b1' r1' r5') = s2 ==>
    trace_indist_IO s1 s2 ==>
    b1 = b1'
Proof
  rw [trace_indist_IO,trace_indist] >>
  `?p1 p2. (example_mov_maximal_execution a1 b1 r1 r5 = SOME p1) /\
  (example_mov_maximal_execution a1' b1' r1' r5' = SOME p2)` by (EVAL_TAC >> rw []) >>
  `maximal_execution_form in_order_step (state_list_to_state
   (example_mov_state_st_list a1 b1 r1 r5)) (MAP step_list_to_step p1) /\
  maximal_execution_form in_order_step (state_list_to_state
   (example_mov_state_st_list a1' b1' r1' r5')) (MAP step_list_to_step p2)`
    by fs [example_mov_maximal_execution_correct] >>
  Q.ABBREV_TAC `stl1 = example_mov_state_st_list a1 b1 r1 r5` >>
  Q.ABBREV_TAC `stl2 = example_mov_state_st_list a1' b1' r1' r5'` >>
  `State_st_list_well_formed_ok stl1 /\ State_st_list_well_formed_ok stl2`
    by fs [Abbr `stl1`,Abbr `stl2`,State_st_list_well_formed_ok_example_mov_state_st_list] >>
  `well_formed_state (state_list_to_state stl1) /\ well_formed_state (state_list_to_state stl2)`
    by (Cases_on `stl1` >> Cases_on `stl2` >> fs [State_st_list_well_formed_ok]) >>
  Q.ABBREV_TAC `s1 = state_list_to_state stl1` >>
  Q.ABBREV_TAC `s2 = state_list_to_state stl2` >>
  Q.ABBREV_TAC `max_org_pi1 = MAP step_list_to_step p1` >>
  Q.ABBREV_TAC `max_org_pi2 = MAP step_list_to_step p2` >>
  `maximal_execution_form in_order_step' s1 (MAP update_lbl max_org_pi1) /\
  maximal_execution_form in_order_step' s2 (MAP update_lbl max_org_pi2)`
    by fs [max_execution_format_step_and_step'] >>
  Q.ABBREV_TAC `max_pi1 = MAP update_lbl max_org_pi1` >>
  Q.ABBREV_TAC `max_pi2 = MAP update_lbl max_org_pi2` >>
  `trace obs_of_l obs_visible max_pi1 = trace obs_of_l obs_visible max_pi2`
    by REWRITE_TAC [UNDISCH_ALL (SPEC_ALL noninterference_implies_maximal_execution_form_in_order_step')] >>
  `trace obs_of_l obs_visible max_org_pi1 = trace obs_of_l obs_visible max_org_pi2` by METIS_TAC [MAP_update_lbl_same_obs,Abbr `max_pi1`,Abbr `max_pi2`] >>
  `example_mov_maximal_trace a1 b1 r1 r5 <> NONE /\
  example_mov_maximal_trace a1' b1' r1' r5' <> NONE` by EVAL_TAC >>
  `?tr1 tr2.example_mov_maximal_trace a1 b1 r1 r5 = SOME tr1 /\
  example_mov_maximal_trace a1' b1' r1' r5' = SOME tr2`
    by (Cases_on `example_mov_maximal_trace a1 b1 r1 r5` >>
        Cases_on `example_mov_maximal_trace a1' b1' r1' r5'` >> fs []) >>
  `(trace obs_of_l obs_visible max_org_pi1 = tr1) /\
  (trace obs_of_l obs_visible max_org_pi2 = tr2)`
    by METIS_TAC [example_mov_maximal_execution,example_mov_maximal_trace,
                  IO_bounded_execution_and_trace,Abbr `max_org_pi1`,Abbr `max_org_pi2`] >>
  `example_mov_maximal_trace a1 b1 r1 r5 = example_mov_maximal_trace a1' b1' r1' r5'` by fs [] >>
  METIS_TAC [example_mov_trace_equivalence_implies_same_pc]
QED

val _ = export_theory ();
