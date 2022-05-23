open HolKernel boolLib Parse bossLib wordsLib wordsTheory finite_mapTheory pred_setTheory relationTheory listTheory rich_listTheory pairTheory milUtilityTheory milTheory milSemanticsUtilityTheory milMetaTheory milTracesTheory milMetaIOTheory milExecutableUtilityTheory milExecutableTransitionTheory milExecutableIOTheory milExecutableIOTraceTheory milExecutableIOCompletenessTheory milExecutableExamplesTheory milNoninterferenceTheory milMaxExeTraceUtilityTheory;

(* ================================================== *)
(*  Maximal execution and trace of example assignment *)
(* ================================================== *)

val _ = new_theory "milMaxExeTraceExampleAssignment";

(* example assignment after initialization *)
(* Variables:
   a: the initial value stored in r1.
   b: the initial value of PC.
   r1: a register address.
   t + n: instruction bounded name.
 *)
Definition example_assignment_exe_init:
  example_assignment_exe_init a b r1 t =
  [i_assign (t+1) (e_val 1w) (o_internal (e_val r1));
   i_assign (t+2) (e_val 1w) (o_internal (e_val a));
   i_assign (t+3) (e_val 1w) (o_store res_REG (t+1) (t+2));
   i_assign (t+4) (e_val 1w) (o_internal (e_val 0w));
   i_assign (t+5) (e_val 1w) (o_internal (e_val b));
   i_assign (t+6) (e_val 1w) (o_store res_PC (t+4) (t+5));
   i_assign (t+7) (e_val 1w) (o_internal (e_val 0w));
   i_assign (t+8) (e_val 1w) (o_internal (e_val r1));
   i_assign (t+9) (e_val 1w) (o_load res_REG (t+8));
   i_assign (t+10) (e_val 1w) (o_internal (e_add (e_name (t+9)) (e_val 1w)));
   i_assign (t+11) (e_val 1w) (o_store res_REG (t+8) (t+10));
   i_assign (t+12) (e_val 1w) (o_load res_PC (t+7));         
   i_assign (t+13) (e_val 1w) (o_internal (e_add (e_name (t+12)) (e_val 4w)));        
   i_assign (t+14) (e_val 1w) (o_store res_PC (t+7) (t+13))]
End

Definition example_assignment_exe_init_store:
 example_assignment_exe_init_store a b r1 t : s =
  (FEMPTY |+ (t+1,r1) |+ (t+2,a) |+ (t+3,a) |+ (t+4,0w) |+ (t+5,b) |+ (t+6,b))
End

Definition example_assignment_exe_init_state_st_list:
  example_assignment_exe_init_state_st_list a b r1 t =
  State_st_list (example_assignment_exe_init a b r1 t)
   (example_assignment_exe_init_store a b r1 t) [] [t+6]
End

Definition example_assignment_maximal_execution:
 example_assignment_maximal_execution a b r1 t =
  let start_pos = 7 in
  let instr_len = 8 in
  IO_bounded_execution (\v t. []) sem_expr_exe (example_assignment_exe_init_state_st_list a b r1 t) start_pos instr_len
End

Definition example_assignment_maximal_trace_aux:
  example_assignment_maximal_trace_aux a b r1 t =
  let start_pos = 7 in
  let instr_len = 8 in
  IO_bounded_trace_aux (\v t. []) sem_expr_exe (example_assignment_exe_init_state_st_list a b r1 t) start_pos instr_len
End

Definition example_assignment_maximal_trace:
  example_assignment_maximal_trace a b r1 t =
  let start_pos = 7 in
  let instr_len = 8 in
  IO_bounded_trace (\v t. []) sem_expr_exe (example_assignment_exe_init_state_st_list a b r1 t) start_pos instr_len
End

Theorem example_assignment_maximal_trace_aux_last_state_all_completed[local]:
 !a b r1.
  all_instructions_completed_list sem_expr_exe
  ((FST o THE) (example_assignment_maximal_trace_aux a b r1 0))
Proof
 rw [] >> EVAL_TAC >> rw [] >> EVAL_TAC
QED

Theorem example_assignment_trace_equivalence_implies_same_pc[local]:
 !a1 b1 r1 a2 b2 r2.
  (example_assignment_maximal_trace a1 b1 r1 0) =
  (example_assignment_maximal_trace a2 b2 r2 0) ==>
   b1 = b2
Proof
 REPEAT GEN_TAC >> EVAL_TAC >> rw []
QED

Theorem State_st_list_well_formed_ok_example_assignment_state_st_list[local]:
  sem_expr = sem_expr_exe ==>
  !a b r1.
    State_st_list_well_formed_ok (example_assignment_exe_init_state_st_list a b r1 0)
Proof
  rw [State_st_list_well_formed_ok,
      example_assignment_exe_init_state_st_list,
      example_assignment_exe_init,example_assignment_exe_init_store] >-
   EVAL_TAC >>
  rw [state_list_to_state] >>
  SIMP_TAC std_ss [well_formed_state] >>
  REPEAT STRIP_TAC >|[
    (* FINITE I *)
    EVAL_TAC,
    (* (C UNION Fs) SUBSET (FDOM s) *)
    EVAL_TAC,
    (* (FDOM s) SUBSET (bound_names_program I) *)
    rw [bound_names_program] >> METIS_TAC [bound_name_instr],
    (* !i. i IN I ==> !t. t IN free_names_instr i ==> t < bound_name_instr i *)
    fs [bound_name_instr] >> rw [] >>
    fs [free_names_instr,names_e,names_o],
    (* !i i'. i IN I ==> i' IN I ==> bound_name_instr i = bound_name_instr i' ==> i = i' *)
    fs [] >> rw [] >> fs [bound_name_instr],
    (* !i. i IN I ==> !t. t IN free_names_instr i ==> ?i'. i' IN I /\ bound_name_instr i' = t *)
    fs [] >> rw [] >> 
    fs [free_names_instr,names_e,names_o] >> METIS_TAC [bound_name_instr],
    (* !t. t IN C ==> ?t1 t2 c. i_assign t c (o_store res_MEM t1 t2) IN I *)
    fs [],
    (* !t. t IN Fs ==> ?t1 t2 c. i_assign t c (o_store res_PC t1 t2) IN I *)
    fs [],
    (* !t c v r t1 t2. i_assign t c (o_store r t1 t2) IN I ==> FLOOKUP s t = SOME v ==> 
       map_down s t1 *)
    fs [map_down,FLOOKUP_DEF],
    (* !t c v r t1 t2. i_assign t c (o_store r t1 t2) IN I ==> FLOOKUP s t = SOME v ==> 
        FLOOKUP s t2 = SOME v *)
    fs [map_down,FLOOKUP_DEF] >> rw [] >> fs [] >> EVAL_TAC,
    (* !t c mop. i_assign t c mop IN I ==> map_down s t ==>
       ?v'. sem_expr c s = SOME v' /\ v' <> val_false *)
    fs [map_down,FLOOKUP_DEF] >> rw [] >> fs [sem_expr_correct,val_false,sem_expr_exe],
    (* !t c ta tv. i_assign t c (o_store res_PC ta tv) IN I ==>
       i_assign ta (e_val val_true) (o_internal (e_val val_zero)) IN I *)
    fs [val_true,val_zero],                  
    (* !t c mop. i_assign t c mop IN I ==>
       !t' c' mop'. t' IN names_e c ==> i_assign t' c' mop' IN I ==> c' = e_val val_true *)
    fs [val_true],
    (* !t c mop. i_assign t c mop IN I ==> !s' v. sem_expr c s' = SOME v ==> v <> val_false ==>
       !t' c' mop' v'. t' IN names_o mop ==> i_assign t' c' mop' IN I ==>
       sem_expr c' s' = SOME v' ==> v' <> val_false *)
    fs [] >> rw [] >> fs [names_o],
    (* !t c e v. i_assign t c (o_internal e) IN I ==> FLOOKUP s t = SOME v ==>
       sem_instr (i_assign t c (o_internal e)) (State_st I s C Fs) = SOME (v,obs_internal) *)
    fs [sem_instr,sem_expr_correct,FLOOKUP_DEF] >> rw [] >> fs [] >> EVAL_TAC,
    (* !t c ta. i_assign t c (o_load res_PC ta) IN I ==>
       i_assign ta (e_val val_true) (o_internal (e_val val_zero)) IN I *)
    fs [val_true,val_zero],
    (* !t. t IN C ==> bound_names_program (str_may (State_st I s C Fs) t) SUBSET C *)
    fs [],
    (* !t. t IN F ==> bound_names_program (str_may (State_st I s C Fs) t) SUBSET F *)  
    `NO_DUPLICATES (example_assignment_exe_init a b r1 0)` by EVAL_TAC >>
    `State_st_list_ok (example_assignment_exe_init_state_st_list a b r1 0)`
      by fs [example_assignment_exe_init_state_st_list,
             example_assignment_exe_init,State_st_list_ok] >>
    `str_may_list sem_expr_exe (example_assignment_exe_init_state_st_list a b r1 0) 6 = []` by EVAL_TAC >>
    `str_may (state_list_to_state (example_assignment_exe_init_state_st_list a b r1 0)) 6 =
     LIST_TO_SET (str_may_list sem_expr (example_assignment_exe_init_state_st_list a b r1 0) 6)`
      by METIS_TAC [str_may_list_correct] >>
    `str_may (state_list_to_state (example_assignment_exe_init_state_st_list a b r1 0)) 6 = {}`
      by METIS_TAC [LIST_TO_SET] >> 
    fs [state_list_to_state,example_assignment_exe_init_state_st_list,
        example_assignment_exe_init,
        example_assignment_exe_init_store,bound_names_program]
  ]
QED

Theorem DROP_example_assignment_exe_init_start_instrs[local]:
  !a b r1 t.
    DROP (PRE 7) (example_assignment_exe_init a b r1 t) =
    [i_assign (t+7) (e_val 1w) (o_internal (e_val 0w));
     i_assign (t+8) (e_val 1w) (o_internal (e_val r1));
     i_assign (t+9) (e_val 1w) (o_load res_REG (t+8));
     i_assign (t+10) (e_val 1w) (o_internal (e_add (e_name (t+9)) (e_val 1w)));
     i_assign (t+11) (e_val 1w) (o_store res_REG (t+8) (t+10));
     i_assign (t+12) (e_val 1w) (o_load res_PC (t+7));
     i_assign (t+13) (e_val 1w) (o_internal (e_add (e_name (t+12)) (e_val 4w)));
     i_assign (t+14) (e_val 1w) (o_store res_PC (t+7) (t+13))]
Proof
  rw [DROP,example_assignment_exe_init]
QED

Theorem SORTED_example_assignment_exe_init[local]:
  !a b r1 t.
    SORTED bound_name_instr_le (example_assignment_exe_init a b r1 t)
Proof
  rw [example_assignment_exe_init,bound_name_instr_le,name_le,bound_name_instr]
QED

Theorem Completed_list_up_to_starting_pos_example_assignment_exe_init_state[local]:
  !a b r1 t.
   Completed_list_up_to sem_expr (example_assignment_exe_init_state_st_list a b r1 t) (PRE 7)
Proof
  rw [example_assignment_exe_init_state_st_list,example_assignment_exe_init,
      example_assignment_exe_init_store,Completed_list_up_to] >>
  rw [Completed_list] >> fs [FLOOKUP_DEF]
QED

Theorem example_assignment_maximal_execution_correct[local]:
  sem_expr = sem_expr_exe ==>
  translate_val_list = (\v t. []) ==>
  !a b r1 pi.
    example_assignment_maximal_execution a b r1 0 = SOME pi ==>
    maximal_execution_form in_order_step
     (state_list_to_state (example_assignment_exe_init_state_st_list a b r1 0))
    (MAP step_list_to_step pi)                             
Proof
  rw [maximal_execution_form] >>
  `State_st_list_well_formed_ok (example_assignment_exe_init_state_st_list a b r1 0)`
   by rw [State_st_list_well_formed_ok_example_assignment_state_st_list] >|[
   `translate_val_list_SORTED` by fs [translate_val_list_SORTED] >>
    fs [example_assignment_maximal_execution,example_assignment_exe_init_state_st_list] >>
   `SORTED bound_name_instr_le (example_assignment_exe_init a b r1 0)`
    by rw [SORTED_example_assignment_exe_init] >>
   sg `Completed_list_up_to sem_expr (State_st_list (example_assignment_exe_init a b r1 0)
      (example_assignment_exe_init_store a b r1 0) [] [6]) (PRE 7)` >-
    (`Completed_list_up_to sem_expr (example_assignment_exe_init_state_st_list a b r1 0) (PRE 7)`
     by rw [Completed_list_up_to_starting_pos_example_assignment_exe_init_state] >>
     fs [example_assignment_exe_init_state_st_list] >> METIS_TAC []) >>
   MP_TAC (Q.SPECL [`a`,`b`,`r1`,`0`] DROP_example_assignment_exe_init_start_instrs) >>
   REWRITE_TAC [arithmeticTheory.ADD] >> STRIP_TAC >> 
   Q.ABBREV_TAC `i = i_assign 7 (e_val 1w) (o_internal (e_val 0w))` >>
   Q.ABBREV_TAC `il = [i_assign 8 (e_val 1w) (o_internal (e_val r1));
         i_assign 9 (e_val 1w) (o_load res_REG 8);
         i_assign 10 (e_val 1w) (o_internal (e_add (e_name 9) (e_val 1w)));
         i_assign 11 (e_val 1w) (o_store res_REG 8 10);
         i_assign 12 (e_val 1w) (o_load res_PC 7);
         i_assign 13 (e_val 1w) (o_internal (e_add (e_name 12) (e_val 4w)));
         i_assign 14 (e_val 1w) (o_store res_PC 7 13)]` >>
   `~(Completed_list sem_expr (State_st_list (example_assignment_exe_init a b r1 0)
       (example_assignment_exe_init_store a b r1 0) [] [6]) i)`
    by (fs [example_assignment_exe_init,example_assignment_exe_init_store,Abbr `i`] >> EVAL_TAC) >>
   `IO_bounded_execution translate_val_list sem_expr (State_st_list (example_assignment_exe_init a b r1 0)
    (example_assignment_exe_init_store a b r1 0) [] [6]) 7 (SUC 7) = SOME pi` by fs [] >>
   PROVE_TAC [IO_bounded_execution_in_order_step_sound],
              
   UNDISCH_TAC ``example_assignment_maximal_execution a b r1 0 = SOME pi`` >>
   EVAL_TAC >> rw [] >> fs [step_list_to_step,state_list_to_state],

   `SND (SND (LAST (MAP step_list_to_step (THE (example_assignment_maximal_execution a b r1 0))))) =
    state_list_to_state (SND (SND (LAST (THE (example_assignment_maximal_execution a b r1 0)))))`
    by EVAL_TAC >>
   rw [] >>
   `all_instructions_completed_list sem_expr_exe
     (SND (SND (LAST (THE (example_assignment_maximal_execution a b r1 0)))))`
    by (EVAL_TAC >> rw [] >> EVAL_TAC) >>
   `THE (example_assignment_maximal_execution a b r1 0) = pi` by fs [] >>
   `all_instructions_completed_list sem_expr (SND (SND (LAST pi)))` by fs [] >>       
   `?stl'.(SND (SND (LAST pi))) = stl'` by fs [] >>  
   sg `well_formed_state (state_list_to_state stl')` >-
    (fs [example_assignment_maximal_execution,example_assignment_exe_init_state_st_list] >>
     MP_TAC (Q.SPECL [`a`,`b`,`r1`,`0`] DROP_example_assignment_exe_init_start_instrs) >>
     REWRITE_TAC [arithmeticTheory.ADD] >> STRIP_TAC >>
     Q.ABBREV_TAC `i = i_assign 7 (e_val 1w) (o_internal (e_val 0w))` >>
     Q.ABBREV_TAC `il = [i_assign 8 (e_val 1w) (o_internal (e_val r1));
                         i_assign 9 (e_val 1w) (o_load res_REG 8);
                         i_assign 10 (e_val 1w) (o_internal (e_add (e_name 9) (e_val 1w)));
                         i_assign 11 (e_val 1w) (o_store res_REG 8 10);                   
                         i_assign 12 (e_val 1w) (o_load res_PC 7);          
                         i_assign 13 (e_val 1w) (o_internal (e_add (e_name 12) (e_val 4w)));     
                         i_assign 14 (e_val 1w) (o_store res_PC 7 13)]` >>                
     `~(Completed_list sem_expr 
        (State_st_list (example_assignment_exe_init a b r1 0)
         (example_assignment_exe_init_store a b r1 0) [] [6]) i)`                            
       by (fs [Abbr `i`] >> EVAL_TAC) >>
     `IO_bounded_execution translate_val_list sem_expr
      (State_st_list (example_assignment_exe_init a b r1 0)
       (example_assignment_exe_init_store a b r1 0) [] [6]) 7 (SUC 7) = SOME pi` by fs [] >>
     PROVE_TAC [State_st_list_well_formed_ok_IO_bounded_execution_last_state]) >>
   fs [all_instructions_completed_list_implies_termination_IO]
  ]
QED

Theorem noninterference_example_assignment_trace[local]:
  sem_expr = sem_expr_exe ==>
  translate_val_list = (\v t. []) ==>
  !a1 b1 r1 a2 b2 r2 s1 s2.
    state_list_to_state (example_assignment_exe_init_state_st_list a1 b1 r1 0) = s1 ==>
    state_list_to_state (example_assignment_exe_init_state_st_list a2 b2 r2 0) = s2 ==>
    trace_indist_IO s1 s2 ==>
    b1 = b2
Proof
  rw [trace_indist_IO,trace_indist] >>
  `?p1 p2. (example_assignment_maximal_execution a1 b1 r1 0 = SOME p1) /\
  (example_assignment_maximal_execution a2 b2 r2 0 = SOME p2)` by (EVAL_TAC >> rw []) >>
  `maximal_execution_form in_order_step (state_list_to_state
   (example_assignment_exe_init_state_st_list a1 b1 r1 0)) (MAP step_list_to_step p1) /\
  maximal_execution_form in_order_step (state_list_to_state
   (example_assignment_exe_init_state_st_list a2 b2 r2 0)) (MAP step_list_to_step p2)`
    by fs [example_assignment_maximal_execution_correct] >>
  Q.ABBREV_TAC `stl1 = example_assignment_exe_init_state_st_list a1 b1 r1 0` >>
  Q.ABBREV_TAC `stl2 = example_assignment_exe_init_state_st_list a2 b2 r2 0` >>           
  `State_st_list_well_formed_ok stl1 /\ State_st_list_well_formed_ok stl2`
    by fs [Abbr `stl1`,Abbr `stl2`,State_st_list_well_formed_ok_example_assignment_state_st_list] >>
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
  `example_assignment_maximal_trace a1 b1 r1 0 <> NONE /\
  example_assignment_maximal_trace a2 b2 r2 0 <> NONE` by EVAL_TAC >>
  `?tr1 tr2.example_assignment_maximal_trace a1 b1 r1 0 = SOME tr1 /\
    example_assignment_maximal_trace a2 b2 r2 0 = SOME tr2`
   by (Cases_on `example_assignment_maximal_trace a1 b1 r1 0` >>
    Cases_on `example_assignment_maximal_trace a2 b2 r2 0` >> fs []) >>
  `(trace obs_of_l obs_visible max_org_pi1 = tr1) /\
    (trace obs_of_l obs_visible max_org_pi2 = tr2)`
    by (fs [example_assignment_maximal_execution,example_assignment_maximal_trace] >>
       METIS_TAC[IO_bounded_execution_and_trace,Abbr `max_org_pi1`,Abbr `max_org_pi2`]) >>
  `example_assignment_maximal_trace a1 b1 r1 0 = example_assignment_maximal_trace a2 b2 r2 0` by fs [] >>
  METIS_TAC [example_assignment_trace_equivalence_implies_same_pc]
QED
                  
val _ = export_theory ();
