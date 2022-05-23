open HolKernel boolLib Parse bossLib wordsLib wordsTheory finite_mapTheory pred_setTheory relationTheory listTheory rich_listTheory pairTheory milUtilityTheory milTheory milSemanticsUtilityTheory milMetaTheory milTracesTheory milMetaIOTheory milExecutableUtilityTheory milExecutableTransitionTheory milExecutableIOTheory milExecutableIOTraceTheory milExecutableIOCompletenessTheory milExecutableExamplesTheory milNoninterferenceTheory milMaxExeTraceUtilityTheory;

(* ================================================== *)
(*  Maximal execution and trace of example spectreOoO *)
(* ================================================== *)

val _ = new_theory "milMaxExeTraceExampleSpectreOOO";

(* example Spectre OoO after initialization *)
Definition example_spectre_OoO_exe_init:
  example_spectre_OoO_exe_init a b c d r1 r2 z b1 b2 t =
  [i_assign (t+1) (e_val 1w) (o_internal (e_val b1));
   i_assign (t+2) (e_val 1w) (o_internal (e_val a));
   i_assign (t+3) (e_val 1w) (o_store res_MEM (t+1) (t+2));        
   i_assign (t+4) (e_val 1w) (o_internal (e_val z));      
   i_assign (t+5) (e_val 1w) (o_internal (e_val b));       
   i_assign (t+6) (e_val 1w) (o_store res_REG (t+4) (t+5)); 
   i_assign (t+7) (e_val 1w) (o_internal (e_val r2));         
   i_assign (t+8) (e_val 1w) (o_internal (e_val c));
   i_assign (t+9) (e_val 1w) (o_store res_REG (t+7) (t+8));    
   i_assign (t+10) (e_val 1w) (o_internal (e_val 0w));
   i_assign (t+11) (e_val 1w) (o_internal (e_val d));
   i_assign (t+12) (e_val 1w) (o_store res_PC (t+10) (t+11));   
   i_assign (t+13) (e_val 1w) (o_internal (e_val 0w));   
   i_assign (t+14) (e_val 1w) (o_internal (e_val r1));  
   i_assign (t+15) (e_val 1w) (o_internal (e_val r2));  
   i_assign (t+16) (e_val 1w) (o_internal (e_val z)); 
   i_assign (t+17) (e_val 1w) (o_internal (e_val b1));
   i_assign (t+18) (e_val 1w) (o_internal (e_val b2));
   i_assign (t+19) (e_val 1w) (o_load res_MEM (t+17));
   i_assign (t+20) (e_val 1w) (o_store res_REG (t+14) (t+19));
   i_assign (t+21) (e_val 1w) (o_load res_REG (t+16));
   i_assign (t+22) (e_eq (e_name (t+21)) (e_val 1w)) (o_load res_REG (t+14));
   i_assign (t+23) (e_eq (e_name (t+21)) (e_val 1w)) (o_store res_REG (t+15) (t+22));
   i_assign (t+24) (e_val 1w) (o_load res_REG (t+15));
   i_assign (t+25) (e_val 1w) (o_store res_MEM (t+18) (t+24)); 
   i_assign (t+26) (e_val 1w) (o_load res_PC (t+13));
   i_assign (t+27) (e_val 1w) (o_internal (e_add (e_name (t+26)) (e_val 4w)));          
   i_assign (t+28) (e_val 1w) (o_store res_PC (t+13) (t+27))]
End
   
Definition example_spectre_OoO_list:
  example_spectre_OoO_list a b c d r1 r2 z b1 b2 = example_spectre_OoO_exe_init a b c d r1 r2 z b1 b2 0
End

Definition example_spectre_OoO_store:
  example_spectre_OoO_store a b c d r2 z b1 : num |-> v =
  (FEMPTY |+ (1,b1) |+ (2,a) |+ (3,a) |+ (4,z) |+ (5,b) |+ (6,b) |+
   (7,r2) |+ (8,c) |+ (9,c) |+ (10,0w) |+ (11,d) |+ (12,d))
End

Definition example_spectre_OoO_state_st_list:
  example_spectre_OoO_state_st_list a b c d r1 r2 z b1 b2 =
  State_st_list (example_spectre_OoO_list a b c d r1 r2 z b1 b2)
  (example_spectre_OoO_store a b c d r2 z b1) [3] [12]
End

Definition example_spectre_OoO_state_st_list_final:
  example_spectre_OoO_state_st_list_final a b c d b1 b2 =
  State_st_list
          [i_assign 1 (e_val 1w) (o_internal (e_val b1));
           i_assign 2 (e_val 1w) (o_internal (e_val a));
           i_assign 3 (e_val 1w) (o_store res_MEM 1 2);
           i_assign 4 (e_val 1w) (o_internal (e_val 3w));
           i_assign 5 (e_val 1w) (o_internal (e_val b));
           i_assign 6 (e_val 1w) (o_store res_REG 4 5);
           i_assign 7 (e_val 1w) (o_internal (e_val 2w));
           i_assign 8 (e_val 1w) (o_internal (e_val c));
           i_assign 9 (e_val 1w) (o_store res_REG 7 8);
           i_assign 10 (e_val 1w) (o_internal (e_val 0w));
           i_assign 11 (e_val 1w) (o_internal (e_val d));
           i_assign 12 (e_val 1w) (o_store res_PC 10 11);
           i_assign 13 (e_val 1w) (o_internal (e_val 0w));
           i_assign 14 (e_val 1w) (o_internal (e_val 1w));
           i_assign 15 (e_val 1w) (o_internal (e_val 2w));
           i_assign 16 (e_val 1w) (o_internal (e_val 3w));
           i_assign 17 (e_val 1w) (o_internal (e_val b1));
           i_assign 18 (e_val 1w) (o_internal (e_val b2));
           i_assign 19 (e_val 1w) (o_load res_MEM 17);
           i_assign 20 (e_val 1w) (o_store res_REG 14 19);
           i_assign 21 (e_val 1w) (o_load res_REG 16);
           i_assign 22 (e_eq (e_name 21) (e_val 1w)) (o_load res_REG 14);
           i_assign 23 (e_eq (e_name 21) (e_val 1w)) (o_store res_REG 15 22);
           i_assign 24 (e_val 1w) (o_load res_REG 15);
           i_assign 25 (e_val 1w) (o_store res_MEM 18 24);
           i_assign 26 (e_val 1w) (o_load res_PC 13);
           i_assign 27 (e_val 1w) (o_internal (e_add (e_name 26) (e_val 4w)));
           i_assign 28 (e_val 1w) (o_store res_PC 13 27)]
          (FEMPTY |+ (1,b1) |+ (2,a) |+ (3,a) |+ (4,3w) |+ (5,b) |+
           (6,b) |+ (7,2w) |+ (8,c) |+ (9,c) |+ (10,0w) |+ (11,d) |+
           (12,d) |+ (13,0w) |+ (14,1w) |+ (15,2w) |+ (16,3w) |+ (17,b1) |+
           (18,b2) |+ (19,a) |+ (20,a) |+ (21,b) |+ (24,c) |+ (25,c) |+
           (26,d) |+ (27,d + 4w) |+ (28,d + 4w)) [25; 3] [28; 12]
End

(* Use 1 - 5 for r1, r2, z, a, b to execute
 * a, b, c and d are initial values for b1, z, r2, PC respectively.
 *)
Definition example_spectre_OoO_maximal_execution:
  example_spectre_OoO_maximal_execution a b c d b1 b2 =
  IO_bounded_execution (\v t. []) sem_expr_exe
  (example_spectre_OoO_state_st_list a b c d 1w 2w 3w b1 b2) 13 16
End

Definition example_spectre_OoO_maximal_trace_aux:
  example_spectre_OoO_maximal_trace_aux a b c d b1 b2 =
  IO_bounded_trace_aux (\v t. []) sem_expr_exe
  (example_spectre_OoO_state_st_list a b c d 1w 2w 3w b1 b2) 13 16
End

Definition example_spectre_OoO_maximal_trace:
  example_spectre_OoO_maximal_trace a b c d b1 b2 =
  IO_bounded_trace (\v t. []) sem_expr_exe
  (example_spectre_OoO_state_st_list a b c d 1w 2w 3w b1 b2) 13 16
End                                     

Theorem IO_bounded_trace_last_example_spectre_OoO[local]:
  translate_val_list = (\v t. []) ==>
  sem_expr = sem_expr_exe ==>
  !f_tran stl' tr a b c d b1 b2.
    IO_bounded_trace_acc (\v t. []) sem_expr_exe (example_spectre_OoO_state_st_list a b c d 1w 2w 3w b1 b2) 12 16 [] = SOME (stl',tr) ==>
    SND (SND (LAST (THE (IO_bounded_execution_acc (\v t. []) sem_expr_exe
    (example_spectre_OoO_state_st_list a b c d 1w 2w 3w b1 b2) 12 16 [])))) = stl'
Proof
  rw [example_spectre_OoO_state_st_list] >>
  `DROP 12 (example_spectre_OoO_list a b c d 1w 2w 3w b1 b2) =
    [i_assign 13 (e_val 1w) (o_internal (e_val 0w));
     i_assign 14 (e_val 1w) (o_internal (e_val 1w));
     i_assign 15 (e_val 1w) (o_internal (e_val 2w));
     i_assign 16 (e_val 1w) (o_internal (e_val 3w));
     i_assign 17 (e_val 1w) (o_internal (e_val b1));
     i_assign 18 (e_val 1w) (o_internal (e_val b2));
     i_assign 19 (e_val 1w) (o_load res_MEM 17);
     i_assign 20 (e_val 1w) (o_store res_REG 14 19);
     i_assign 21 (e_val 1w) (o_load res_REG 16);
     i_assign 22 (e_eq (e_name 21) (e_val 1w)) (o_load res_REG 14);
     i_assign 23 (e_eq (e_name 21) (e_val 1w)) (o_store res_REG 15 22);
     i_assign 24 (e_val 1w) (o_load res_REG 15);
     i_assign 25 (e_val 1w) (o_store res_MEM 18 24);
     i_assign 26 (e_val 1w) (o_load res_PC 13);
     i_assign 27 (e_val 1w) (o_internal (e_add (e_name 26) (e_val 4w)));
     i_assign 28 (e_val 1w) (o_store res_PC 13 27)]`
      by (fs [example_spectre_OoO_list,example_spectre_OoO_exe_init] >> EVAL_TAC) >>
    Q.ABBREV_TAC `i = i_assign 13 (e_val 1w) (o_internal (e_val 0w))` >>
    Q.ABBREV_TAC `il = [i_assign 14 (e_val 1w) (o_internal (e_val 1w));
                        i_assign 15 (e_val 1w) (o_internal (e_val 2w));               
                        i_assign 16 (e_val 1w) (o_internal (e_val 3w));
                        i_assign 17 (e_val 1w) (o_internal (e_val b1));
                        i_assign 18 (e_val 1w) (o_internal (e_val b2));
                        i_assign 19 (e_val 1w) (o_load res_MEM 17);
                        i_assign 20 (e_val 1w) (o_store res_REG 14 19);
                        i_assign 21 (e_val 1w) (o_load res_REG 16);
                        i_assign 22 (e_eq (e_name 21) (e_val 1w)) (o_load res_REG 14);
                        i_assign 23 (e_eq (e_name 21) (e_val 1w)) (o_store res_REG 15 22);
                        i_assign 24 (e_val 1w) (o_load res_REG 15);
                        i_assign 25 (e_val 1w) (o_store res_MEM 18 24);
                        i_assign 26 (e_val 1w) (o_load res_PC 13);
                        i_assign 27 (e_val 1w) (o_internal (e_add (e_name 26) (e_val 4w)));
                        i_assign 28 (e_val 1w) (o_store res_PC 13 27)]` >>
  `~(Completed_list sem_expr (State_st_list (example_spectre_OoO_list a b c d 1w 2w 3w b1 b2)
  (example_spectre_OoO_store a b c d 2w 3w b1) [3] [12]) i)`                            
    by (fs [example_spectre_OoO_list,example_spectre_OoO_exe_init,example_spectre_OoO_store,Abbr `i`] >> EVAL_TAC) >>
  `?x. IO_bounded_execution_acc (\v t. []) sem_expr_exe
  (State_st_list (example_spectre_OoO_list a b c d 1w 2w 3w b1 b2)
   (example_spectre_OoO_store a b c d 2w 3w b1) [3] [12]) 12 16 [] = SOME x`
  by METIS_TAC [IO_bounded_trace_execution_acc_SOME] >> fs [] >>
  `IO_bounded_execution_acc translate_val_list sem_expr
   (State_st_list (example_spectre_OoO_list a b c d 1w 2w 3w b1 b2)
   (example_spectre_OoO_store a b c d 2w 3w b1) [3] [12]) 12 (SUC 15) [] = SOME x` by fs [] >>
  `IO_bounded_trace_acc translate_val_list sem_expr
   (State_st_list (example_spectre_OoO_list a b c d 1w 2w 3w b1 b2)
    (example_spectre_OoO_store a b c d 2w 3w b1) [3] [12]) 12 (SUC 15) [] = SOME (stl',tr)` by fs [] >>
  Q.ABBREV_TAC `l = example_spectre_OoO_list a b c d 1w 2w 3w b1 b2` >>
  Q.ABBREV_TAC `s = example_spectre_OoO_store a b c d 2w 3w b1` >>
  PROVE_TAC [IO_bounded_trace_acc_empty_LAST]
QED

Theorem example_spectre_OoO_IO_bounded_trace_acc_not_true[local]:
  !a b c d b1 b2.
    b <> 1w ==>
    IO_bounded_trace_acc (\v t. []) sem_expr_exe
    (example_spectre_OoO_state_st_list a b c d 1w 2w 3w b1 b2) 12 16 [] =
    SOME (example_spectre_OoO_state_st_list_final a b c d b1 b2,
           [obs_dl b1; obs_ds b2; obs_il (d + 4w)])
Proof
  rw [example_spectre_OoO_state_st_list,Once IO_bounded_trace_acc,example_spectre_OoO_list,
      example_spectre_OoO_exe_init,example_spectre_OoO_store,
      FLOOKUP_DEF,OoO_Ftc_list_stored_incomplete] >>
  NTAC 6 (fs [Once IO_bounded_trace_acc,FLOOKUP_DEF,sem_expr_exe,val_false,sem_instr_exe,sem_expr_exe,
              OoO_Exe_list_instr_not_stored_guard_true_sem_instr,obs_of_ll,obs_visible]) >>  
  fs [Once IO_bounded_trace_acc] >>
  fs [Once FLOOKUP_DEF,sem_expr_exe,val_false,sem_instr_exe,sem_expr_exe] >>
  qmatch_goalsub_abbrev_tac `State_st_list instr_list store _ _` >>
  `str_act_list sem_expr_exe (State_st_list instr_list store [3] [12]) 19 =
  [i_assign 3 (e_val 1w) (o_store res_MEM 1 2)]` by (fs [Abbr `instr_list`,Abbr `store`] >> EVAL_TAC) >>
  fs [bound_names_program_list,bound_name_instr,FLOOKUP_DEF,
      OoO_Exe_list_instr_not_stored_guard_true_sem_instr,obs_of_ll,obs_visible,Abbr `store`] >>
  qmatch_goalsub_abbrev_tac `store ' 3` >>
  `store ' 3 = a` by (fs [Abbr `store`] >> EVAL_TAC) >>
  `store ' 17 = b1` by (fs [Abbr `store`] >> EVAL_TAC) >> fs [Abbr `instr_list`,Abbr `store`] >> 
  fs [Once IO_bounded_trace_acc] >>
  fs [FLOOKUP_DEF,sem_expr_exe,val_false,sem_instr_exe,sem_expr_exe,
      OoO_Exe_list_instr_not_stored_guard_true_sem_instr,obs_of_ll,obs_visible] >>
  fs [Once IO_bounded_trace_acc] >>
  fs [Once FLOOKUP_DEF,sem_expr_exe,val_false,sem_instr_exe,sem_expr_exe] >>
  qmatch_goalsub_abbrev_tac `State_st_list instr_list store _ _` >>
  `str_act_list sem_expr_exe (State_st_list instr_list store [3] [12]) 21 =
  [i_assign 6 (e_val 1w) (o_store res_REG 4 5)]` by (fs [Abbr `instr_list`,Abbr `store`] >> EVAL_TAC) >>
  fs [bound_names_program_list,bound_name_instr,Once FLOOKUP_DEF,Abbr `store`] >>
  fs [Once FLOOKUP_DEF,OoO_Exe_list_instr_not_stored_guard_true_sem_instr,
      obs_of_ll,obs_visible,Abbr `instr_list`] >>
  fs [Once IO_bounded_trace_acc] >>
  fs [FLOOKUP_DEF,sem_expr_exe,v_eq,val_false] >>
  qmatch_goalsub_abbrev_tac `store ' 6` >>
  `store ' 6 = b` by (fs [Abbr `store`] >> EVAL_TAC) >> fs [Abbr `store`] >>
  NTAC 3 (rw [Once IO_bounded_trace_acc] >> fs [FLOOKUP_DEF,sem_expr_exe,v_eq,val_false]) >>
  rw [Once sem_instr_exe] >>
  fs [str_act_list,addr_of_list,FIND_instr,bound_name_instr,str_may_list] >>
  qmatch_goalsub_abbrev_tac `State_st_list instr_list store _ _` >>
  `str_may_list_find sem_expr_exe instr_list store 24 res_REG 15 = [i_assign 9 (e_val 1w) (o_store res_REG 7 8)]`
    by (fs [Abbr `instr_list`,Abbr `store`] >>EVAL_TAC >> fs []) >>
  fs [str_act_list_find,str_act_list_cond,sem_expr_exe,Abbr `instr_list`,Abbr `store`] >>
  NTAC 3 (rw [Once FLOOKUP_DEF]) >>
  fs [bound_names_program_list] >>
  rw [Once FLOOKUP_DEF] >>
  fs [bound_name_instr,FLOOKUP_DEF,OoO_Exe_list_instr_not_stored_guard_true_sem_instr,
      obs_visible,obs_of_ll] >>
  EVAL_TAC >>
  Cases_on `b1 = b2` >> fs [] >> EVAL_TAC      
QED

Theorem example_spectre_OoO_maximal_execution_last_state_all_completed[local]:
  translate_val_list = (\v t. []) ==>
  sem_expr = sem_expr_exe ==>
  !a b c d b1 b2.
    all_instructions_completed_list sem_expr_exe
    (SND (SND (LAST (THE (example_spectre_OoO_maximal_execution a b c d b1 b2)))))
Proof
  rw [] >>
  Cases_on `b = 1w` >-
   (rw [] >> EVAL_TAC >> Cases_on `b1 <> b2` >> fs [] >> EVAL_TAC >> rw [] >> EVAL_TAC) >>
  rw [example_spectre_OoO_maximal_execution,IO_bounded_execution] >>
  `IO_bounded_trace_acc (\v t. []) sem_expr_exe
  (example_spectre_OoO_state_st_list a b c d 1w 2w 3w b1 b2) 12 16 [] =
  SOME (example_spectre_OoO_state_st_list_final a b c d b1 b2,
        [obs_dl b1; obs_ds b2; obs_il (d + 4w)])`
    by fs [example_spectre_OoO_IO_bounded_trace_acc_not_true] >>
  `SND (SND (LAST (THE (IO_bounded_execution_acc (\v t. []) sem_expr_exe
  (example_spectre_OoO_state_st_list a b c d 1w 2w 3w b1 b2) 12 16 [])))) =
  example_spectre_OoO_state_st_list_final a b c d b1 b2`
    by METIS_TAC [IO_bounded_trace_last_example_spectre_OoO] >>
  rw [example_spectre_OoO_state_st_list_final] >> EVAL_TAC >> rw [] >> EVAL_TAC >> fs []
QED

Theorem State_st_list_well_formed_ok_example_spectre_OoO_state_st_list:
  sem_expr_exe = sem_expr ==>
  !a b c d b1 b2.
    State_st_list_well_formed_ok (example_spectre_OoO_state_st_list a b c d 1w 2w 3w b1 b2)
Proof
  rw [State_st_list_well_formed_ok,example_spectre_OoO_state_st_list,
      example_spectre_OoO_list,example_spectre_OoO_exe_init,example_spectre_OoO_store] >-
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
    fs [map_down,FLOOKUP_DEF] >> rw [] >> fs [sem_expr_correct,val_false],
    fs [val_true,val_zero],                  
    fs [val_true] >> rw [] >> fs [names_e],
    fs [] >> rw [] >> fs [names_o,names_e,sem_expr_correct,val_false],
    fs [sem_instr,sem_expr_correct,FLOOKUP_DEF] >> rw [] >> fs [] >> EVAL_TAC,
    fs [val_true,val_zero],
    (* sem_expr = sem_expr_exe needed here *)
    `NO_DUPLICATES (example_spectre_OoO_list a b c d 1w 2w 3w b1 b2)`
      by (fs [example_spectre_OoO_state_st_list] >> EVAL_TAC) >>
    `State_st_list_ok (example_spectre_OoO_state_st_list a b c d 1w 2w 3w b1 b2)`
      by fs [example_spectre_OoO_state_st_list,State_st_list_ok] >>
    `str_may_list sem_expr_exe (example_spectre_OoO_state_st_list a b c d 1w 2w 3w b1 b2) 3 = []` by EVAL_TAC >>
    `str_may (state_list_to_state (example_spectre_OoO_state_st_list a b c d 1w 2w 3w b1 b2)) 3 =
     LIST_TO_SET (str_may_list sem_expr (example_spectre_OoO_state_st_list a b c d 1w 2w 3w b1 b2) 3)`
      by METIS_TAC [str_may_list_correct] >>
    `str_may (state_list_to_state (example_spectre_OoO_state_st_list a b c d 1w 2w 3w b1 b2)) 3 = {}`
      by METIS_TAC [LIST_TO_SET] >> 
    fs [state_list_to_state,example_spectre_OoO_state_st_list,
        example_spectre_OoO_list,example_spectre_OoO_exe_init,
        example_spectre_OoO_store,bound_names_program],
    `NO_DUPLICATES (example_spectre_OoO_list a b c d 1w 2w 3w b1 b2)`
      by (fs [example_spectre_OoO_state_st_list] >> EVAL_TAC) >>
    `State_st_list_ok (example_spectre_OoO_state_st_list a b c d 1w 2w 3w b1 b2)`
      by fs [example_spectre_OoO_state_st_list,State_st_list_ok] >>
    `str_may_list sem_expr_exe (example_spectre_OoO_state_st_list a b c d 1w 2w 3w b1 b2) 12 = []` by EVAL_TAC >>
    `str_may (state_list_to_state (example_spectre_OoO_state_st_list a b c d 1w 2w 3w b1 b2)) 12 =
     LIST_TO_SET (str_may_list sem_expr (example_spectre_OoO_state_st_list a b c d 1w 2w 3w b1 b2) 12)`
      by METIS_TAC [str_may_list_correct] >>
    `str_may (state_list_to_state (example_spectre_OoO_state_st_list a b c d 1w 2w 3w b1 b2)) 12 = {}`
      by METIS_TAC [LIST_TO_SET] >> 
    fs [state_list_to_state,example_spectre_OoO_state_st_list,
        example_spectre_OoO_list,example_spectre_OoO_exe_init,
        example_spectre_OoO_store,bound_names_program]
  ]
QED

Theorem HD_MAP_step_list_to_step_and_state_list_to_state[local]:
  !pi stl.
    pi <> [] ==>
    FST (HD pi) = stl ==>
    FST (HD (MAP step_list_to_step pi)) = state_list_to_state stl
Proof
  Cases_on `pi` >> rw [] >>
  Cases_on `h` >> Cases_on `r` >> rw [step_list_to_step]
QED

Theorem LAST_MAP_step_list_to_step_and_state_list_to_state[local]:
  !pi.
    pi <> [] ==>
    SND (SND (LAST (MAP step_list_to_step pi))) = state_list_to_state (SND (SND (LAST pi))) 
Proof
  Cases_on `pi` >> rw [LAST_MAP] >>
  Cases_on `LAST (h::t)` >> Cases_on `r` >> rw [step_list_to_step]
QED

Theorem example_spectre_OoO_maximal_execution_sound[local]:
  sem_expr = sem_expr_exe ==>
  translate_val_list = (\v t. []) ==>
  !a b c d b1 b2 pi.
    example_spectre_OoO_maximal_execution a b c d b1 b2 = SOME pi ==>
    State_st_list_well_formed_ok (example_spectre_OoO_state_st_list a b c d 1w 2w 3w b1 b2) ==>
    step_execution in_order_step (MAP step_list_to_step pi) /\
    FST (HD pi) = example_spectre_OoO_state_st_list a b c d 1w 2w 3w b1 b2
Proof
   rw [] >>
   `translate_val_list_SORTED` by fs [translate_val_list_SORTED] >>
    fs [example_spectre_OoO_maximal_execution,example_spectre_OoO_state_st_list] >>
    `SORTED bound_name_instr_le (example_spectre_OoO_list a b c d 1w 2w 3w b1 b2)` by (fs [] >> EVAL_TAC) >>
    `Completed_list_up_to sem_expr (State_st_list (example_spectre_OoO_list a b c d 1w 2w 3w b1 b2)
    (example_spectre_OoO_store a b c d 2w 3w b1) [3] [12]) (PRE 13)`                               
      by (fs [example_spectre_OoO_list,example_spectre_OoO_exe_init,example_spectre_OoO_store] >> EVAL_TAC >> rw [] >> EVAL_TAC) >>
    `DROP (PRE 13) (example_spectre_OoO_list a b c d 1w 2w 3w b1 b2) =
    [i_assign 13 (e_val 1w) (o_internal (e_val 0w));
     i_assign 14 (e_val 1w) (o_internal (e_val 1w));
     i_assign 15 (e_val 1w) (o_internal (e_val 2w));
     i_assign 16 (e_val 1w) (o_internal (e_val 3w));
     i_assign 17 (e_val 1w) (o_internal (e_val b1));
     i_assign 18 (e_val 1w) (o_internal (e_val b2));
     i_assign 19 (e_val 1w) (o_load res_MEM 17);
     i_assign 20 (e_val 1w) (o_store res_REG 14 19);
     i_assign 21 (e_val 1w) (o_load res_REG 16);
     i_assign 22 (e_eq (e_name 21) (e_val 1w)) (o_load res_REG 14);
     i_assign 23 (e_eq (e_name 21) (e_val 1w)) (o_store res_REG 15 22);
     i_assign 24 (e_val 1w) (o_load res_REG 15);
     i_assign 25 (e_val 1w) (o_store res_MEM 18 24);
     i_assign 26 (e_val 1w) (o_load res_PC 13);
     i_assign 27 (e_val 1w) (o_internal (e_add (e_name 26) (e_val 4w)));
     i_assign 28 (e_val 1w) (o_store res_PC 13 27)]`
      by (fs [example_spectre_OoO_list,example_spectre_OoO_exe_init] >> EVAL_TAC) >>
    Q.ABBREV_TAC `i = i_assign 13 (e_val 1w) (o_internal (e_val 0w))` >>
    Q.ABBREV_TAC `il = [i_assign 14 (e_val 1w) (o_internal (e_val 1w));
                        i_assign 15 (e_val 1w) (o_internal (e_val 2w));               
                        i_assign 16 (e_val 1w) (o_internal (e_val 3w));
                        i_assign 17 (e_val 1w) (o_internal (e_val b1));
                        i_assign 18 (e_val 1w) (o_internal (e_val b2));
                        i_assign 19 (e_val 1w) (o_load res_MEM 17);
                        i_assign 20 (e_val 1w) (o_store res_REG 14 19);
                        i_assign 21 (e_val 1w) (o_load res_REG 16);
                        i_assign 22 (e_eq (e_name 21) (e_val 1w)) (o_load res_REG 14);
                        i_assign 23 (e_eq (e_name 21) (e_val 1w)) (o_store res_REG 15 22);
                        i_assign 24 (e_val 1w) (o_load res_REG 15);
                        i_assign 25 (e_val 1w) (o_store res_MEM 18 24);
                        i_assign 26 (e_val 1w) (o_load res_PC 13);
                        i_assign 27 (e_val 1w) (o_internal (e_add (e_name 26) (e_val 4w)));
                        i_assign 28 (e_val 1w) (o_store res_PC 13 27)]` >>
    `~(Completed_list sem_expr (State_st_list (example_spectre_OoO_list a b c d 1w 2w 3w b1 b2)
    (example_spectre_OoO_store a b c d 2w 3w b1) [3] [12]) i)`
      by (fs [example_spectre_OoO_list,example_spectre_OoO_exe_init,example_spectre_OoO_store,Abbr `i`] >> EVAL_TAC) >>
    `IO_bounded_execution translate_val_list sem_expr
     (State_st_list (example_spectre_OoO_list a b c d 1w 2w 3w b1 b2)
     (example_spectre_OoO_store a b c d 2w 3w b1) [3] [12]) 13 (SUC 15) = SOME pi` by fs [] >>
    PROVE_TAC [IO_bounded_execution_in_order_step_sound]
QED

Theorem example_spectre_OoO_maximal_execution_correct[local]:
  sem_expr = sem_expr_exe ==>
  translate_val_list = (\v t. []) ==>
  !a b c d b1 b2 pi.
    example_spectre_OoO_maximal_execution a b c d b1 b2 = SOME pi ==>
    pi <> [] ==>
    maximal_execution_form in_order_step (state_list_to_state (example_spectre_OoO_state_st_list a b c d 1w 2w 3w b1 b2))
    (MAP step_list_to_step pi)                                  
Proof
  rw [maximal_execution_form] >>
  `State_st_list_well_formed_ok (example_spectre_OoO_state_st_list a b c d 1w 2w 3w b1 b2)`
    by fs [State_st_list_well_formed_ok_example_spectre_OoO_state_st_list] >-
   METIS_TAC [example_spectre_OoO_maximal_execution_sound] >-
             
   (`FST (HD pi) = example_spectre_OoO_state_st_list a b c d 1w 2w 3w b1 b2`
      by METIS_TAC [example_spectre_OoO_maximal_execution_sound] >>
    fs [HD_MAP_step_list_to_step_and_state_list_to_state]) >>

  `SND (SND (LAST (MAP step_list_to_step (THE (example_spectre_OoO_maximal_execution a b c d b1 b2))))) =
  state_list_to_state (SND (SND (LAST (THE (example_spectre_OoO_maximal_execution a b c d b1 b2)))))`
    by fs [LAST_MAP_step_list_to_step_and_state_list_to_state] >>
  `all_instructions_completed_list sem_expr_exe
   (SND (SND (LAST (THE (example_spectre_OoO_maximal_execution a b c d b1 b2)))))`
    by fs [example_spectre_OoO_maximal_execution_last_state_all_completed] >>
  `THE (example_spectre_OoO_maximal_execution a b c d b1 b2) = pi` by fs [] >> fs [] >>
  `all_instructions_completed_list sem_expr (SND (SND (LAST pi)))` by fs [] >>
  `?stl'.(SND (SND (LAST pi))) = stl'` by fs [] >>
  `well_formed_state (state_list_to_state stl')`
    by (fs [example_spectre_OoO_maximal_execution,example_spectre_OoO_state_st_list] >>
        `DROP (PRE 13) (example_spectre_OoO_list a b c d 1w 2w 3w b1 b2) =
        [i_assign 13 (e_val 1w) (o_internal (e_val 0w));
         i_assign 14 (e_val 1w) (o_internal (e_val 1w));             
         i_assign 15 (e_val 1w) (o_internal (e_val 2w));
         i_assign 16 (e_val 1w) (o_internal (e_val 3w));
         i_assign 17 (e_val 1w) (o_internal (e_val b1));
         i_assign 18 (e_val 1w) (o_internal (e_val b2));
         i_assign 19 (e_val 1w) (o_load res_MEM 17);
         i_assign 20 (e_val 1w) (o_store res_REG 14 19);
         i_assign 21 (e_val 1w) (o_load res_REG 16);
         i_assign 22 (e_eq (e_name 21) (e_val 1w)) (o_load res_REG 14);
         i_assign 23 (e_eq (e_name 21) (e_val 1w)) (o_store res_REG 15 22);
         i_assign 24 (e_val 1w) (o_load res_REG 15);
         i_assign 25 (e_val 1w) (o_store res_MEM 18 24);
         i_assign 26 (e_val 1w) (o_load res_PC 13);
         i_assign 27 (e_val 1w) (o_internal (e_add (e_name 26) (e_val 4w)));
         i_assign 28 (e_val 1w) (o_store res_PC 13 27)]`                                              
          by (fs [example_spectre_OoO_list] >> EVAL_TAC) >>
        Q.ABBREV_TAC `i = i_assign 13 (e_val 1w) (o_internal (e_val 0w))` >>
        Q.ABBREV_TAC `il = [i_assign 14 (e_val 1w) (o_internal (e_val 1w));
                            i_assign 15 (e_val 1w) (o_internal (e_val 2w));
                            i_assign 16 (e_val 1w) (o_internal (e_val 3w));
                            i_assign 17 (e_val 1w) (o_internal (e_val b1));     
                            i_assign 18 (e_val 1w) (o_internal (e_val b2));
                            i_assign 19 (e_val 1w) (o_load res_MEM 17);
                            i_assign 20 (e_val 1w) (o_store res_REG 14 19);
                            i_assign 21 (e_val 1w) (o_load res_REG 16);
                            i_assign 22 (e_eq (e_name 21) (e_val 1w)) (o_load res_REG 14);
                            i_assign 23 (e_eq (e_name 21) (e_val 1w)) (o_store res_REG 15 22);
                            i_assign 24 (e_val 1w) (o_load res_REG 15);      
                            i_assign 25 (e_val 1w) (o_store res_MEM 18 24);     
                            i_assign 26 (e_val 1w) (o_load res_PC 13);        
                            i_assign 27 (e_val 1w) (o_internal (e_add (e_name 26) (e_val 4w)));   
                            i_assign 28 (e_val 1w) (o_store res_PC 13 27)]` >>
        `~(Completed_list sem_expr (State_st_list (example_spectre_OoO_list a b c d 1w 2w 3w b1 b2)
        (example_spectre_OoO_store a b c d 2w 3w b1) [3] [12]) i)`                            
          by (fs [example_spectre_OoO_list,example_spectre_OoO_store,Abbr `i`] >> EVAL_TAC) >>
        `IO_bounded_execution translate_val_list sem_expr
         (State_st_list (example_spectre_OoO_list a b c d 1w 2w 3w b1 b2)
         (example_spectre_OoO_store a b c d 2w 3w b1) [3] [12]) 13 (SUC 15) = SOME pi` by fs [] >>
        PROVE_TAC [State_st_list_well_formed_ok_IO_bounded_execution_last_state]) >>
  `SND (SND (step_list_to_step (LAST pi))) = SND (SND (LAST (MAP step_list_to_step pi)))` by METIS_TAC [LAST_MAP] >>     
  fs [all_instructions_completed_list_implies_termination_IO]
QED

Theorem example_spectre_OoO_maximal_trace_result[local]:
  !a b c d b1 b2.
     example_spectre_OoO_maximal_trace a b c d b1 b2 =
     SOME [obs_dl b1; obs_ds b2; obs_il (d + 4w)]
Proof
  rw [] >> Cases_on `b = 1w` >-
   (rw [] >> EVAL_TAC >> Cases_on `b1 = b2` >> fs [] >> EVAL_TAC) >>
  rw [example_spectre_OoO_maximal_trace,IO_bounded_trace,IO_bounded_trace_aux] >>
  `IO_bounded_trace_acc (\v t. []) sem_expr_exe
  (example_spectre_OoO_state_st_list a b c d 1w 2w 3w b1 b2) 12 16 [] =
  SOME (example_spectre_OoO_state_st_list_final a b c d b1 b2,[obs_dl b1; obs_ds b2; obs_il (d + 4w)])`
    by fs [example_spectre_OoO_IO_bounded_trace_acc_not_true] >>
  fs [IO_bounded_trace_aux]
QED

Theorem example_spectre_OoO_maximal_execution_exists_result[local]:
  !a b c d b1 b2.
    ?pi. example_spectre_OoO_maximal_execution a b c d b1 b2 = SOME pi /\ pi <> []
Proof
  rw [] >>
  `example_spectre_OoO_maximal_trace a b c d b1 b2 = SOME [obs_dl b1; obs_ds b2; obs_il (d + 4w)]`
    by rw [example_spectre_OoO_maximal_trace_result] >>
  fs [example_spectre_OoO_maximal_trace,example_spectre_OoO_maximal_execution] >>
  `?pi. IO_bounded_execution (\v t. []) sem_expr_exe
    (example_spectre_OoO_state_st_list a b c d 1w 2w 3w b1 b2) 13 16 = SOME pi /\
  [obs_dl b1; obs_ds b2; obs_il (d + 4w)] = trace obs_of_ll obs_visible pi`
    by fs [IO_bounded_execution_for_trace] >>
  Q.EXISTS_TAC `pi` >> fs [trace] >>
  Cases_on  `pi` >> fs []           
QED                                                                     

Theorem example_spectre_OoO_same_obs[local]:
  !a a' b b' c c' d d' b1 b1' b2 b2'.
    example_spectre_OoO_maximal_trace a b c d b1 b2 =
    example_spectre_OoO_maximal_trace a' b' c' d' b1' b2' ==>
    d = d' /\ b1 = b1' /\ b2 = b2'
Proof
  rw [] >> fs [example_spectre_OoO_maximal_trace_result]
QED

Theorem noninterference_example_spectre_OoO_trace:
  sem_expr = sem_expr_exe ==>
  translate_val_list = (\v t. []) ==>
  !a a' b b' c c' d d' b1 b1' b2 b2' s1 s2.
    state_list_to_state (example_spectre_OoO_state_st_list a b c d 1w 2w 3w b1 b2) = s1 ==>
    state_list_to_state (example_spectre_OoO_state_st_list a' b' c' d' 1w 2w 3w b1' b2') = s2 ==>
    trace_indist_IO s1 s2 ==>
    d = d' /\ b1 = b1' /\ b2 = b2'
Proof
  REWRITE_TAC [trace_indist_IO,trace_indist] >>
  NTAC 2 STRIP_TAC >>
  REPEAT GEN_TAC >> NTAC 3 STRIP_TAC >> fs [] >>
  `?p1 p2. example_spectre_OoO_maximal_execution a b c d b1 b2 = SOME p1 /\
  example_spectre_OoO_maximal_execution a' b' c' d' b1' b2' = SOME p2 /\
  p1 <> [] /\ p2 <> []` by METIS_TAC [example_spectre_OoO_maximal_execution_exists_result] >>
  `maximal_execution_form in_order_step (state_list_to_state
  (example_spectre_OoO_state_st_list a b c d 1w 2w 3w b1 b2)) (MAP step_list_to_step p1) /\
  maximal_execution_form in_order_step (state_list_to_state
  (example_spectre_OoO_state_st_list a' b' c' d' 1w 2w 3w b1' b2')) (MAP step_list_to_step p2)`
    by fs [example_spectre_OoO_maximal_execution_correct] >>
  Q.ABBREV_TAC `stl1 = example_spectre_OoO_state_st_list a b c d 1w 2w 3w b1 b2` >>
  Q.ABBREV_TAC `stl2 = example_spectre_OoO_state_st_list a' b' c' d' 1w 2w 3w b1' b2'` >>           
  `State_st_list_well_formed_ok stl1 /\ State_st_list_well_formed_ok stl2`
    by fs [Abbr `stl1`,Abbr `stl2`,State_st_list_well_formed_ok_example_spectre_OoO_state_st_list] >>
  `well_formed_state (state_list_to_state stl1) /\ well_formed_state (state_list_to_state stl2)`
    by (Cases_on `stl1` >> Cases_on `stl2` >> fs [State_st_list_well_formed_ok]) >>
  `well_formed_state s1 /\ well_formed_state s2` by METIS_TAC [] >>
  Q.ABBREV_TAC `max_org_pi1 = MAP step_list_to_step p1` >>
  Q.ABBREV_TAC `max_org_pi2 = MAP step_list_to_step p2` >>
  `maximal_execution_form in_order_step s1 max_org_pi1 /\
  maximal_execution_form in_order_step s2 max_org_pi2` by METIS_TAC [] >>
  `maximal_execution_form in_order_step' s1 (MAP update_lbl max_org_pi1) /\
  maximal_execution_form in_order_step' s2 (MAP update_lbl max_org_pi2)`
    by fs [max_execution_format_step_and_step'] >>
  Q.ABBREV_TAC `max_pi1 = MAP update_lbl max_org_pi1` >>
  Q.ABBREV_TAC `max_pi2 = MAP update_lbl max_org_pi2` >>
  `trace obs_of_l obs_visible max_pi1 = trace obs_of_l obs_visible max_pi2`
    by REWRITE_TAC [UNDISCH_ALL (SPEC_ALL noninterference_implies_maximal_execution_form_in_order_step')] >>
  `trace obs_of_l obs_visible max_org_pi1 = trace obs_of_l obs_visible max_org_pi2` by METIS_TAC [MAP_update_lbl_same_obs,Abbr `max_pi1`,Abbr `max_pi2`] >>
  `example_spectre_OoO_maximal_trace a b c d b1 b2 <> NONE /\
  example_spectre_OoO_maximal_trace a' b' c' d' b1' b2' <> NONE`
    by fs [example_spectre_OoO_maximal_trace_result] >>
  `?tr1 tr2. example_spectre_OoO_maximal_trace a b c d b1 b2 = SOME tr1 /\
  example_spectre_OoO_maximal_trace a' b' c' d' b1' b2' = SOME tr2`
    by (Cases_on `example_spectre_OoO_maximal_trace a b c d b1 b2` >>
        Cases_on `example_spectre_OoO_maximal_trace a' b' c' d' b1' b2'` >> fs []) >>
  `(trace obs_of_l obs_visible max_org_pi1 = tr1) /\ (trace obs_of_l obs_visible max_org_pi2 = tr2)`
    by METIS_TAC [example_spectre_OoO_maximal_execution,example_spectre_OoO_maximal_trace,
                  IO_bounded_execution_and_trace,Abbr `max_org_pi1`,Abbr `max_org_pi2`] >>
  `example_spectre_OoO_maximal_trace a b c d b1 b2 = example_spectre_OoO_maximal_trace a' b' c' d' b1' b2'` by fs [] >>
  METIS_TAC [example_spectre_OoO_same_obs]
QED

(* Unused definitions and theorems of example SpectreOoO

Definition example_spectre_OoO_state_st_list_mid:
  example_spectre_OoO_state_st_list_mid a b c d b1 b2 =
  State_st_list
          [i_assign 1 (e_val 1w) (o_internal (e_val b1));
           i_assign 2 (e_val 1w) (o_internal (e_val a));
           i_assign 3 (e_val 1w) (o_store res_MEM 1 2);
           i_assign 4 (e_val 1w) (o_internal (e_val 3w));
           i_assign 5 (e_val 1w) (o_internal (e_val b));
           i_assign 6 (e_val 1w) (o_store res_REG 4 5);
           i_assign 7 (e_val 1w) (o_internal (e_val 2w));
           i_assign 8 (e_val 1w) (o_internal (e_val c));
           i_assign 9 (e_val 1w) (o_store res_REG 7 8);
           i_assign 10 (e_val 1w) (o_internal (e_val 0w));
           i_assign 11 (e_val 1w) (o_internal (e_val d));
           i_assign 12 (e_val 1w) (o_store res_PC 10 11);
           i_assign 13 (e_val 1w) (o_internal (e_val 0w));
           i_assign 14 (e_val 1w) (o_internal (e_val 1w));
           i_assign 15 (e_val 1w) (o_internal (e_val 2w));
           i_assign 16 (e_val 1w) (o_internal (e_val 3w));
           i_assign 17 (e_val 1w) (o_internal (e_val b1));
           i_assign 18 (e_val 1w) (o_internal (e_val b2));
           i_assign 19 (e_val 1w) (o_load res_MEM 17);
           i_assign 20 (e_val 1w) (o_store res_REG 14 19);
           i_assign 21 (e_val 1w) (o_load res_REG 16);
           i_assign 22 (e_eq (e_name 21) (e_val 1w)) (o_load res_REG 14);
           i_assign 23 (e_eq (e_name 21) (e_val 1w)) (o_store res_REG 15 22);
           i_assign 24 (e_val 1w) (o_load res_REG 15);
           i_assign 25 (e_val 1w) (o_store res_MEM 18 24);
           i_assign 26 (e_val 1w) (o_load res_PC 13);
           i_assign 27 (e_val 1w) (o_internal (e_add (e_name 26) (e_val 4w)));
           i_assign 28 (e_val 1w) (o_store res_PC 13 27)]
          (FEMPTY |+ (1,b1) |+ (2,a) |+ (3,a) |+ (4,3w) |+ (5,b) |+ (6,b) |+          
           (7,2w) |+ (8,c) |+ (9,c) |+ (10,0w) |+ (11,d) |+ (12,d) |+ (13,0w) |+
           (14,1w) |+ (15,2w) |+ (16,3w) |+ (17,b1) |+ (18,b2) |+ (19,a) |+ (20,a) |+ (21,b)) [3] [12]
End
        
Theorem IO_bounded_execution_acc_complete_steps[local]:
  translate_val_list_SORTED ==>
  !l s cs fs l' s' cs' fs' pi n pos.
    State_st_list_well_formed_initialized_ok (State_st_list l s cs fs) ==>
    SORTED bound_name_instr_le l ==>
    Completed_list_up_to sem_expr (State_st_list l s cs fs) pos ==>
    (!t. MEM t (bound_names_program_list l) /\ t > pos ==> t NOTIN FDOM s) ==>
    FST (HD pi) = State_st_list l s cs fs ==>
    step_execution in_order_step (MAP step_list_to_step pi) ==>
    SND (SND (LAST pi)) = State_st_list l' s' cs' fs' ==>
    Completed_list_up_to sem_expr (State_st_list l' s' cs' fs') (pos + n) ==>
    (!t. MEM t (bound_names_program_list l') /\ t > (pos+n) ==> t NOTIN FDOM s') ==>
    IO_bounded_execution_acc translate_val_list sem_expr (State_st_list l s cs fs) pos n [] = SOME pi
Proof
  cheat
QED

Theorem APPEND_HD_FST[local]:
  !l1 l2 l.
    l = l1 ++ l2 ==> l1 <> [] ==> HD l = HD l1
Proof
  rw [] >> Cases_on `l1` >> fs []
QED

Theorem IO_bounded_execution_acc_subresults[local]:
  translate_val_list_SORTED ==>
  !l l' l'' s s' s'' cs cs' cs'' fs fs' fs'' stl'' pos m n pi pi' i il.
    State_st_list_well_formed_initialized_ok (State_st_list l s cs fs) ==>
    State_st_list_well_formed_ok (State_st_list l' s' cs' fs') ==>
    (!t. MEM t (bound_names_program_list l) /\ t > pos ==> t NOTIN FDOM s) ==>
    (!t. MEM t (bound_names_program_list l'') /\ t > (pos+m+n) ==> t NOTIN FDOM s'') ==>
    SORTED bound_name_instr_le l ==>
    SORTED bound_name_instr_le l' ==>
    Completed_list_up_to sem_expr (State_st_list l s cs fs) pos ==>
    DROP pos l = i::il ==>
    ~Completed_list sem_expr (State_st_list l s cs fs) i ==>
    pi <> [] ==>    
    IO_bounded_execution_acc translate_val_list sem_expr (State_st_list l s cs fs) pos m [] = SOME pi ==>
    SND (SND (LAST pi)) = State_st_list l' s' cs' fs' ==>
    SND (SND (LAST pi')) = State_st_list l'' s'' cs'' fs'' ==>
    IO_bounded_execution_acc translate_val_list sem_expr (State_st_list l' s' cs' fs') (pos+m) n pi = SOME pi' ==>
    IO_bounded_execution_acc translate_val_list sem_expr (State_st_list l s cs fs) pos (m+n) [] = SOME pi'
Proof
  rw [] >>
  Cases_on `m` >-
   fs [Once IO_bounded_execution_acc] >>
  `State_st_list_well_formed_ok (State_st_list l s cs fs)` by fs [State_st_list_well_formed_ok,State_st_list_well_formed_initialized_ok] >>
  `step_execution_list_IO_HD (State_st_list l s cs fs) pi pos (SUC n')` by fs [IO_bounded_execution_acc_IO_empty_sound] >>
  fs [step_execution_list_IO_HD] >>
  `Completed_list_up_to sem_expr (State_st_list l' s' cs' fs') (pos + SUC n')` by METIS_TAC [] >>
  `?pi''. pi' = pi ++ pi'' /\ step_execution in_order_step (MAP step_list_to_step pi') /\
  Completed_list_up_to sem_expr (SND (SND (LAST pi'))) (pos + SUC n' + n) /\
  LENGTH pi'' <= 2 * n` by fs [IO_bounded_execution_acc_IO_execution_sound] >>  
  `HD pi' = HD pi` by fs [APPEND_HD_FST] >>
  `FST (HD pi') = State_st_list l s cs fs` by fs [] >>
  `pos + SUC n' + n = pos + (n + SUC n') /\ n + (pos + SUC n') = pos + (n + SUC n')` by rw [] >>
  `Completed_list_up_to sem_expr (SND (SND (LAST pi'))) (pos + (n + SUC n'))` by METIS_TAC [] >>
  `(!t. MEM t (bound_names_program_list l'') /\ t > (pos+(n + SUC n')) ==> t NOTIN FDOM s'')` by METIS_TAC [] >>
  METIS_TAC [IO_bounded_execution_acc_complete_steps]
QED

Theorem IO_bounded_trace_acc_subresults[local]:
  !f_tran f_sem l s s' cs cs' fs fs' stl'' pos m n tr tr'.
    IO_bounded_trace_acc f_tran f_sem (State_st_list l s cs fs) pos m [] = SOME (State_st_list l s' cs' fs',tr) ==>
    IO_bounded_trace_acc f_tran f_sem (State_st_list l s' cs' fs') (pos+m) n tr = SOME (stl'',tr') ==>
    IO_bounded_trace_acc f_tran f_sem (State_st_list l s cs fs) pos (m+n) [] = SOME (stl'',tr')
Proof
  cheat
QED

Theorem example_spectre_OoO_IO_bounded_trace_acc_not_true_part1[local]:
  !a b c d b1 b2.
    b <> 1w ==>
    IO_bounded_trace_acc (\v t. []) sem_expr_exe
    (example_spectre_OoO_state_st_list a b c d 1w 2w 3w b1 b2) 11 10 [] =
    SOME (example_spectre_OoO_state_st_list_mid a b c d b1 b2, [obs_il d; obs_dl b1])
Proof
  rw [example_spectre_OoO_state_st_list_mid] >> EVAL_TAC
QED

Theorem example_spectre_OoO_IO_bounded_trace_acc_not_true_part2[local]:
  !a b c d b1 b2.
    b <> 1w ==>
    IO_bounded_trace_acc (\v t. []) sem_expr_exe
    (example_spectre_OoO_state_st_list_mid a b c d b1 b2) 21 7 [obs_il d; obs_dl b1] =
    SOME (example_spectre_OoO_state_st_list_final a b c d b1 b2,
          [obs_il d; obs_dl b1; obs_ds b2; obs_il (d + 4w)])
Proof
  rw [example_spectre_OoO_state_st_list_mid,example_spectre_OoO_state_st_list_final] >>
  NTAC 3 (rw [Once IO_bounded_trace_acc] >> fs [FLOOKUP_DEF,sem_expr_exe,v_eq,val_false]) >>
  rw [Once sem_instr_exe] >>
  fs [str_act_list,addr_of_list,FIND_instr,bound_name_instr,str_may_list] >>
  Q.ABBREV_TAC `l1 = [i_assign 1 (e_val 1w) (o_internal (e_val b1));
                      i_assign 2 (e_val 1w) (o_internal (e_val a));
                      i_assign 3 (e_val 1w) (o_store res_MEM 1 2);
                      i_assign 4 (e_val 1w) (o_internal (e_val 3w));
                      i_assign 5 (e_val 1w) (o_internal (e_val b));
                      i_assign 6 (e_val 1w) (o_store res_REG 4 5);
                      i_assign 7 (e_val 1w) (o_internal (e_val 2w));
                      i_assign 8 (e_val 1w) (o_internal (e_val c));
                      i_assign 9 (e_val 1w) (o_store res_REG 7 8);
                      i_assign 10 (e_val 1w) (o_internal (e_val 0w));
                      i_assign 11 (e_val 1w) (o_internal (e_val d));
                      i_assign 12 (e_val 1w) (o_store res_PC 10 11);
                      i_assign 13 (e_val 1w) (o_internal (e_val 0w));
                      i_assign 14 (e_val 1w) (o_internal (e_val 1w));
                      i_assign 15 (e_val 1w) (o_internal (e_val 2w));
                      i_assign 16 (e_val 1w) (o_internal (e_val 3w));
                      i_assign 17 (e_val 1w) (o_internal (e_val b1));
                      i_assign 18 (e_val 1w) (o_internal (e_val b2));
                      i_assign 19 (e_val 1w) (o_load res_MEM 17);
                      i_assign 20 (e_val 1w) (o_store res_REG 14 19);
                      i_assign 21 (e_val 1w) (o_load res_REG 16);
                      i_assign 22 (e_eq (e_name 21) (e_val 1w)) (o_load res_REG 14);
                      i_assign 23 (e_eq (e_name 21) (e_val 1w)) (o_store res_REG 15 22);
                      i_assign 24 (e_val 1w) (o_load res_REG 15);
                      i_assign 25 (e_val 1w) (o_store res_MEM 18 24);
                      i_assign 26 (e_val 1w) (o_load res_PC 13);
                      i_assign 27 (e_val 1w) (o_internal (e_add (e_name 26) (e_val 4w)));
                      i_assign 28 (e_val 1w) (o_store res_PC 13 27)]` >>
   Q.ABBREV_TAC `(s1:num |-> v) = (FEMPTY |+ (1,b1) |+ (2,a) |+ (3,a) |+ (4,3w) |+
                      (5,b) |+ (6,b) |+ (7,2w) |+ (8,c) |+ (9,c) |+
                      (10,0w) |+ (11,d) |+ (12,d) |+ (13,0w) |+ (14,1w) |+
                      (15,2w) |+ (16,3w) |+ (17,b1) |+ (18,b2) |+ (19,a) |+
                      (20,a) |+ (21,b))` >>
  `str_may_list_find sem_expr_exe l1 s1 24 res_REG 15 = [i_assign 9 (e_val 1w) (o_store res_REG 7 8)]`
    by (fs [Abbr `l1`,Abbr `s1`] >> EVAL_TAC >> fs []) >>
  fs [str_act_list_find,str_act_list_cond,sem_expr_exe,Abbr `s1`] >>
  NTAC 3 (rw [Once FLOOKUP_DEF]) >>
  fs [bound_names_program_list] >>
  rw [Once FLOOKUP_DEF] >>
  fs [bound_name_instr,FLOOKUP_DEF,OoO_Exe_list_instr_not_stored_guard_true_sem_instr,
      obs_visible,obs_of_ll] >>
  fs [Abbr `l1`] >> EVAL_TAC >>
  Cases_on `b1 = b2` >> fs [] >> EVAL_TAC
QED

Theorem example_spectre_OoO_IO_bounded_trace_acc_not_true[local]:
  !a b c d b1 b2.
    b <> 1w ==>
    IO_bounded_trace_acc (\v t. []) sem_expr_exe
    (example_spectre_OoO_state_st_list a b c d 1w 2w 3w b1 b2) 11 17 [] =
    SOME (example_spectre_OoO_state_st_list_final a b c d b1 b2,
           [obs_il d; obs_dl b1; obs_ds b2; obs_il (d + 4w)])
Proof      
  rw [] >>
  `IO_bounded_trace_acc (\v t. []) sem_expr_exe
   (example_spectre_OoO_state_st_list a b c d 1w 2w 3w b1 b2) 11 10 [] =
  SOME (example_spectre_OoO_state_st_list_mid a b c d b1 b2, [obs_il d; obs_dl b1])`
    by fs [example_spectre_OoO_IO_bounded_trace_acc_not_true_part1] >>
  `IO_bounded_trace_acc (\v t. []) sem_expr_exe
   (example_spectre_OoO_state_st_list_mid a b c d b1 b2) (11+10) 7 [obs_il d; obs_dl b1] =
   SOME (example_spectre_OoO_state_st_list_final a b c d b1 b2,
         [obs_il d; obs_dl b1; obs_ds b2; obs_il (d + 4w)])`
    by fs [example_spectre_OoO_IO_bounded_trace_acc_not_true_part2] >>
  fs [example_spectre_OoO_state_st_list,example_spectre_OoO_state_st_list_mid] >>
  `example_spectre_OoO_list a b c d 1w 2w 3w b1 b2 =
  [i_assign 1 (e_val 1w) (o_internal (e_val b1));
   i_assign 2 (e_val 1w) (o_internal (e_val a));  
   i_assign 3 (e_val 1w) (o_store res_MEM 1 2);  
   i_assign 4 (e_val 1w) (o_internal (e_val 3w));  
   i_assign 5 (e_val 1w) (o_internal (e_val b));  
   i_assign 6 (e_val 1w) (o_store res_REG 4 5);  
   i_assign 7 (e_val 1w) (o_internal (e_val 2w)); 
   i_assign 8 (e_val 1w) (o_internal (e_val c));  
   i_assign 9 (e_val 1w) (o_store res_REG 7 8);
   i_assign 10 (e_val 1w) (o_internal (e_val 0w)); 
   i_assign 11 (e_val 1w) (o_internal (e_val d));  
   i_assign 12 (e_val 1w) (o_store res_PC 10 11);     
   i_assign 13 (e_val 1w) (o_internal (e_val 0w));     
   i_assign 14 (e_val 1w) (o_internal (e_val 1w));     
   i_assign 15 (e_val 1w) (o_internal (e_val 2w));       
   i_assign 16 (e_val 1w) (o_internal (e_val 3w));         
   i_assign 17 (e_val 1w) (o_internal (e_val b1));  
   i_assign 18 (e_val 1w) (o_internal (e_val b2));      
   i_assign 19 (e_val 1w) (o_load res_MEM 17);    
   i_assign 20 (e_val 1w) (o_store res_REG 14 19);      
   i_assign 21 (e_val 1w) (o_load res_REG 16);      
   i_assign 22 (e_eq (e_name 21) (e_val 1w)) (o_load res_REG 14);  
   i_assign 23 (e_eq (e_name 21) (e_val 1w)) (o_store res_REG 15 22);        
   i_assign 24 (e_val 1w) (o_load res_REG 15);       
   i_assign 25 (e_val 1w) (o_store res_MEM 18 24);         
   i_assign 26 (e_val 1w) (o_load res_PC 13);       
   i_assign 27 (e_val 1w) (o_internal (e_add (e_name 26) (e_val 4w)));
   i_assign 28 (e_val 1w) (o_store res_PC 13 27)]` by fs [example_spectre_OoO_list] >>
  `IO_bounded_trace_acc (\v t. []) sem_expr_exe
   (State_st_list (example_spectre_OoO_list a b c d 1w 2w 3w b1 b2)
   (example_spectre_OoO_store a b c d 2w 3w b1) [3] []) 11 (10+7) [] =
   SOME (example_spectre_OoO_state_st_list_final a b c d b1 b2,
   [obs_il d; obs_dl b1; obs_ds b2; obs_il (d + 4w)])` by fs [IO_bounded_trace_acc_subresults] >>
  FULL_SIMP_TAC arith_ss []
QED  
*)
                  
val _ = export_theory ();
