open HolKernel boolLib Parse bossLib wordsLib optionTheory wordsTheory finite_mapTheory pred_setTheory listTheory rich_listTheory ottTheory milTheory milUtilityTheory milMetaTheory milInitializationTheory milExecutableUtilityTheory milExecutableTransitionTheory milExecutableInitializationTheory milExecutableExamplesTheory milExecutableIOTheory milExecutableIOTraceTheory bir_programTheory bir_to_milLib;

val _ = new_theory "bir_to_mil_test_store";

val bir_prog = ``
 BirProgram
   [<|bb_label := BL_Address (Imm64 0x000w);
      bb_statements :=
             [BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
                           (BExp_Store (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                                       (BExp_Const (Imm64 25w))
                                       BEnd_LittleEndian
                                       (BExp_Const (Imm64 26w)));
	      BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
                           (BExp_Store (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                                       (BExp_Const (Imm64 25w))
                                       BEnd_LittleEndian
                                       (BExp_Const (Imm64 25w)))];
           bb_last_statement :=
             BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x004w)))|>;
   <|bb_label := BL_Address (Imm64 0x004w);
     bb_statements := [];
     bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x000w)))|>]
: bir_val_t bir_program_t
``;

val translate_val_bir_prog_set =
 bir_prog_to_mil_iset bir_prog "translate_val_bir_prog_set";

val translate_val_bir_prog_list =
 bir_prog_to_mil_ilist bir_prog "translate_val_bir_prog_list";

(* Here we choose 0w for "MEM", although the value doesn't affect the program *)
Theorem translate_val_bir_prog_list_eq_set[local]:  
 LIST_TO_SET (translate_val_bir_prog_list 0w 0) =
 translate_val_bir_prog_set 0w 0
Proof
 EVAL_TAC >> rw [SUBSET_DEF]
QED

Theorem translate_val_bir_prog_list_block_1[local]:
  translate_val_bir_prog_list 0w 0 =
  [i_assign 1 (e_val 1w) (o_internal (e_val 25w));
      i_assign 2 (e_val 1w) (o_internal (e_val 26w));
      i_assign 3 (e_val 1w) (o_store res_MEM 1 2);
      i_assign 4 (e_val 1w) (o_internal (e_name 3));
      i_assign 5 (e_val 1w) (o_internal (e_val 25w));
      i_assign 6 (e_val 1w) (o_internal (e_val 25w));
      i_assign 7 (e_val 1w) (o_store res_MEM 5 6);
      i_assign 8 (e_val 1w) (o_internal (e_name 7));
      i_assign 9 (e_val 1w) (o_internal (e_val 0w));
      i_assign 10 (e_val 1w) (o_load res_PC 9);
      i_assign 11 (e_val 1w) (o_internal (e_add (e_name 10) (e_val 4w)));
      i_assign 12 (e_val 1w) (o_store res_PC 9 11)]
Proof
  EVAL_TAC
QED

Theorem translate_val_bir_prog_list_block_2[local]:
  translate_val_bir_prog_list 4w 0 =
  [i_assign 1 (e_val 1w) (o_internal (e_val 0w));
   i_assign 2 (e_val 1w) (o_load res_PC 1);
   i_assign 3 (e_val 1w) (o_internal (e_sub (e_name 2) (e_val 4w)));
   i_assign 4 (e_val 1w) (o_store res_PC 1 3)]
Proof
  EVAL_TAC
QED

Theorem exe_bir_prog_list_OoO_step_list[local]:
  (let tr = translate_val_bir_prog_list in
   let (st,tmax) = initialize_state_without_pc_fetch_list [] [] 0w in
   OoO_step_list tr sem_expr_exe st tmax) =
   SOME
       (ll_lb (obs_il 0w)
          (act_ftc_list
             [i_assign 4 (e_val 1w) (o_internal (e_val 25w));
              i_assign 5 (e_val 1w) (o_internal (e_val 26w));
              i_assign 6 (e_val 1w) (o_store res_MEM 4 5);
              i_assign 7 (e_val 1w) (o_internal (e_name 6));
              i_assign 8 (e_val 1w) (o_internal (e_val 25w));
              i_assign 9 (e_val 1w) (o_internal (e_val 25w));
              i_assign 10 (e_val 1w) (o_store res_MEM 8 9);
              i_assign 11 (e_val 1w) (o_internal (e_name 10));
              i_assign 12 (e_val 1w) (o_internal (e_val 0w));
              i_assign 13 (e_val 1w) (o_load res_PC 12);
              i_assign 14 (e_val 1w)
                (o_internal (e_add (e_name 13) (e_val 4w)));
              i_assign 15 (e_val 1w) (o_store res_PC 12 14)]) 3,
        State_st_list
          [i_assign 1 (e_val 1w) (o_internal (e_val 0w));
           i_assign 2 (e_val 1w) (o_internal (e_val 0w));
           i_assign 3 (e_val 1w) (o_store res_PC 1 2);
           i_assign 4 (e_val 1w) (o_internal (e_val 25w));
           i_assign 5 (e_val 1w) (o_internal (e_val 26w));
           i_assign 6 (e_val 1w) (o_store res_MEM 4 5);
           i_assign 7 (e_val 1w) (o_internal (e_name 6));
           i_assign 8 (e_val 1w) (o_internal (e_val 25w));
           i_assign 9 (e_val 1w) (o_internal (e_val 25w));
           i_assign 10 (e_val 1w) (o_store res_MEM 8 9);
           i_assign 11 (e_val 1w) (o_internal (e_name 10));
           i_assign 12 (e_val 1w) (o_internal (e_val 0w));
           i_assign 13 (e_val 1w) (o_load res_PC 12);
           i_assign 14 (e_val 1w) (o_internal (e_add (e_name 13) (e_val 4w)));
           i_assign 15 (e_val 1w) (o_store res_PC 12 14)]
          (FEMPTY |+ (1,0w) |+ (2,0w) |+ (3,0w)) [] [3])
Proof
  EVAL_TAC
QED

Theorem exe_bir_prog_list_IO_bounded_execution[local]:
  (let tr = translate_val_bir_prog_list in
   let (st,tmax) = initialize_state_without_pc_fetch_list [] [] 0w in
   IO_bounded_execution tr sem_expr_exe st tmax 1) =
   SOME
       [(State_st_list
           [i_assign 1 (e_val 1w) (o_internal (e_val 0w));
            i_assign 2 (e_val 1w) (o_internal (e_val 0w));
            i_assign 3 (e_val 1w) (o_store res_PC 1 2)]
           (FEMPTY |+ (1,0w) |+ (2,0w) |+ (3,0w)) [] [],
         ll_lb (obs_il 0w)
           (act_ftc_list
              [i_assign 4 (e_val 1w) (o_internal (e_val 25w));
               i_assign 5 (e_val 1w) (o_internal (e_val 26w));
               i_assign 6 (e_val 1w) (o_store res_MEM 4 5);
               i_assign 7 (e_val 1w) (o_internal (e_name 6));
               i_assign 8 (e_val 1w) (o_internal (e_val 25w));
               i_assign 9 (e_val 1w) (o_internal (e_val 25w));
               i_assign 10 (e_val 1w) (o_store res_MEM 8 9);
               i_assign 11 (e_val 1w) (o_internal (e_name 10));
               i_assign 12 (e_val 1w) (o_internal (e_val 0w));
               i_assign 13 (e_val 1w) (o_load res_PC 12);
               i_assign 14 (e_val 1w)
                 (o_internal (e_add (e_name 13) (e_val 4w)));
               i_assign 15 (e_val 1w) (o_store res_PC 12 14)]) 3,
         State_st_list
           [i_assign 1 (e_val 1w) (o_internal (e_val 0w));
            i_assign 2 (e_val 1w) (o_internal (e_val 0w));
            i_assign 3 (e_val 1w) (o_store res_PC 1 2);
            i_assign 4 (e_val 1w) (o_internal (e_val 25w));
            i_assign 5 (e_val 1w) (o_internal (e_val 26w));
            i_assign 6 (e_val 1w) (o_store res_MEM 4 5);
            i_assign 7 (e_val 1w) (o_internal (e_name 6));
            i_assign 8 (e_val 1w) (o_internal (e_val 25w));
            i_assign 9 (e_val 1w) (o_internal (e_val 25w));
            i_assign 10 (e_val 1w) (o_store res_MEM 8 9);
            i_assign 11 (e_val 1w) (o_internal (e_name 10));
            i_assign 12 (e_val 1w) (o_internal (e_val 0w));
            i_assign 13 (e_val 1w) (o_load res_PC 12);
            i_assign 14 (e_val 1w)
              (o_internal (e_add (e_name 13) (e_val 4w)));
            i_assign 15 (e_val 1w) (o_store res_PC 12 14)]
           (FEMPTY |+ (1,0w) |+ (2,0w) |+ (3,0w)) [] [3])]
Proof
  EVAL_TAC
QED

Theorem exe_bir_prog_list_IO_bounded_trace_1[local]:
  (let tr = translate_val_bir_prog_list in
   let (st,tmax) = initialize_state_without_pc_fetch_list [] [] 0w in
   IO_bounded_trace tr sem_expr_exe st tmax 1) =
  SOME [obs_il 0w]
Proof
  EVAL_TAC
QED

Theorem exe_bir_prog_list_IO_bounded_trace_2[local]:
  (let tr = translate_val_bir_prog_list in
   let (st,tmax) = initialize_state_without_pc_fetch_list [] [] 0w in
   IO_bounded_trace tr sem_expr_exe st tmax 4) =
  SOME [obs_il 0w; obs_ds 25w]
Proof
  EVAL_TAC
QED

Theorem exe_bir_prog_list_IO_bounded_trace_3[local]:
  (let tr = translate_val_bir_prog_list in
   let (st,tmax) = initialize_state_without_pc_fetch_list [] [] 0w in
   IO_bounded_trace tr sem_expr_exe st tmax 8) =
  SOME [obs_il 0w; obs_ds 25w; obs_ds 25w]
Proof
  EVAL_TAC
QED

Theorem exe_bir_prog_list_IO_bounded_trace_4[local]:
  (let tr = translate_val_bir_prog_list in
   let (st,tmax) = initialize_state_without_pc_fetch_list [] [] 0w in
   IO_bounded_trace tr sem_expr_exe st tmax 13) =
  SOME [obs_il 0w; obs_ds 25w; obs_ds 25w; obs_il 4w]
Proof
  EVAL_TAC
QED

Theorem exe_bir_prog_list_IO_bounded_trace_5[local]:
  (let tr = translate_val_bir_prog_list in
   let (st,tmax) = initialize_state_without_pc_fetch_list [] [] 0w in
   IO_bounded_trace tr sem_expr_exe st tmax 17) =
  SOME [obs_il 0w; obs_ds 25w; obs_ds 25w; obs_il 4w; obs_il 0w]
Proof
  EVAL_TAC
QED
          
val _ = export_theory ();
