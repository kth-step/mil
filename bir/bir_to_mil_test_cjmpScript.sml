open HolKernel boolLib Parse bossLib wordsLib optionTheory wordsTheory bitstringTheory finite_mapTheory pred_setTheory listTheory rich_listTheory llistTheory ottTheory milTheory milUtilityTheory milMetaTheory milInitializationTheory milExecutableUtilityTheory milExecutableTransitionTheory milExecutableInitializationTheory milExecutableExamplesTheory milExecutableIOTheory milExecutableIOTraceTheory bir_auxiliaryTheory bir_immTheory bir_valuesTheory bir_exp_immTheory bir_exp_memTheory bir_envTheory bir_programTheory bir_expTheory bir_evalLib milExecutableIOTheory milExecutableIOTraceTheory bir_to_milLib;

val _ = new_theory "bir_to_mil_test_cjmp";

val bir_prog = ``
 BirProgram
   [<|bb_label := BL_Address (Imm64 0x000w);
      bb_statements := [];
      bb_last_statement := BStmt_CJmp 
       (BExp_BinPred BIExp_Equal (BExp_Const (Imm64 0w)) (BExp_Const (Imm64 0w)))
       (BLE_Label (BL_Address (Imm64 0x004w))) (BLE_Label (BL_Address (Imm64 0x000w)))|>;
   <|bb_label := BL_Address (Imm64 0x004w);
       bb_statements := [];
       bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x000w)))|>]
``;

(* BIR initial state and execution *)

val bir_st = ``
 <| bst_pc := <| bpc_label := BL_Address (Imm64 0x000w); bpc_index := 0 |>;
    bst_environ := bir_env_default (bir_envty_of_vs {}); 
    bst_status := BST_Running |>
``;

EVAL ``bir_exec_step ^bir_prog ^bir_st``;

EVAL ``bir_exec_step ^bir_prog (bir_state_init ^bir_prog)``;

val (bir_exec_obs,bir_exec_st) = bir_eval_exec_n bir_prog bir_st 5;

(* MIL program, initial state, and execution *)

val translate_val_bir_prog_list =
 bir_prog_to_mil_ilist bir_prog "translate_val_bir_prog_list";

EVAL ``
  let tr = translate_val_bir_prog_list in
  let (st,tmax) = initialize_state_without_pc_fetch_list [] [] 0w in
  IO_bounded_trace_aux tr sem_expr_exe st tmax 5
``;

Theorem mil_exec_obs_st[local]:
 (let tr = translate_val_bir_prog_list in
  let (st,tmax) = initialize_state_without_pc_fetch_list [] [] 0w in
  IO_bounded_trace_aux tr sem_expr_exe st tmax 5) =
 SOME
 (State_st_list
  [i_assign 1 (e_val 1w) (o_internal (e_val 0w));
   i_assign 2 (e_val 1w) (o_internal (e_val 0w));
   i_assign 3 (e_val 1w) (o_store res_PC 1 2);
   i_assign 4 (e_val 1w) (o_internal (e_val 0w));
   i_assign 5 (e_val 1w) (o_load res_PC 4);
   i_assign 6 (e_val 1w) (o_internal (e_eq (e_val 0w) (e_val 0w)));
   i_assign 7 (e_val 1w) (o_internal (e_add (e_name 5) (e_val 4w)));
   i_assign 8 (e_name 6) (o_store res_PC 4 7);
   i_assign 9 (e_val 1w) (o_internal (e_sub (e_name 5) (e_val 0w)));
   i_assign 10 (e_val 1w) (o_store res_PC 4 9)]
   (FEMPTY |+ (1,0w) |+ (2,0w) |+ (3,0w) |+ (4,0w) |+ (5,0w) |+
    (6,1w) |+ (7,4w)) [] [3],
  [obs_il 0w])
Proof
 EVAL_TAC
QED

val _ = export_theory ();
