open HolKernel boolLib Parse bossLib wordsLib optionTheory wordsTheory finite_mapTheory pred_setTheory listTheory rich_listTheory ottTheory milTheory milUtilityTheory milMetaTheory milInitializationTheory milExecutableUtilityTheory milExecutableTransitionTheory milExecutableInitializationTheory milExecutableExamplesTheory milExecutableIOTheory milExecutableIOTraceTheory bir_to_milLib;

val _ = new_theory "bir_to_mil_test_basic";

val bir_prog_reg = ``
 BirProgram [
  <|bb_label := BL_Address (Imm64 0x000w);
    bb_statements :=
    [BStmt_Assign (BVar "r1" (BType_Imm Bit64))
     (BExp_BinExp BIExp_Plus
      (BExp_Den (BVar "r1" (BType_Imm Bit64)))
      (BExp_Const (Imm64 1w)))];
    bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x004w)))|>;
  <|bb_label := BL_Address (Imm64 0x004w);
    bb_statements :=
      [BStmt_Assign (BVar "r2" (BType_Imm Bit64))
       (BExp_BinExp BIExp_Plus
        (BExp_Den (BVar "r3" (BType_Imm Bit64)))
        (BExp_Const (Imm64 1w)))
      ];
    bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x000w)))|>
 ]
: bir_val_t bir_program_t
``;

val translate_val_bir_prog_reg_set =
 bir_prog_to_mil_iset bir_prog_reg "translate_val_bir_prog_reg_set";

val translate_val_bir_prog_reg_list =
 bir_prog_to_mil_ilist bir_prog_reg "translate_val_bir_prog_reg_list";

(*
 Theorem with name now in DB: DB.find "translate_val_bir_prog_reg_list";
 This will also be found when opening bir_to_mil_testTheory.
*)

Theorem ex_translate_val_bir_prog_reg_list_1[local]:
 !r1 r2 r3.
 LIST_TO_SET (translate_val_bir_prog_reg_list r1 r2 r3 0w 0) =
 translate_val_bir_prog_reg_set r1 r2 r3 0w 0
Proof
 EVAL_TAC >> rw [SUBSET_DEF]
QED

Theorem ex_translate_val_bir_prog_reg_1[local]:
 (let (r1,r2,r3) = (1w,2w,3w) in translate_val_bir_prog_reg_list r1 r2 r3 0w 0) =
 [i_assign 1 (e_val 1w) (o_internal (e_val 1w));
  i_assign 2 (e_val 1w) (o_load res_REG 1);
  i_assign 3 (e_val 1w) (o_internal (e_add (e_name 2) (e_val 1w)));
  i_assign 4 (e_val 1w) (o_store res_REG 1 3);
  i_assign 5 (e_val 1w) (o_internal (e_val 0w));
  i_assign 6 (e_val 1w) (o_load res_PC 5);
  i_assign 7 (e_val 1w) (o_internal (e_add (e_name 6) (e_val 4w)));
  i_assign 8 (e_val 1w) (o_store res_PC 5 7)]
Proof
 EVAL_TAC
QED

Theorem ex_translate_val_bir_prog_reg_2[local]:
 (let (r1,r2,r3) = (1w,2w,3w) in translate_val_bir_prog_reg_list r1 r2 r3 4w 0) =
 [i_assign 1 (e_val 1w) (o_internal (e_val 3w));
  i_assign 2 (e_val 1w) (o_load res_REG 1);
  i_assign 3 (e_val 1w) (o_internal (e_add (e_name 2) (e_val 1w)));
  i_assign 4 (e_val 1w) (o_internal (e_val 2w));
  i_assign 5 (e_val 1w) (o_store res_REG 4 3);
  i_assign 6 (e_val 1w) (o_internal (e_val 0w));
  i_assign 7 (e_val 1w) (o_load res_PC 6);
  i_assign 8 (e_val 1w) (o_internal (e_sub (e_name 7) (e_val 4w)));
  i_assign 9 (e_val 1w) (o_store res_PC 6 8)]
Proof
 EVAL_TAC
QED

Theorem ex_bir_prog_OoO_step_list[local]:
 (let (r1,r2,r3) = (1w,2w,3w) in
  let tr = translate_val_bir_prog_reg_list r1 r2 r3 in
  let (st,tmax) = initialize_state_without_pc_fetch_list [] [(r1,0w);(r2,0w);(r3,0w)] 0w in
  OoO_step_list tr sem_expr_exe st tmax) =
  SOME
    (ll_lb (obs_il 0w)
       (act_ftc_list
          [i_assign 13 (e_val 1w) (o_internal (e_val 1w));
           i_assign 14 (e_val 1w) (o_load res_REG 13);
           i_assign 15 (e_val 1w)
            (o_internal (e_add (e_name 14) (e_val 1w)));
           i_assign 16 (e_val 1w) (o_store res_REG 13 15);
           i_assign 17 (e_val 1w) (o_internal (e_val 0w));
           i_assign 18 (e_val 1w) (o_load res_PC 17);
           i_assign 19 (e_val 1w)
            (o_internal (e_add (e_name 18) (e_val 4w)));
           i_assign 20 (e_val 1w) (o_store res_PC 17 19)]) 12,
     State_st_list
       [i_assign 1 (e_val 1w) (o_internal (e_val 1w));
        i_assign 2 (e_val 1w) (o_internal (e_val 0w));
        i_assign 3 (e_val 1w) (o_store res_REG 1 2);
        i_assign 4 (e_val 1w) (o_internal (e_val 2w));
        i_assign 5 (e_val 1w) (o_internal (e_val 0w));
        i_assign 6 (e_val 1w) (o_store res_REG 4 5);
        i_assign 7 (e_val 1w) (o_internal (e_val 3w));
        i_assign 8 (e_val 1w) (o_internal (e_val 0w));
        i_assign 9 (e_val 1w) (o_store res_REG 7 8);
        i_assign 10 (e_val 1w) (o_internal (e_val 0w));
        i_assign 11 (e_val 1w) (o_internal (e_val 0w));
        i_assign 12 (e_val 1w) (o_store res_PC 10 11);
        i_assign 13 (e_val 1w) (o_internal (e_val 1w));
        i_assign 14 (e_val 1w) (o_load res_REG 13);
        i_assign 15 (e_val 1w) (o_internal (e_add (e_name 14) (e_val 1w)));
        i_assign 16 (e_val 1w) (o_store res_REG 13 15);
        i_assign 17 (e_val 1w) (o_internal (e_val 0w));
        i_assign 18 (e_val 1w) (o_load res_PC 17);
        i_assign 19 (e_val 1w) (o_internal (e_add (e_name 18) (e_val 4w)));
        i_assign 20 (e_val 1w) (o_store res_PC 17 19)]
       (FEMPTY |+ (1,1w) |+ (2,0w) |+ (3,0w) |+ (4,2w) |+ (5,0w) |+
        (6,0w) |+ (7,3w) |+ (8,0w) |+ (9,0w) |+ (10,0w) |+ (11,0w) |+
        (12,0w)) [] [12])
Proof
 EVAL_TAC
QED

Theorem ex_bir_prog_IO_bounded_execution[local]:
 (let (r1,r2,r3) = (1w,2w,3w) in
  let tr = translate_val_bir_prog_reg_list r1 r2 r3 in
  let (st,tmax) = initialize_state_without_pc_fetch_list [] [(r1,0w);(r2,0w);(r3,0w)] 0w in
  IO_bounded_execution tr sem_expr_exe st tmax 1) =
  SOME
   [(State_st_list
       [i_assign 1 (e_val 1w) (o_internal (e_val 1w));
        i_assign 2 (e_val 1w) (o_internal (e_val 0w));
        i_assign 3 (e_val 1w) (o_store res_REG 1 2);
        i_assign 4 (e_val 1w) (o_internal (e_val 2w));
        i_assign 5 (e_val 1w) (o_internal (e_val 0w));
        i_assign 6 (e_val 1w) (o_store res_REG 4 5);
        i_assign 7 (e_val 1w) (o_internal (e_val 3w));
        i_assign 8 (e_val 1w) (o_internal (e_val 0w));
        i_assign 9 (e_val 1w) (o_store res_REG 7 8);
        i_assign 10 (e_val 1w) (o_internal (e_val 0w));
        i_assign 11 (e_val 1w) (o_internal (e_val 0w));
        i_assign 12 (e_val 1w) (o_store res_PC 10 11)]
       (FEMPTY |+ (1,1w) |+ (2,0w) |+ (3,0w) |+ (4,2w) |+ (5,0w) |+
        (6,0w) |+ (7,3w) |+ (8,0w) |+ (9,0w) |+ (10,0w) |+ (11,0w) |+
        (12,0w)) [] [],
     ll_lb (obs_il 0w)
       (act_ftc_list
          [i_assign 13 (e_val 1w) (o_internal (e_val 1w));
           i_assign 14 (e_val 1w) (o_load res_REG 13);
           i_assign 15 (e_val 1w)
             (o_internal (e_add (e_name 14) (e_val 1w)));
           i_assign 16 (e_val 1w) (o_store res_REG 13 15);
           i_assign 17 (e_val 1w) (o_internal (e_val 0w));
           i_assign 18 (e_val 1w) (o_load res_PC 17);
           i_assign 19 (e_val 1w)
             (o_internal (e_add (e_name 18) (e_val 4w)));
           i_assign 20 (e_val 1w) (o_store res_PC 17 19)]) 12,
     State_st_list
       [i_assign 1 (e_val 1w) (o_internal (e_val 1w));
        i_assign 2 (e_val 1w) (o_internal (e_val 0w));
        i_assign 3 (e_val 1w) (o_store res_REG 1 2);
        i_assign 4 (e_val 1w) (o_internal (e_val 2w));
        i_assign 5 (e_val 1w) (o_internal (e_val 0w));
        i_assign 6 (e_val 1w) (o_store res_REG 4 5);
        i_assign 7 (e_val 1w) (o_internal (e_val 3w));
        i_assign 8 (e_val 1w) (o_internal (e_val 0w));
        i_assign 9 (e_val 1w) (o_store res_REG 7 8);
        i_assign 10 (e_val 1w) (o_internal (e_val 0w));
        i_assign 11 (e_val 1w) (o_internal (e_val 0w));
        i_assign 12 (e_val 1w) (o_store res_PC 10 11);
        i_assign 13 (e_val 1w) (o_internal (e_val 1w));
        i_assign 14 (e_val 1w) (o_load res_REG 13);
        i_assign 15 (e_val 1w)
          (o_internal (e_add (e_name 14) (e_val 1w)));
        i_assign 16 (e_val 1w) (o_store res_REG 13 15);
        i_assign 17 (e_val 1w) (o_internal (e_val 0w));
        i_assign 18 (e_val 1w) (o_load res_PC 17);
        i_assign 19 (e_val 1w)
          (o_internal (e_add (e_name 18) (e_val 4w)));
        i_assign 20 (e_val 1w) (o_store res_PC 17 19)]
       (FEMPTY |+ (1,1w) |+ (2,0w) |+ (3,0w) |+ (4,2w) |+ (5,0w) |+
        (6,0w) |+ (7,3w) |+ (8,0w) |+ (9,0w) |+ (10,0w) |+ (11,0w) |+
        (12,0w)) [] [12])]
Proof
 EVAL_TAC
QED

Theorem ex_bir_prog_IO_bounded_trace_1[local]:
 (let (r1,r2,r3) = (1w,2w,3w) in
  let tr = translate_val_bir_prog_reg_list r1 r2 r3 in
  let (st,tmax) = initialize_state_without_pc_fetch_list [] [(r1,0w);(r2,0w);(r3,0w)] 0w in
  IO_bounded_trace tr sem_expr_exe st tmax 1) =
 SOME [obs_il 0w]
Proof
 EVAL_TAC
QED

Theorem ex_bir_prog_IO_bounded_trace_2[local]:
 (let (r1,r2,r3) = (1w,2w,3w) in
  let tr = translate_val_bir_prog_reg_list r1 r2 r3 in
  let (st,tmax) = initialize_state_without_pc_fetch_list [] [(r1,0w);(r2,0w);(r3,0w)] 0w in
  IO_bounded_trace tr sem_expr_exe st tmax 17) =
 SOME [obs_il 0w;obs_il 4w]
Proof
 EVAL_TAC
QED

Theorem ex_bir_prog_IO_bounded_trace_3[local]:
 (let (r1,r2,r3) = (1w,2w,3w) in
  let tr = translate_val_bir_prog_reg_list r1 r2 r3 in
  let (st,tmax) = initialize_state_without_pc_fetch_list [] [(r1,0w);(r2,0w);(r3,0w)] 0w in
  IO_bounded_trace tr sem_expr_exe st tmax 20) =
 SOME [obs_il 0w; obs_il 4w; obs_il 0w]
Proof
 EVAL_TAC
QED

Theorem ex_bir_prog_IO_bounded_trace_long:
 (let (r1,r2,r3) = (1w,2w,3w) in
  let tr = translate_val_bir_prog_reg_list r1 r2 r3 in
  let (st,tmax) = initialize_state_without_pc_fetch_list [] [(r1,0w);(r2,0w);(r3,0w)] 0w in
  IO_bounded_trace tr sem_expr_exe st tmax 200) =
 SOME [obs_il 0w; obs_il 4w; obs_il 0w; obs_il 4w; obs_il 0w; obs_il 4w; obs_il 0w;
  obs_il 4w; obs_il 0w; obs_il 4w; obs_il 0w; obs_il 4w; obs_il 0w; obs_il 4w; obs_il 0w;
  obs_il 4w; obs_il 0w; obs_il 4w; obs_il 0w; obs_il 4w; obs_il 0w; obs_il 4w; obs_il 0w; obs_il 4w]
Proof
 EVAL_TAC
QED

(* get the instruction list
EVAL ``(let (r1,r2,r3) = (1w,2w,3w) in
  let tr = translate_val_bir_prog_reg_list r1 r2 r3 in
  let (st,tmax) = initialize_state_without_pc_fetch_list [] [(r1,0w);(r2,0w);(r3,0w)] 0w in
  IO_bounded_trace_aux tr sem_expr_exe st tmax 200)``
 *)
        
val _ = export_theory ();
