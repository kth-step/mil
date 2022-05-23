open HolKernel boolLib Parse bossLib wordsLib optionTheory wordsTheory finite_mapTheory pred_setTheory listTheory rich_listTheory ottTheory milTheory milUtilityTheory milMetaTheory milInitializationTheory milExecutableUtilityTheory milExecutableTransitionTheory milExecutableInitializationTheory milExecutableExamplesTheory milExecutableIOTheory milExecutableIOTraceTheory bir_programTheory bir_to_milLib;

val _ = new_theory "bir_to_mil_test_cast";

val bir_prog = ``
 BirProgram
   [<|bb_label := BL_Address (Imm64 0x400570w);
         bb_statements :=
           [BStmt_Assign (BVar "SP_EL0" (BType_Imm Bit64))
              (BExp_BinExp BIExp_Minus
                 (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                 (BExp_Const (Imm64 112w)))];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400574w)))|>;
       <|bb_label := BL_Address (Imm64 0x400574w);
         bb_statements :=
           [BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 7w))) (BExp_Const (Imm64 0w)));
            BStmt_Assert
              (BExp_BinExp BIExp_And
                 (BExp_BinPred BIExp_LessOrEqual
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 24w)))
                    (BExp_Const (Imm64 0xFFFFFFFFFFFFFFF7w)))
                 (BExp_BinExp BIExp_And
                    (BExp_BinExp BIExp_Or
                       (BExp_BinPred BIExp_LessThan (BExp_Const (Imm64 0w))
                          (BExp_BinExp BIExp_Plus
                             (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                             (BExp_Const (Imm64 24w))))
                       (BExp_BinPred BIExp_LessOrEqual
                          (BExp_BinExp BIExp_Plus (BExp_Const (Imm64 8w))
                             (BExp_BinExp BIExp_Plus
                                (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                                (BExp_Const (Imm64 24w))))
                          (BExp_Const (Imm64 0w))))
                    (BExp_BinExp BIExp_Or
                       (BExp_BinPred BIExp_LessThan
                          (BExp_BinExp BIExp_Plus
                             (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                             (BExp_Const (Imm64 24w)))
                          (BExp_Const (Imm64 0w)))
                       (BExp_BinPred BIExp_LessOrEqual
                          (BExp_Const (Imm64 0x1000000w))
                          (BExp_BinExp BIExp_Plus
                             (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                             (BExp_Const (Imm64 24w)))))));
            BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
              (BExp_Store (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 24w))) BEnd_LittleEndian
                 (BExp_Den (BVar "R0" (BType_Imm Bit64))))];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x400578w)))|>;
       <|bb_label := BL_Address (Imm64 0x400578w);
         bb_statements :=
           [BStmt_Assert
              (BExp_BinPred BIExp_Equal
                 (BExp_BinExp BIExp_And
                    (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 3w))) (BExp_Const (Imm64 0w)));
            BStmt_Assert
              (BExp_BinExp BIExp_And
                 (BExp_BinPred BIExp_LessOrEqual
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 20w)))
                    (BExp_Const (Imm64 0xFFFFFFFFFFFFFFFBw)))
                 (BExp_BinExp BIExp_And
                    (BExp_BinExp BIExp_Or
                       (BExp_BinPred BIExp_LessThan (BExp_Const (Imm64 0w))
                          (BExp_BinExp BIExp_Plus
                             (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                             (BExp_Const (Imm64 20w))))
                       (BExp_BinPred BIExp_LessOrEqual
                          (BExp_BinExp BIExp_Plus (BExp_Const (Imm64 4w))
                             (BExp_BinExp BIExp_Plus
                                (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                                (BExp_Const (Imm64 20w))))
                          (BExp_Const (Imm64 0w))))
                    (BExp_BinExp BIExp_Or
                       (BExp_BinPred BIExp_LessThan
                          (BExp_BinExp BIExp_Plus
                             (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                             (BExp_Const (Imm64 20w)))
                          (BExp_Const (Imm64 0w)))
                       (BExp_BinPred BIExp_LessOrEqual
                          (BExp_Const (Imm64 0x1000000w))
                          (BExp_BinExp BIExp_Plus
                             (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                             (BExp_Const (Imm64 20w)))))));
            BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
              (BExp_Store (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 20w))) BEnd_LittleEndian
                 (BExp_Cast BIExp_LowCast
                    (BExp_Den (BVar "R1" (BType_Imm Bit64))) Bit32))];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x40057Cw)))|>]
: bir_val_t bir_program_t
``;

val translate_val_bir_prog_list =
 bir_prog_to_mil_ilist bir_prog "translate_val_bir_prog_list";

(* EVAL ``translate_val_bir_prog_list 2w 0w 1w 0x400570w 0`` *)

Theorem bir_cast_prog_IO_bounded_trace_1[local]:
 (let (SP_EL0,R0,R1) = (2w,0w,1w) in
  let tr = translate_val_bir_prog_list SP_EL0 R0 R1 in
  let (st,tmax) = initialize_state_without_pc_fetch_list [] [(SP_EL0,0x80000000w);(R0,0w);(R1,0w)] 0x400570w in
  IO_bounded_trace tr sem_expr_exe st tmax 1) =
 SOME [obs_il 0x400570w]
Proof
 EVAL_TAC
QED
  
Theorem bir_cast_prog_IO_bounded_trace_28[local]:
 (let (SP_EL0,R0,R1) = (2w,0w,1w) in
  let tr = translate_val_bir_prog_list SP_EL0 R0 R1 in
  let (st,tmax) = initialize_state_without_pc_fetch_list [] [(SP_EL0,0x80000000w);(R0,0w);(R1,0w)] 0x400570w in
  IO_bounded_trace tr sem_expr_exe st tmax 28) =
 SOME [obs_il 0x400570w; obs_il 0x400574w; obs_ds 0x7FFFFFA8w;
       obs_il 0x400578w; obs_ds 0x7FFFFFA4w]
Proof
 EVAL_TAC
QED
 
val _ = export_theory ();
