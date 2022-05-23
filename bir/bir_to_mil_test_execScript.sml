open HolKernel boolLib Parse bossLib wordsLib optionTheory wordsTheory finite_mapTheory pred_setTheory listTheory rich_listTheory ottTheory milTheory milUtilityTheory milMetaTheory milInitializationTheory milExecutableUtilityTheory milExecutableTransitionTheory milExecutableInitializationTheory milExecutableExamplesTheory milExecutableIOTheory bir_execLib bir_to_milLib;

val _ = new_theory "bir_to_mil_test_exec";

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
``;

val validprog_o = NONE;
val welltypedprog_o = NONE;
val state_o = NONE;
val n_max = 20;

val exec_test_thm =
 bir_exec_prog_print "exec_test" bir_prog_reg n_max validprog_o welltypedprog_o state_o;

val _ = export_theory ();
