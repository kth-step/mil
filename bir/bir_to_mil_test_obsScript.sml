open HolKernel boolLib Parse bossLib wordsLib optionTheory wordsTheory finite_mapTheory pred_setTheory listTheory rich_listTheory ottTheory milTheory milUtilityTheory milMetaTheory milInitializationTheory milExecutableUtilityTheory milExecutableTransitionTheory milExecutableInitializationTheory milExecutableExamplesTheory milExecutableIOTheory milExecutableIOTraceTheory bir_programTheory bir_obs_modelLib bir_execLib bir_to_milLib;

val _ = new_theory "bir_to_mil_test_obs";

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

val {add_obs=add_obs, id=id, obs_hol_type=obs_hol_type} = get_obs_model "mem_address_pc";

val mem_bounds = mem_bounds_from_hex "0x00000010" "0x90";

val bir_prog_obs = add_obs mem_bounds bir_prog;

val validprog_o = NONE;
val welltypedprog_o = NONE;
val state_o = NONE;
val n_max = 10;

val exec_obs_thm =
 bir_exec_prog_print "exec_obs" bir_prog_obs n_max validprog_o welltypedprog_o state_o;
          
val _ = export_theory ();
