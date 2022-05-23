open HolKernel boolLib Parse bossLib wordsLib optionTheory wordsTheory finite_mapTheory pred_setTheory listTheory rich_listTheory ottTheory milTheory milUtilityTheory milMetaTheory milInitializationTheory milExecutableUtilityTheory milExecutableTransitionTheory milExecutableInitializationTheory milExecutableExamplesTheory milExecutableIOTheory milExecutableIOTraceTheory bir_programTheory bir_program_labelsTheory bir_obs_modelLib bir_execLib bir_to_milLib;

val _ = new_theory "milScamvExperiment0";

val bir_prog = ``
 BirProgram
   [<|bb_label := BL_Address_HC (Imm64 0w) "EB02003F (cmp x1, x2)";
      bb_statements :=
        [BStmt_Assign (BVar "ProcState_C" BType_Bool)
            (BExp_nzcv_SUB_C (BExp_Den (BVar "R1" (BType_Imm Bit64)))
               (BExp_Den (BVar "R2" (BType_Imm Bit64))));
         BStmt_Assign (BVar "ProcState_N" BType_Bool)
            (BExp_nzcv_SUB_N Bit64 (BExp_Den (BVar "R1" (BType_Imm Bit64)))
               (BExp_Den (BVar "R2" (BType_Imm Bit64))));
         BStmt_Assign (BVar "ProcState_V" BType_Bool)
            (BExp_nzcv_SUB_V Bit64 (BExp_Den (BVar "R1" (BType_Imm Bit64)))
               (BExp_Den (BVar "R2" (BType_Imm Bit64))));
         BStmt_Assign (BVar "ProcState_Z" BType_Bool)
            (BExp_nzcv_SUB_Z (BExp_Den (BVar "R1" (BType_Imm Bit64)))
               (BExp_Den (BVar "R2" (BType_Imm Bit64))))];
      bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 4w)))|>;
    <|bb_label := BL_Address_HC (Imm64 4w) "54000082 (b.cs 14 <.text+0x14>  // b.hs, b.nlast)";
      bb_statements := [];
      bb_last_statement :=
        BStmt_CJmp (BExp_Den (BVar "ProcState_C" BType_Bool))
          (BLE_Label (BL_Address (Imm64 20w)))
          (BLE_Label (BL_Address (Imm64 8w)))|>;
    <|bb_label := BL_Address_HC (Imm64 8w) "F8616864 (ldr x4, [x3, x1])";
      bb_statements :=
        [BStmt_Assert
         (BExp_Aligned Bit64 3
          (BExp_BinExp BIExp_Plus
           (BExp_Den (BVar "R1" (BType_Imm Bit64)))
           (BExp_Den (BVar "R3" (BType_Imm Bit64)))));
         BStmt_Assign (BVar "R4" (BType_Imm Bit64))
           (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
            (BExp_BinExp BIExp_Plus
             (BExp_Den (BVar "R1" (BType_Imm Bit64)))
             (BExp_Den (BVar "R3" (BType_Imm Bit64)))) BEnd_LittleEndian Bit64)];
      bb_last_statement :=
        BStmt_Jmp (BLE_Label (BL_Address (Imm64 12w)))|>;
    <|bb_label :=
        BL_Address_HC (Imm64 12w) "D379E084 (lsl x4, x4, #7)";
      bb_statements :=
        [BStmt_Assign (BVar "R4" (BType_Imm Bit64))
          (BExp_BinExp BIExp_And
           (BExp_Const (Imm64 0xFFFFFFFFFFFFFFFFw))
           (BExp_BinExp BIExp_LeftShift
            (BExp_Den (BVar "R4" (BType_Imm Bit64)))
            (BExp_Const (Imm64 7w))))];
      bb_last_statement :=
        BStmt_Jmp (BLE_Label (BL_Address (Imm64 16w)))|>;
    <|bb_label :=
        BL_Address_HC (Imm64 16w) "F86468A6 (ldr x6, [x5, x4])";
      bb_statements :=
        [BStmt_Assert
         (BExp_Aligned Bit64 3
          (BExp_BinExp BIExp_Plus
           (BExp_Den (BVar "R5" (BType_Imm Bit64)))
           (BExp_Den (BVar "R4" (BType_Imm Bit64)))));
         BStmt_Assign (BVar "R6" (BType_Imm Bit64))
            (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
             (BExp_BinExp BIExp_Plus
              (BExp_Den (BVar "R5" (BType_Imm Bit64)))
              (BExp_Den (BVar "R4" (BType_Imm Bit64)))) BEnd_LittleEndian
             Bit64)];
      bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 20w)))|>]
: bir_val_t bir_program_t
``;

val mnf_prog = bir_prog_to_mnf bir_prog;

val translate_val_bir_prog_list =
 bir_prog_to_mil_ilist mnf_prog "translate_val_bir_prog_list";
        
val _ = export_theory ();
