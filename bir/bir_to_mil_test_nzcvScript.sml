open HolKernel boolLib Parse bossLib wordsLib optionTheory wordsTheory finite_mapTheory pred_setTheory listTheory rich_listTheory ottTheory milTheory milUtilityTheory milMetaTheory milInitializationTheory milExecutableUtilityTheory milExecutableTransitionTheory milExecutableInitializationTheory milExecutableExamplesTheory milExecutableIOTheory milExecutableIOTraceTheory bir_to_milLib;

val _ = new_theory "bir_to_mil_test_nzcv";
    
val bir_prog = ``
 BirProgram
  [<|bb_label := BL_Address (Imm64 0w);
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
     bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 4w)))|>]
: bir_val_t bir_program_t
``;

val mnf_prog = bir_prog_to_mnf bir_prog;
        
val translate_val_mnf_prog_set =
 bir_prog_to_mil_iset mnf_prog "translate_val_mnf_prog_set";

val translate_val_mnf_prog_list =
 bir_prog_to_mil_ilist mnf_prog "translate_val_mnf_prog_list";
 
Theorem bir_prog_eq_mnf_prog[local]:
  ^mnf_prog =
     BirProgram
       [<|bb_label := BL_Address (Imm64 0w);
          bb_statements :=
            [BStmt_Assign (BVar "ProcState_C" (BType_Imm Bit1))
               (BExp_BinPred BIExp_LessOrEqual
                  (BExp_Den (BVar "R2" (BType_Imm Bit64)))
                  (BExp_Den (BVar "R1" (BType_Imm Bit64))));
             BStmt_Assign (BVar "ProcState_N" (BType_Imm Bit1))
               (BExp_BinPred BIExp_SignedLessThan
                  (BExp_BinExp BIExp_Minus
                     (BExp_Den (BVar "R1" (BType_Imm Bit64)))
                     (BExp_Den (BVar "R2" (BType_Imm Bit64))))
                  (BExp_Const (Imm64 0w)));
             BStmt_Assign (BVar "ProcState_V" (BType_Imm Bit1))
               (BExp_BinPred BIExp_Equal
                  (BExp_BinPred BIExp_SignedLessThan
                     (BExp_BinExp BIExp_Minus
                        (BExp_Den (BVar "R1" (BType_Imm Bit64)))
                        (BExp_Den (BVar "R2" (BType_Imm Bit64))))
                     (BExp_Const (Imm64 0w)))
                  (BExp_BinPred BIExp_SignedLessOrEqual
                     (BExp_Den (BVar "R2" (BType_Imm Bit64)))
                     (BExp_Den (BVar "R1" (BType_Imm Bit64)))));
             BStmt_Assign (BVar "ProcState_Z" (BType_Imm Bit1))
               (BExp_BinPred BIExp_Equal
                  (BExp_Den (BVar "R1" (BType_Imm Bit64)))
                  (BExp_Den (BVar "R2" (BType_Imm Bit64))))];
          bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 4w)))|>]
Proof
 EVAL_TAC
QED
        
val _ = export_theory ();
