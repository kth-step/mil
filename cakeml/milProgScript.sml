open preamble ml_translatorLib ml_translatorTheory ml_progLib basisProgTheory mlmapTheory basisFunctionsLib astPP comparisonTheory milUtilityTheory milTheory milSemanticsUtilityTheory milExecutableUtilityTheory milExecutableInitializationTheory milExecutableIOTheory milExecutableIOTraceTheory milExecutableExamplesTheory milCakeTheory milCakeBirTheory bir_to_mil_test_basicTheory;

val _ = new_theory "milProg";

val _ = translation_extends "basisProg";

val _ = ml_prog_update (open_module "Mil");

(* ----------------------- *)
(* Basic utility functions *)
(* ----------------------- *)

(* TODO: use int_cmp instead, better performance *)
val _ = translate num_cmp_def;

val _ = translate name_le;

val _ = translate bound_name_instr;

val _ = translate FIND_instr;

(* FIXME: need to use Word64.fromInt *)
val _ = translate val_false;

(* FIXME: need to use Word64.fromInt *)
val _ = translate val_true;

(* FIXME: need to use Word64.fromInt *)
val _ = translate val_zero;

(* FIXME: need to use Word64.fromInt *)
val _ = translate val_one;

(* FIXME: need to use Word64.fromInt *)
val _ = translate val_two;

(* FIXME: need to use Word64.fromInt *)
val _ = translate val_four;

(* -------------------------- *)
(* Semantic utility functions *)
(* -------------------------- *)

val _ = translate addr_of_list;

val _ = translate str_may_list_find_cake;

val _ = translate str_may_list_cake;

val _ = translate str_act_list_cond_cake;

val _ = translate str_act_list_find_cake;

val _ = translate str_act_list_cake;

val _ = translate bound_names_program_list;

val _ = translate sem_instr_exe_cake;

val _ = translate Completed_list_cake;

val _ = translate max_bound_name_list;

val _ = translate names_e_list;

val _ = translate obs_of_ll;

val _ = translate obs_visible;

(* ------------------------ *)
(* Initialization functions *)
(* ------------------------ *)

val _ = translate empty_state_list_cake;

val _ = translate instrs_completed_store_list;

val _ = translate initialize_resource_at_list_cake;

val _ = translate initialize_pc_without_fetch_at_list_cake;

val _ = translate init_res_val_list_cake;

val _ = translate init_pc_without_fetch_val_list_cake;

val _ = translate init_res_list_cake;

val _ = translate initialize_state_list_cake;

val _ = translate initialize_state_without_pc_fetch_list;

(* ------------------------- *)
(* Pretty-printing functions *)
(* ------------------------- *)

val _ = translate string_app_list_of_res;

val _ = translate string_app_paren_binop;

val _ = translate string_app_paren_unop;

val _ = translate string_app_list_of_e;

val _ = translate string_app_list_of_o;

val _ = translate string_app_list_of_i;

val _ = translate string_app_list_of_obs;

(* -------------- *)
(* Step functions *)
(* -------------- *)

val _ = translate word_2comp_cake;
val _ = translate i2w_cake;
val _ = translate word_msb_cake;
val _ = translate w2i_cake;

val _ = translate bitTheory.MOD_2EXP_def;
val _ = translate bitTheory.DIV_2EXP_def;
val _ = translate bitTheory.BITS_def;
val _ = translate bitTheory.BIT_def;
val _ = translate nzcv_cake;

val _ = translate v_and_cake;
val _ = translate v_or_cake;
val _ = translate v_xor_cake;
val _ = translate v_add_cake;
val _ = translate v_sub_cake;
val _ = translate v_mul_cake;
val _ = translate v_div_cake;
val _ = translate v_sdiv_cake;
val _ = translate v_mod_cake;
val _ = translate v_smod_cake;
val _ = translate v_lsl_cake;
val _ = translate v_lsr_cake;
val _ = translate v_asr_cake;
val _ = translate v_eq_cake;
val _ = translate v_neq_cake;
val _ = translate v_lt_cake;
val _ = translate v_slt_cake;
val _ = translate v_le_cake;
val _ = translate v_sle_cake;
val _ = translate v_comp_cake;
val _ = translate v_not_cake;

val _ = translate sem_expr_exe_cake;

val _ = translate OoO_step_name_cake;

val _ = translate OoO_Exe_list_instr_not_stored_guard_true_sem_instr_cake;

val _ = translate OoO_Exe_list_instr_not_stored_guard_true_cake;

val _ = translate OoO_Exe_list_instr_not_stored_cake;

val _ = translate OoO_Exe_list_instr_cake;

val _ = translate OoO_Exe_list_cake;

val _ = translate OoO_Cmt_list_stored_incomplete_cake;

val _ = translate OoO_Cmt_list_stored_cake;

val _ = translate OoO_Cmt_list_instr_cake;

val _ = translate OoO_Cmt_list_cake;

val _ = translate OoO_Ftc_list_stored_incomplete_cake;

val _ = translate OoO_Ftc_list_stored_cake;

val _ = translate OoO_Ftc_list_instr_cake;

val _ = translate OoO_Ftc_list_cake;

val _ = translate OoO_step_list_instr_cake;

val _ = translate OoO_step_list_cake;

val _ = translate IO_bounded_execution_acc_cake;

val _ = translate IO_bounded_execution_cake;

val _ = translate IO_bounded_trace_acc_cake;

val _ = translate IO_bounded_trace_aux_cake;

val _ = translate IO_bounded_trace_cake;

val _ = ml_prog_update (close_module NONE);

(* ------------- *)
(* BIR functions *)
(* ------------- *)

(* FIXME: need to use Word64.fromInt *)

(* FIXME: consequences of "WARNING: translate_val_bir_prog_reg_list has a precondition."? *)

val _ = translate translate_val_bir_prog_reg_list;

val _ = translate bir_prog_reg_trace;

val _ = translate bir_prog_reg_trace_string_app_list;

(* ------------------------------ *)
(* Pretty-printing Mil module AST *)
(* ------------------------------ *)

fun get_current_prog () =
  let
    val state = get_ml_prog_state ()
    val state_thm =
     state |> ml_progLib.remove_snocs
           |> ml_progLib.clean_state
           |> get_thm
  in
    state_thm |> concl |> strip_comb |> #2 |> el 2
  end
;

val _ = astPP.enable_astPP();

val _ = Globals.max_print_depth := 100;

val _ = print_term (get_current_prog ());

val _ = Globals.max_print_depth := 20;

val _ = astPP.disable_astPP();

val _ = export_theory();
