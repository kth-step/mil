open preamble ml_translatorLib ml_translatorTheory ml_progLib ml_progTheory basisFunctionsLib milTheory milCakeTheory bir_to_mil_test_basicTheory;

val _ = new_theory "milCakeBir";

Definition bir_prog_reg_trace:
  bir_prog_reg_trace (r1,v1) (r2,v2) (r3,v3) n =
   let init = initialize_state_without_pc_fetch_list_cake [] [(r1,v1);(r2,v2);(r3,v3)] val_zero in
   IO_bounded_trace_cake (translate_val_bir_prog_reg_list r1 r2 r3) sem_expr_exe_cake (FST init) (SND init) n
End

Definition bir_prog_reg_trace_string_app_list:
 bir_prog_reg_trace_string_app_list n =
  fromOption (fromList string_app_list_of_obs) (bir_prog_reg_trace (val_zero,val_zero) (val_one,val_zero) (val_two,val_zero) n)
End

val _ = export_theory ();
