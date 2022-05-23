open HolKernel boolLib Parse bossLib wordsLib optionTheory wordsTheory integer_wordTheory finite_mapTheory pred_setTheory listTheory rich_listTheory ottTheory milTheory milUtilityTheory milMetaTheory milInitializationTheory milExecutableUtilityTheory milExecutableTransitionTheory milExecutableInitializationTheory milExecutableExamplesTheory milExecutableIOTheory milExecutableIOTraceTheory;

(* ======================================= *)
(* Executable example MIL program for loop *)
(* ======================================= *)

val _ = new_theory "milExampleLoop";

(* example_loop*)
Definition example_loop_exe:
  example_loop_exe R1 R2 R3 R4 R5 a n (v:v) t =
  [i_assign (t+1) (e_val val_true) (o_internal (e_val R1));
   i_assign (t+2) (e_val val_true) (o_internal (e_val R2));
   i_assign (t+3) (e_val val_true) (o_internal (e_val R3));
   i_assign (t+4) (e_val val_true) (o_internal (e_val R4));
   i_assign (t+5) (e_val val_true) (o_internal (e_val R5));
   i_assign (t+6) (e_val val_true) (o_internal (e_val a));         
   i_assign (t+7) (e_val val_true) (o_internal (e_val n));
   i_assign (t+8) (e_val val_true) (o_internal (e_val val_zero));
   (* load R1 *)
   i_assign (t+9) (e_val val_true) (o_load res_REG (t+1));           
   (* t1 + 1 *)
   i_assign (t+10) (e_val val_true) (o_internal (e_add (e_name (t+9)) (e_val 1w)));
   (* t2 < n ? *)
   i_assign (t+11) (e_val val_true) (o_internal (e_lt (e_name (t+10)) (e_name (t+7))));
   (* t2 < n ? ST PC a *)
   i_assign (t+12) (e_name (t+11)) (o_store res_PC (t+8) (t+6));
   (* t2 >= n ? ST PC a+1 *)
   i_assign (t+13) (e_val val_true) (o_internal (e_add (e_name (t+6)) (e_val 4w)));
   i_assign (t+14) (e_not (e_name (t+11))) (o_store res_PC (t+8) (t+13));            
   (* LR R3 *)
   i_assign (t+15) (e_val val_true) (o_load res_REG (t+3));
   (* (t4 >> t1) & 0b1 *)
   i_assign (t+16) (e_val val_true) (o_internal (e_and (e_val 1w) (e_lsr (e_name (t+15)) (e_name (t+9)))));         
   (* LR R4; LR R5; LR R2 *)
   i_assign (t+17) (e_val val_true) (o_load res_REG (t+4));
   i_assign (t+18) (e_val val_true) (o_load res_REG (t+5));
   i_assign (t+19) (e_val val_true) (o_load res_REG (t+2));
   (* (t8*t7) % t6 *)
   i_assign (t+20) (e_val val_true) (o_internal (e_mod (e_mul (e_name (t+19)) (e_name (t+18))) (e_name (t+17))));
   (* t5 ? ST R2 t9 *)
   i_assign (t+21) (e_name (t+16)) (o_store res_REG (t+2) (t+20));
   (* t5*t5 & t6 *)
   i_assign (t+22) (e_val val_true) (o_internal (e_add (e_name (t+17)) (e_mul (e_name (t+16)) (e_name (t+16)))));   
   (* ST R5 t11 *)
   i_assign (t+23) (e_val val_true) (o_store res_REG (t+5) (t+22))]
End

Definition example_loop_exe_IO_bounded_execution:
  example_loop_exe_IO_bounded_execution R1 R2 R3 R4 R5 a n r1v r2v r3v r4v r5v pc0 n1 =
  let tr = example_loop_exe R1 R2 R3 R4 R5 a n in
    let (st,tmax) =
        initialize_state_without_pc_fetch_list [] [(R1,r1v);(R2,r2v);(R3,r3v);(R4,r4v);(R5,r5v)] pc0 in
    IO_bounded_execution tr sem_expr_exe st tmax n1
End

Definition example_loop_exe_IO_bounded_trace_aux:
  example_loop_exe_IO_bounded_trace_aux R1 R2 R3 R4 R5 a n r1v r2v r3v r4v r5v pc0 n1 =
  let tr = example_loop_exe R1 R2 R3 R4 R5 a n in
    let (st,tmax) =
        initialize_state_without_pc_fetch_list [] [(R1,r1v);(R2,r2v);(R3,r3v);(R4,r4v);(R5,r5v)] pc0 in
    IO_bounded_trace_aux tr sem_expr_exe st tmax n1
End

Definition example_loop_exe_IO_bounded_trace:
  example_loop_exe_IO_bounded_trace R1 R2 R3 R4 R5 a n r1v r2v r3v r4v r5v pc0 n1 =
  let tr = example_loop_exe R1 R2 R3 R4 R5 a n in
    let (st,tmax) =
        initialize_state_without_pc_fetch_list [] [(R1,r1v);(R2,r2v);(R3,r3v);(R4,r4v);(R5,r5v)] pc0 in
    IO_bounded_trace tr sem_expr_exe st tmax n1
End

Theorem example_loop_exe_IO_bounded_trace_3_times:
  !a r2v r4v r5v pc0.
    example_loop_exe_IO_bounded_trace 1w 2w 3w 4w 5w a 3w 0w r2v 0w r4v r5v pc0 59 =
    SOME [obs_il pc0; obs_il a; obs_il a; obs_il a]
Proof
  rw [] >> EVAL_TAC
QED

val _ = export_theory ();
