open HolKernel boolLib Parse bossLib wordsTheory milTheory milMetaTheory;

(* ==========================================  *)
(* Example MIL program for register assignment *)
(* =========================================== *)

val _ = new_theory "milExampleAssignment";

(* --------------------- *)
(* Definition of program *)
(* --------------------- *)

(* Translation of "r1 := r1 + 1", example 1 in CCS20 paper *)
Definition example_assignment:
 example_assignment t0 t1 t2 t3 t4 t5 t6 t7 r1 : I =
  { i_assign t0 (e_val val_true) (o_internal (e_val val_zero)); (* zeroed name *)
    i_assign t1 (e_val val_true) (o_internal (e_val r1));
    i_assign t2 (e_val val_true) (o_load res_REG t1);
    i_assign t3 (e_val val_true) (o_internal (e_add (e_name t2) (e_val val_one)));
    i_assign t4 (e_val val_true) (o_store res_REG t1 t3);
    i_assign t5 (e_val val_true) (o_load res_PC t0);
    i_assign t6 (e_val val_true) (o_internal (e_add (e_name t5) (e_val 4w)));
    i_assign t7 (e_val val_true) (o_store res_PC t0 t6)
  }
End

Definition example_assignment_initial_state:
 example_assignment_initial_state t0 t1 t2 t3 t4 t5 t6 t7 r1 =
  State_st (example_assignment t0 t1 t2 t3 t4 t5 t6 t7 r1) FEMPTY {} {}
End

Theorem example_assignment_well_formed_state:
 !t0 t1 t2 t3 t4 t5 t6 t7 r1.
  t0 < t1 /\ t1 < t2 /\ t2 < t3 /\ t3 < t4 /\ t4 < t5 /\ t5 < t6 /\ t6 < t7 ==>
  well_formed_state (example_assignment_initial_state t0 t1 t2 t3 t4 t5 t6 t7 r1)
Proof
 rw [example_assignment_initial_state,well_formed_state,map_down] >| [
  rw [example_assignment],
  fs [example_assignment] >> rw [] >> fs [free_names_instr,bound_name_instr,names_e,names_o],
  fs [example_assignment] >> rw [] >> fs [bound_name_instr],
  fs [example_assignment] >> rw [] >>
  fs [free_names_instr,names_e,names_o] >>
  METIS_TAC [bound_name_instr],
  fs [example_assignment] >> rw [],
  fs [example_assignment] >> rw [],
  fs [example_assignment] >> rw [] >> fs [names_o],
  fs [example_assignment] >> rw []
 ]
QED

val _ = export_theory ();
