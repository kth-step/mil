open HolKernel boolLib Parse bossLib wordsLib optionTheory wordsTheory integer_wordTheory finite_mapTheory pred_setTheory listTheory rich_listTheory ottTheory milTheory milUtilityTheory milMetaTheory milInitializationTheory milExecutableUtilityTheory milExecutableTransitionTheory milExecutableInitializationTheory milExecutableExamplesTheory milExecutableIOTheory milExecutableIOTraceTheory;

(* ============================================= *)
(* Using IO executor for examples of MIL program *)
(* ============================================= *)

val _ = new_theory "milExecutableHelper";

(* Example assignment: r := r + 1 *)
Definition example_assignment_exe:
 example_assignment_exe r1 (v:v) t =
   [i_assign (t+1) (e_val val_true) (o_internal (e_val val_zero));
    i_assign (t+2) (e_val val_true) (o_internal (e_val r1));
    i_assign (t+3) (e_val val_true) (o_load res_REG (t+2));
    i_assign (t+4) (e_val val_true) (o_internal (e_add (e_name (t+3)) (e_val val_one)));
    i_assign (t+5) (e_val val_true) (o_store res_REG (t+2) (t+4));
    i_assign (t+6) (e_val val_true) (o_load res_PC (t+1));
    i_assign (t+7) (e_val val_true) (o_internal (e_add (e_name (t+6)) (e_val 4w)));
    i_assign (t+8) (e_val val_true) (o_store res_PC (t+1) (t+7))]
End

Definition example_assignment_IO_bounded_exe:
  example_assignment_IO_bounded_exe a b r1 n =
  let tr = example_assignment_exe r1 in
  let (st,tmax) = initialize_state_without_pc_fetch_list [] [(r1,a)] b in    
    IO_bounded_execution tr sem_expr_exe st tmax n
End

Definition example_assignment_IO_bounded_trace:
  example_assignment_IO_bounded_trace a b r1 n =
  let tr = example_assignment_exe r1 in
  let (st,tmax) = initialize_state_without_pc_fetch_list [] [(r1,a)] b in    
    IO_bounded_trace tr sem_expr_exe st tmax n
End

(* Theorems for example_assignment_exe *)
(* a is the initial value for REG r1, b is the initial value for PC *)
Theorem example_assignment_IO_bounded_execution[local]:
 !a b r1.
   example_assignment_IO_bounded_exe a b r1 1 =
   SOME
       [(State_st_list
           [i_assign 1 (e_val 1w) (o_internal (e_val r1));
            i_assign 2 (e_val 1w) (o_internal (e_val a));
            i_assign 3 (e_val 1w) (o_store res_REG 1 2);
            i_assign 4 (e_val 1w) (o_internal (e_val 0w));
            i_assign 5 (e_val 1w) (o_internal (e_val b));
            i_assign 6 (e_val 1w) (o_store res_PC 4 5)]
           (FEMPTY |+ (1,r1) |+ (2,a) |+ (3,a) |+ (4,0w) |+ (5,b) |+ (6,b))
           [] [],
         ll_lb (obs_il b)
           (act_ftc_list
              [i_assign 7 (e_val 1w) (o_internal (e_val 0w));
               i_assign 8 (e_val 1w) (o_internal (e_val r1));
               i_assign 9 (e_val 1w) (o_load res_REG 8);
               i_assign 10 (e_val 1w)
                 (o_internal (e_add (e_name 9) (e_val 1w)));
               i_assign 11 (e_val 1w) (o_store res_REG 8 10);
               i_assign 12 (e_val 1w) (o_load res_PC 7);
               i_assign 13 (e_val 1w)
                 (o_internal (e_add (e_name 12) (e_val 4w)));
               i_assign 14 (e_val 1w) (o_store res_PC 7 13)]) 6,
         State_st_list
           [i_assign 1 (e_val 1w) (o_internal (e_val r1));
            i_assign 2 (e_val 1w) (o_internal (e_val a));
            i_assign 3 (e_val 1w) (o_store res_REG 1 2);
            i_assign 4 (e_val 1w) (o_internal (e_val 0w));
            i_assign 5 (e_val 1w) (o_internal (e_val b));
            i_assign 6 (e_val 1w) (o_store res_PC 4 5);
            i_assign 7 (e_val 1w) (o_internal (e_val 0w));
            i_assign 8 (e_val 1w) (o_internal (e_val r1));
            i_assign 9 (e_val 1w) (o_load res_REG 8);
            i_assign 10 (e_val 1w) (o_internal (e_add (e_name 9) (e_val 1w)));
            i_assign 11 (e_val 1w) (o_store res_REG 8 10);
            i_assign 12 (e_val 1w) (o_load res_PC 7);
            i_assign 13 (e_val 1w)
              (o_internal (e_add (e_name 12) (e_val 4w)));
            i_assign 14 (e_val 1w) (o_store res_PC 7 13)]
           (FEMPTY |+ (1,r1) |+ (2,a) |+ (3,a) |+ (4,0w) |+ (5,b) |+ (6,b))
           [] [6])]  
Proof
  rw [] >> EVAL_TAC
QED

Theorem example_assignment_IO_bound_trace_1[local]:
  !a b r1.
    example_assignment_IO_bounded_trace a b r1 1 = SOME [obs_il b]
Proof
  rw [] >> EVAL_TAC
QED

Theorem example_assignment_IO_bound_trace_2[local]:
  !a b r1.
    example_assignment_IO_bounded_trace a b r1 9 = SOME [obs_il b; obs_il (b + 4w)]
Proof
  rw [] >> EVAL_TAC
QED

(* Example moving values: mov r1 r5 *)
Definition example_mov_exe:
 example_mov_exe r1 r5 (v:v) t =
   [i_assign (t+1) (e_val val_true) (o_internal (e_val val_zero));
    i_assign (t+2) (e_val val_true) (o_internal (e_val r1));
    i_assign (t+3) (e_val val_true) (o_internal (e_val r5));
    i_assign (t+4) (e_val val_true) (o_load res_REG (t+3));
    i_assign (t+5) (e_val val_true) (o_store res_REG (t+2) (t+4));
    i_assign (t+6) (e_val val_true) (o_load res_PC (t+1));
    i_assign (t+7) (e_val val_true) (o_internal (e_add (e_name (t+6)) (e_val 4w)));
    i_assign (t+8) (e_val val_true) (o_store res_PC (t+1) (t+7))]
End

Definition example_mov_IO_bounded_exe:
  example_mov_IO_bounded_exe a b r1 r5 n =
  let tr = example_mov_exe r1 r5 in
  let (st,tmax) = initialize_state_without_pc_fetch_list [] [(r5,a)] b in    
    IO_bounded_execution tr sem_expr_exe st tmax n
End

Definition example_mov_IO_bounded_trace:
  example_mov_IO_bounded_trace a b r1 r5 n =
  let tr = example_mov_exe r1 r5 in
  let (st,tmax) = initialize_state_without_pc_fetch_list [] [(r5,a)] b in    
    IO_bounded_trace tr sem_expr_exe st tmax n
End

(* Theorems for example_mov_exe *)
(* a is the initial value for REG r5, b is the initial value for PC *)
Theorem example_mov_IO_bound_trace_1[local]:
  !a b r1 r5.
    example_mov_IO_bounded_trace a b r1 r5 1 = SOME [obs_il b]
Proof
  rw [] >> EVAL_TAC
QED

Theorem example_mov_IO_bound_trace_2[local]:
  !a b r1 r5.
    example_mov_IO_bounded_trace a b r1 r5 9 = SOME [obs_il b; obs_il (b + 4w)]
Proof
  rw [] >> EVAL_TAC
QED

(* Example conditional: beq a *)
Definition example_conditional_exe:
  example_conditional_exe z a (v:v) t =
    [i_assign (t+1) (e_val val_true) (o_internal (e_val val_zero));
     i_assign (t+2) (e_val val_true) (o_internal (e_val z));
     i_assign (t+3) (e_val val_true) (o_load res_REG (t+2));
     i_assign (t+4) (e_val val_true) (o_internal (e_eq (e_name (t+3)) (e_val val_one)));
     i_assign (t+5) (e_val val_true) (o_load res_PC (t+1));
     i_assign (t+6) (e_val val_true) (o_internal (e_val a));
     i_assign (t+7) (e_name (t+4)) (o_store res_PC (t+1) (t+6));
     i_assign (t+8) (e_val val_true) (o_internal (e_add (e_name (t+5)) (e_val 4w)));
     i_assign (t+9) (e_not (e_name (t+4))) (o_store res_PC (t+1) (t+8))]
End

Definition example_conditional_IO_bounded_exe:
  example_conditional_IO_bounded_exe b c z a n =
  (let tr = example_conditional_exe z a in
   let (st,tmax) = initialize_state_without_pc_fetch_list [] [(z,c)] b in
     IO_bounded_execution tr sem_expr_exe st tmax n)
End

Definition example_conditional_IO_bounded_trace:
  example_conditional_IO_bounded_trace b c z a n =
  (let tr = example_conditional_exe z a in
   let (st,tmax) = initialize_state_without_pc_fetch_list [] [(z,c)] b in
     IO_bounded_trace tr sem_expr_exe st tmax n)
End

(* Theorems for example_conditional_exe *)
(* c is the initial value for REG z, b is the initial value for PC *)
Theorem example_conditional_IO_bounded_execution[local]:
  !z a b c.
    example_conditional_IO_bounded_exe b c z a 1 =
    SOME
       [(State_st_list
           [i_assign 1 (e_val 1w) (o_internal (e_val z));
            i_assign 2 (e_val 1w) (o_internal (e_val c));
            i_assign 3 (e_val 1w) (o_store res_REG 1 2);
            i_assign 4 (e_val 1w) (o_internal (e_val 0w));
            i_assign 5 (e_val 1w) (o_internal (e_val b));
            i_assign 6 (e_val 1w) (o_store res_PC 4 5)]
           (FEMPTY |+ (1,z) |+ (2,c) |+ (3,c) |+ (4,0w) |+ (5,b) |+ (6,b)) []
           [],
         ll_lb (obs_il b)
           (act_ftc_list
              [i_assign 7 (e_val 1w) (o_internal (e_val 0w));
               i_assign 8 (e_val 1w) (o_internal (e_val z));
               i_assign 9 (e_val 1w) (o_load res_REG 8);
               i_assign 10 (e_val 1w)
                 (o_internal (e_eq (e_name 9) (e_val 1w)));
               i_assign 11 (e_val 1w) (o_load res_PC 7);
               i_assign 12 (e_val 1w) (o_internal (e_val a));
               i_assign 13 (e_name 10) (o_store res_PC 7 12);
               i_assign 14 (e_val 1w)
                 (o_internal (e_add (e_name 11) (e_val 4w)));
               i_assign 15 (e_not (e_name 10)) (o_store res_PC 7 14)]) 6,
         State_st_list
           [i_assign 1 (e_val 1w) (o_internal (e_val z));
            i_assign 2 (e_val 1w) (o_internal (e_val c));
            i_assign 3 (e_val 1w) (o_store res_REG 1 2);
            i_assign 4 (e_val 1w) (o_internal (e_val 0w));
            i_assign 5 (e_val 1w) (o_internal (e_val b));
            i_assign 6 (e_val 1w) (o_store res_PC 4 5);
            i_assign 7 (e_val 1w) (o_internal (e_val 0w));
            i_assign 8 (e_val 1w) (o_internal (e_val z));
            i_assign 9 (e_val 1w) (o_load res_REG 8);
            i_assign 10 (e_val 1w) (o_internal (e_eq (e_name 9) (e_val 1w)));
            i_assign 11 (e_val 1w) (o_load res_PC 7);
            i_assign 12 (e_val 1w) (o_internal (e_val a));
            i_assign 13 (e_name 10) (o_store res_PC 7 12);
            i_assign 14 (e_val 1w)
              (o_internal (e_add (e_name 11) (e_val 4w)));
            i_assign 15 (e_not (e_name 10)) (o_store res_PC 7 14)]
           (FEMPTY |+ (1,z) |+ (2,c) |+ (3,c) |+ (4,0w) |+ (5,b) |+ (6,b)) []
           [6])]
Proof
  rw [] >> EVAL_TAC
QED

Theorem example_conditional_IO_bounded_trace_1[local]:
  !z a b c.
    example_conditional_IO_bounded_trace b c z a 1 = SOME [obs_il b]
Proof
  rw [] >> EVAL_TAC
QED

(* if reg[z] = val_true, jump to a *)
Theorem val_true_example_conditional_IO_bounded_trace_2[local]:
  !z a b.
    example_conditional_IO_bounded_trace b val_true z a 8 = SOME [obs_il b; obs_il a]
Proof
  rw [] >> EVAL_TAC
QED

(* if reg[z] <> val_true, jump to PC + 4w *)
Theorem not_val_true_example_conditional_IO_bounded_trace_2[local]:
  !z a b c.  
    c <> val_true ==>
    example_conditional_IO_bounded_trace b c z a 10 = SOME [obs_il b; obs_il (b + 4w)]
Proof
  EVAL_TAC >> rw [val_true] >> EVAL_TAC
QED

(* Example SpectreOOO: cmov z, r2, r1 *)
Definition example_spectre_OoO_exe:
  example_spectre_OoO_exe r1 r2 z b1 b2 (v:v) t =
    [i_assign (t+1) (e_val val_true) (o_internal (e_val val_zero));
     i_assign (t+2) (e_val val_true) (o_internal (e_val r1));
     i_assign (t+3) (e_val val_true) (o_internal (e_val r2));
     i_assign (t+4) (e_val val_true) (o_internal (e_val z));
     i_assign (t+5) (e_val val_true) (o_internal (e_val b1));
     i_assign (t+6) (e_val val_true) (o_internal (e_val b2));
     (* r1 := *b1 *)
     i_assign (t+7) (e_val val_true) (o_load res_MEM (t+5));
     i_assign (t+8) (e_val val_true) (o_store res_REG (t+2) (t+7));              
     (* cmov z, r2, r1 *)
     i_assign (t+9) (e_val val_true) (o_load res_REG (t+4));
     i_assign (t+10) (e_eq (e_name (t+9)) (e_val val_one)) (o_load res_REG (t+2));
     i_assign (t+11) (e_eq (e_name (t+9)) (e_val val_one)) (o_store res_REG (t+3) (t+10));
     (* b2 := r2 *)       
     i_assign (t+12) (e_val val_true) (o_load res_REG (t+3));
     i_assign (t+13) (e_val val_true) (o_store res_MEM (t+6) (t+12));
     (* pc := pc + 4w *)
     i_assign (t+14) (e_val val_true) (o_load res_PC (t+1));
     i_assign (t+15) (e_val val_true) (o_internal (e_add (e_name (t+14)) (e_val 4w)));
     i_assign (t+16) (e_val val_true) (o_store res_PC (t+1) (t+15))]
End

Definition example_spectre_OoO_IO_bounded_exe:
  example_spectre_OoO_IO_bounded_exe a b c d r1 r2 z b1 b2 n =
  let tr = example_spectre_OoO_exe r1 r2 z b1 b2 in
  let (st,tmax) = initialize_state_without_pc_fetch_list [(b1,a)] [(z,b);(r2,c)] d in    
    IO_bounded_execution tr sem_expr_exe st tmax n
End

Definition example_spectre_OoO_IO_bounded_trace_aux:
  example_spectre_OoO_IO_bounded_trace_aux a b c d r1 r2 z b1 b2 n =
  let tr = example_spectre_OoO_exe r1 r2 z b1 b2 in
  let (st,tmax) = initialize_state_without_pc_fetch_list [(b1,a)] [(z,b);(r2,c)] d in    
    IO_bounded_trace_aux tr sem_expr_exe st tmax n
End

Definition example_spectre_OoO_IO_bounded_trace:
  example_spectre_OoO_IO_bounded_trace a b c d r1 r2 z b1 b2 n =
  let tr = example_spectre_OoO_exe r1 r2 z b1 b2 in
  let (st,tmax) = initialize_state_without_pc_fetch_list [(b1,a)] [(z,b);(r2,c)] d in    
    IO_bounded_trace tr sem_expr_exe st tmax n
End

(* Theorems for example_spectre_OoO_exe *)
Theorem example_spectre_OoO_IO_bounded_execution[local]:
  !a b c d r1 r2 z b1 b2.
    example_spectre_OoO_IO_bounded_exe a b c d r1 r2 z b1 b2 1 =
    SOME
       [(State_st_list
           [i_assign 1 (e_val 1w) (o_internal (e_val b1));
            i_assign 2 (e_val 1w) (o_internal (e_val a));
            i_assign 3 (e_val 1w) (o_store res_MEM 1 2);
            i_assign 4 (e_val 1w) (o_internal (e_val z));
            i_assign 5 (e_val 1w) (o_internal (e_val b));
            i_assign 6 (e_val 1w) (o_store res_REG 4 5);
            i_assign 7 (e_val 1w) (o_internal (e_val r2));
            i_assign 8 (e_val 1w) (o_internal (e_val c));
            i_assign 9 (e_val 1w) (o_store res_REG 7 8);
            i_assign 10 (e_val 1w) (o_internal (e_val 0w));
            i_assign 11 (e_val 1w) (o_internal (e_val d));
            i_assign 12 (e_val 1w) (o_store res_PC 10 11)]
           (FEMPTY |+ (1,b1) |+ (2,a) |+ (3,a) |+ (4,z) |+ (5,b) |+ (6,b) |+
            (7,r2) |+ (8,c) |+ (9,c) |+ (10,0w) |+ (11,d) |+ (12,d)) [3] [],
         ll_lb (obs_il d)
           (act_ftc_list
              [i_assign 13 (e_val 1w) (o_internal (e_val 0w));
               i_assign 14 (e_val 1w) (o_internal (e_val r1));
               i_assign 15 (e_val 1w) (o_internal (e_val r2));
               i_assign 16 (e_val 1w) (o_internal (e_val z));
               i_assign 17 (e_val 1w) (o_internal (e_val b1));
               i_assign 18 (e_val 1w) (o_internal (e_val b2));
               i_assign 19 (e_val 1w) (o_load res_MEM 17);
               i_assign 20 (e_val 1w) (o_store res_REG 14 19);
               i_assign 21 (e_val 1w) (o_load res_REG 16);
               i_assign 22 (e_eq (e_name 21) (e_val 1w)) (o_load res_REG 14);
               i_assign 23 (e_eq (e_name 21) (e_val 1w))
                 (o_store res_REG 15 22);
               i_assign 24 (e_val 1w) (o_load res_REG 15);
               i_assign 25 (e_val 1w) (o_store res_MEM 18 24);
               i_assign 26 (e_val 1w) (o_load res_PC 13);
               i_assign 27 (e_val 1w)
                 (o_internal (e_add (e_name 26) (e_val 4w)));
               i_assign 28 (e_val 1w) (o_store res_PC 13 27)]) 12,
         State_st_list
           [i_assign 1 (e_val 1w) (o_internal (e_val b1));
            i_assign 2 (e_val 1w) (o_internal (e_val a));
            i_assign 3 (e_val 1w) (o_store res_MEM 1 2);
            i_assign 4 (e_val 1w) (o_internal (e_val z));
            i_assign 5 (e_val 1w) (o_internal (e_val b));
            i_assign 6 (e_val 1w) (o_store res_REG 4 5);
            i_assign 7 (e_val 1w) (o_internal (e_val r2));
            i_assign 8 (e_val 1w) (o_internal (e_val c));
            i_assign 9 (e_val 1w) (o_store res_REG 7 8);
            i_assign 10 (e_val 1w) (o_internal (e_val 0w));
            i_assign 11 (e_val 1w) (o_internal (e_val d));
            i_assign 12 (e_val 1w) (o_store res_PC 10 11);
            i_assign 13 (e_val 1w) (o_internal (e_val 0w));
            i_assign 14 (e_val 1w) (o_internal (e_val r1));
            i_assign 15 (e_val 1w) (o_internal (e_val r2));
            i_assign 16 (e_val 1w) (o_internal (e_val z));
            i_assign 17 (e_val 1w) (o_internal (e_val b1));
            i_assign 18 (e_val 1w) (o_internal (e_val b2));
            i_assign 19 (e_val 1w) (o_load res_MEM 17);
            i_assign 20 (e_val 1w) (o_store res_REG 14 19);
            i_assign 21 (e_val 1w) (o_load res_REG 16);
            i_assign 22 (e_eq (e_name 21) (e_val 1w)) (o_load res_REG 14);
            i_assign 23 (e_eq (e_name 21) (e_val 1w)) (o_store res_REG 15 22);
            i_assign 24 (e_val 1w) (o_load res_REG 15);
            i_assign 25 (e_val 1w) (o_store res_MEM 18 24);
            i_assign 26 (e_val 1w) (o_load res_PC 13);
            i_assign 27 (e_val 1w)
              (o_internal (e_add (e_name 26) (e_val 4w)));
            i_assign 28 (e_val 1w) (o_store res_PC 13 27)]
           (FEMPTY |+ (1,b1) |+ (2,a) |+ (3,a) |+ (4,z) |+ (5,b) |+ (6,b) |+
            (7,r2) |+ (8,c) |+ (9,c) |+ (10,0w) |+ (11,d) |+ (12,d)) [3] [12])]
Proof
  rw [] >> EVAL_TAC
QED

Theorem example_spectre_OoO_IO_bounded_trace_1[local]:
  !a b c d r1 r2 z b1 b2.
    example_spectre_OoO_IO_bounded_trace a b c d r1 r2 z b1 b2 1 = SOME [obs_il d]
Proof
  rw [] >> EVAL_TAC
QED

Theorem example_spectre_OoO_IO_bounded_trace_9[local]:
  !a b c d r1 r2 z b1 b2.
    example_spectre_OoO_IO_bounded_trace a b c d r1 r2 z b1 b2 9 = SOME [obs_il d; obs_dl b1]
Proof
  rw [] >> EVAL_TAC
QED

(* To continue the executable functions we need the assumption that
 * z <> r1 <> r2 /\ b1 <> b2.
 * So here we use 1-5 for r1,r2,z,b1,b2.
 *)
Theorem example_spectre_OoO_IO_bounded_trace_10[local]:
  !a b c d.
    example_spectre_OoO_IO_bounded_trace a b c d 1w 2w 3w 4w 5w 10 = SOME [obs_il d; obs_dl 4w]
Proof
  rw [] >> EVAL_TAC
QED

(* The following executable trace depends on b that is the initial value for z.
 * For in order semantics, no matter b is 1w or not, the traces are the same.
 *)
Theorem b_1w_example_spectre_OoO_IO_bounded_trace_14[local]:
  !a c d.
    example_spectre_OoO_IO_bounded_trace a 1w c d 1w 2w 3w 4w 5w 14 = SOME [obs_il d; obs_dl 4w; obs_ds 5w]
Proof
  rw [] >> EVAL_TAC
QED

Theorem b_1w_example_spectre_OoO_IO_bounded_trace_17[local]:
  !a c d.
    example_spectre_OoO_IO_bounded_trace a 1w c d 1w 2w 3w 4w 5w 17 =
    SOME [obs_il d; obs_dl 4w; obs_ds 5w; obs_il (d + 4w)]
Proof
  rw [] >> EVAL_TAC
QED

Theorem b_not_1w_example_spectre_OoO_IO_bounded_trace_14[local]:
  !a c d.
    example_spectre_OoO_IO_bounded_trace a 0w c d 0w 2w 3w 4w 5w 14 = SOME [obs_il d; obs_dl 4w; obs_ds 5w]
Proof
  rw [] >> EVAL_TAC
QED

Theorem b_not_1w_example_spectre_OoO_IO_bounded_trace_14[local]:
  !a c d.
    example_spectre_OoO_IO_bounded_trace a 0w c d 0w 2w 3w 4w 5w 17 =
    SOME [obs_il d; obs_dl 4w; obs_ds 5w; obs_il (d + 4w)]
Proof
  rw [] >> EVAL_TAC
QED

(* add instructions based on PC *)
Definition example_spectre_OoO_exe_v2:
  example_spectre_OoO_exe_v2 r1 r2 z b1 b2 (v:v) t =
  if v = 0w then                           
  [i_assign (t+1) (e_val val_true) (o_internal (e_val val_zero));
   i_assign (t+2) (e_val val_true) (o_internal (e_val r1));
   i_assign (t+3) (e_val val_true) (o_internal (e_val b1));
   i_assign (t+4) (e_val val_true) (o_load res_MEM (t+3));
   i_assign (t+5) (e_val val_true) (o_store res_REG (t+2) (t+4));
   i_assign (t+6) (e_val val_true) (o_load res_PC (t+1));
   i_assign (t+7) (e_val val_true) (o_internal (e_add (e_name (t+6)) (e_val 4w)));
   i_assign (t+8) (e_val val_true) (o_store res_PC (t+1) (t+7))]
 else if v = 4w then
  [i_assign (t+1) (e_val val_true) (o_internal (e_val val_zero));
   i_assign (t+2) (e_val val_true) (o_internal (e_val r1));
   i_assign (t+3) (e_val val_true) (o_internal (e_val r2));
   i_assign (t+4) (e_val val_true) (o_internal (e_val z));
   i_assign (t+5) (e_val val_true) (o_load res_REG (t+4));
   i_assign (t+6) (e_eq (e_name (t+5)) (e_val val_one)) (o_load res_REG (t+2));
   i_assign (t+7) (e_eq (e_name (t+5)) (e_val val_one)) (o_store res_REG (t+3) (t+6));
   i_assign (t+8) (e_val val_true) (o_load res_PC (t+1));
   i_assign (t+9) (e_val val_true) (o_internal (e_add (e_name (t + 8)) (e_val 4w)));
   i_assign (t+10) (e_val val_true) (o_store res_PC (t+1) (t+9))]
 else if v = 8w then
  [i_assign (t+1) (e_val val_true) (o_internal (e_val val_zero));
   i_assign (t+2) (e_val val_true) (o_internal (e_val r2));
   i_assign (t+3) (e_val val_true) (o_internal (e_val b2));
   i_assign (t+4) (e_val val_true) (o_load res_REG (t+2));
   i_assign (t+5) (e_val val_true) (o_store res_MEM (t+3) (t+4));
   i_assign (t+6) (e_val val_true) (o_load res_PC (t+1));
   i_assign (t+7) (e_val val_true) (o_internal (e_add (e_name (t+6)) (e_val 4w)));
   i_assign (t+8) (e_val val_true) (o_store res_PC (t+1) (t+7))]
 else  []
End

Definition example_spectre_OoO_v2_IO_bounded_exe:
  example_spectre_OoO_v2_IO_bounded_exe a b c r1 r2 z b1 b2 n =
  let tr = example_spectre_OoO_exe_v2 r1 r2 z b1 b2 in
  let (st,tmax) = initialize_state_without_pc_fetch_list [(b1,a)] [(z,b);(r2,c)] 0w in    
    IO_bounded_execution tr sem_expr_exe st tmax n
End

Definition example_spectre_OoO_v2_IO_bounded_trace_aux:
  example_spectre_OoO_v2_IO_bounded_trace_aux a b c r1 r2 z b1 b2 n =
  let tr = example_spectre_OoO_exe_v2 r1 r2 z b1 b2 in
  let (st,tmax) = initialize_state_without_pc_fetch_list [(b1,a)] [(z,b);(r2,c)] 0w in    
    IO_bounded_trace_aux tr sem_expr_exe st tmax n
End

Definition example_spectre_OoO_v2_IO_bounded_trace:
  example_spectre_OoO_v2_IO_bounded_trace a b c r1 r2 z b1 b2 n =
  let tr = example_spectre_OoO_exe_v2 r1 r2 z b1 b2 in
  let (st,tmax) = initialize_state_without_pc_fetch_list [(b1,a)] [(z,b);(r2,c)] 0w in    
    IO_bounded_trace tr sem_expr_exe st tmax n
End

(* Theorems for example_spectre_OoO_exe_v2 *)
Theorem example_spectre_OoO_v2_IO_bounded_execution_1[local]:
  !a b c r1 r2 z b1 b2.
    example_spectre_OoO_v2_IO_bounded_exe a b c r1 r2 z b1 b2 1 =
    SOME
       [(State_st_list
           [i_assign 1 (e_val 1w) (o_internal (e_val b1));
            i_assign 2 (e_val 1w) (o_internal (e_val a));
            i_assign 3 (e_val 1w) (o_store res_MEM 1 2);
            i_assign 4 (e_val 1w) (o_internal (e_val z));
            i_assign 5 (e_val 1w) (o_internal (e_val b));
            i_assign 6 (e_val 1w) (o_store res_REG 4 5);
            i_assign 7 (e_val 1w) (o_internal (e_val r2));
            i_assign 8 (e_val 1w) (o_internal (e_val c));
            i_assign 9 (e_val 1w) (o_store res_REG 7 8);
            i_assign 10 (e_val 1w) (o_internal (e_val 0w));
            i_assign 11 (e_val 1w) (o_internal (e_val 0w));
            i_assign 12 (e_val 1w) (o_store res_PC 10 11)]
           (FEMPTY |+ (1,b1) |+ (2,a) |+ (3,a) |+ (4,z) |+ (5,b) |+ (6,b) |+
            (7,r2) |+ (8,c) |+ (9,c) |+ (10,0w) |+ (11,0w) |+ (12,0w)) [3] [],
         ll_lb (obs_il 0w)
           (act_ftc_list
              [i_assign 13 (e_val 1w) (o_internal (e_val 0w));
               i_assign 14 (e_val 1w) (o_internal (e_val r1));
               i_assign 15 (e_val 1w) (o_internal (e_val b1));
               i_assign 16 (e_val 1w) (o_load res_MEM 15);
               i_assign 17 (e_val 1w) (o_store res_REG 14 16);
               i_assign 18 (e_val 1w) (o_load res_PC 13);
               i_assign 19 (e_val 1w)
                 (o_internal (e_add (e_name 18) (e_val 4w)));
               i_assign 20 (e_val 1w) (o_store res_PC 13 19)]) 12,
         State_st_list
           [i_assign 1 (e_val 1w) (o_internal (e_val b1));
            i_assign 2 (e_val 1w) (o_internal (e_val a));
            i_assign 3 (e_val 1w) (o_store res_MEM 1 2);
            i_assign 4 (e_val 1w) (o_internal (e_val z));
            i_assign 5 (e_val 1w) (o_internal (e_val b));
            i_assign 6 (e_val 1w) (o_store res_REG 4 5);
            i_assign 7 (e_val 1w) (o_internal (e_val r2));
            i_assign 8 (e_val 1w) (o_internal (e_val c));
            i_assign 9 (e_val 1w) (o_store res_REG 7 8);
            i_assign 10 (e_val 1w) (o_internal (e_val 0w));
            i_assign 11 (e_val 1w) (o_internal (e_val 0w));
            i_assign 12 (e_val 1w) (o_store res_PC 10 11);
            i_assign 13 (e_val 1w) (o_internal (e_val 0w));
            i_assign 14 (e_val 1w) (o_internal (e_val r1));
            i_assign 15 (e_val 1w) (o_internal (e_val b1));
            i_assign 16 (e_val 1w) (o_load res_MEM 15);
            i_assign 17 (e_val 1w) (o_store res_REG 14 16);
            i_assign 18 (e_val 1w) (o_load res_PC 13);
            i_assign 19 (e_val 1w)
              (o_internal (e_add (e_name 18) (e_val 4w)));
            i_assign 20 (e_val 1w) (o_store res_PC 13 19)]
           (FEMPTY |+ (1,b1) |+ (2,a) |+ (3,a) |+ (4,z) |+ (5,b) |+ (6,b) |+
            (7,r2) |+ (8,c) |+ (9,c) |+ (10,0w) |+ (11,0w) |+ (12,0w)) [3]
           [12])]
Proof
  rw [] >> EVAL_TAC
QED

Theorem example_spectre_OoO_v2_IO_bounded_trace_1[local]:
  !a b c r1 r2 z b1 b2.
    example_spectre_OoO_v2_IO_bounded_trace a b c r1 r2 z b1 b2 1 = SOME [obs_il 0w]
Proof
  rw [] >> EVAL_TAC
QED

Theorem example_spectre_OoO_v2_IO_bounded_trace_5[local]:
  !a b c r1 r2 z b1 b2.
    example_spectre_OoO_v2_IO_bounded_trace a b c r1 r2 z b1 b2 5 = SOME [obs_il 0w; obs_dl b1]
Proof
  rw [] >> EVAL_TAC
QED

Theorem example_spectre_OoO_v2_IO_bounded_trace_9[local]:
  !a b c r1 r2 z b1 b2.
    example_spectre_OoO_v2_IO_bounded_trace a b c r1 r2 z b1 b2 9 = SOME [obs_il 0w; obs_dl b1; obs_il 4w]
Proof
  rw [] >> EVAL_TAC
QED

(* To continue the executable functions we need the assumption that
 * z <> r1 <> r2 /\ b1 <> b2.
 * So here we use 1-5 for r1,r2,z,b1,b2.
 * The following executable trace depends on b that is the initial value for z.
 * For in order semantics, no matter b is 1w or not, the traces are the same.
 *)
Theorem b_1w_example_spectre_OoO_v2_IO_bounded_trace_19[local]:
  !a c.
    example_spectre_OoO_v2_IO_bounded_trace a 1w c 1w 2w 3w 4w 5w 19 =
    SOME [obs_il 0w; obs_dl 4w; obs_il 4w; obs_il 8w]
Proof
  rw [] >> EVAL_TAC
QED
        
Theorem b_1w_example_spectre_OoO_v2_IO_bounded_trace_24[local]:
  !a c.
    example_spectre_OoO_v2_IO_bounded_trace a 1w c 1w 2w 3w 4w 5w 24 =
    SOME [obs_il 0w; obs_dl 4w; obs_il 4w; obs_il 8w; obs_ds 5w]
Proof
  rw [] >> EVAL_TAC
QED

Theorem b_1w_example_spectre_OoO_v2_IO_bounded_trace_27[local]:
  !a c.
    example_spectre_OoO_v2_IO_bounded_trace a 1w c 1w 2w 3w 4w 5w 27 =
    SOME [obs_il 0w; obs_dl 4w; obs_il 4w; obs_il 8w; obs_ds 5w; obs_il 12w]
Proof
  rw [] >> EVAL_TAC
QED

Theorem b_not_1w_example_spectre_OoO_v2_IO_bounded_trace_19[local]:
   !a c.
    example_spectre_OoO_v2_IO_bounded_trace a 0w c 1w 2w 3w 4w 5w 19 =
    SOME [obs_il 0w; obs_dl 4w; obs_il 4w; obs_il 8w]
Proof
  rw [] >> EVAL_TAC
QED

Theorem b_not_1w_example_spectre_OoO_v2_IO_bounded_trace_24[local]:
   !a c.
    example_spectre_OoO_v2_IO_bounded_trace a 0w c 1w 2w 3w 4w 5w 24 =
    SOME [obs_il 0w; obs_dl 4w; obs_il 4w; obs_il 8w; obs_ds 5w]
Proof
  rw [] >> EVAL_TAC
QED

Theorem b_not_1w_example_spectre_OoO_v2_IO_bounded_trace_27[local]:
   !a c.
    example_spectre_OoO_v2_IO_bounded_trace a 0w c 1w 2w 3w 4w 5w 27 =
    SOME [obs_il 0w; obs_dl 4w; obs_il 4w; obs_il 8w; obs_ds 5w; obs_il 12w]
Proof
  rw [] >> EVAL_TAC
QED
     
val _ = export_theory ();
