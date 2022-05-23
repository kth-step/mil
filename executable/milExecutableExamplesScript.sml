open HolKernel boolLib Parse bossLib wordsLib optionTheory wordsTheory integer_wordTheory finite_mapTheory pred_setTheory listTheory rich_listTheory ottTheory milTheory milUtilityTheory milMetaTheory milInitializationTheory milExecutableUtilityTheory milExecutableTransitionTheory milExecutableInitializationTheory;

(* ================================ *)
(* MIL executable function examples *)
(* ================================ *)

val _ = new_theory "milExecutableExamples";

(* --------------------------------------- *)
(* Functions needed for executing examples *)
(* --------------------------------------- *)

(* used for eval examples *)
Definition f_sem_expr:
 (f_sem_expr (e_val v) (s:(t |-> v)) = SOME v)
 /\
 (f_sem_expr _ s = NONE)
End

Definition FIND_NONE:
 (FIND_NONE ([]:'a list) (s:'a |-> 'b) : bool = F)
 /\
 (FIND_NONE (a::l) s =
  case FLOOKUP s a of
  | NONE => T
  | SOME _ => FIND_NONE l s)
End

Theorem FIND_NONE_NOT_SUBSET_FDOM[local]:
 !l s. FIND_NONE l s <=> ~(LIST_TO_SET l SUBSET FDOM s)
Proof
 Induct_on `l` >> rw [FIND_NONE] >>
 Cases_on `FLOOKUP s h` >> rw [] >>
 fs [flookup_thm]
QED

Theorem names_e_list_FIND_NONE_correct[local]:
 !e s. (FIND_NONE (names_e_list e) s) <=> ~(names_e e SUBSET FDOM s)
Proof
 rw [FIND_NONE_NOT_SUBSET_FDOM,names_e_list_correct]
QED

Definition v_and:
 v_and (v1:v) (v2:v) : v = word_and v1 v2
End

Definition v_or:
 v_or (v1:v) (v2:v) : v = word_or v1 v2
End

Definition v_xor:
 v_xor (v1:v) (v2:v) : v = word_xor v1 v2
End

Definition v_add:
 v_add (v1:v) (v2:v) : v = word_add v1 v2
End

Definition v_sub:
 v_sub (v1:v) (v2:v) : v = word_sub v1 v2
End

Definition v_mul:
 v_mul (v1:v) (v2:v) : v = word_mul v1 v2
End

Definition v_div:
 v_div (v1:v) (v2:v) : v = word_div v1 v2
End

Definition v_sdiv:
 v_sdiv (v1:v) (v2:v) : v = word_sdiv v1 v2
End

Definition v_mod:
 v_mod (v1:v) (v2:v) : v = word_mod v1 v2
End

Definition v_smod:
 v_smod (v1:v) (v2:v) : v = word_smod v1 v2
End

Definition v_lsl:
 v_lsl (v1:v) (v2:v) : v = word_lsl_bv v1 v2
End

Definition v_lsr:
 v_lsr (v1:v) (v2:v) : v = word_lsr_bv v1 v2
End

Definition v_asr:
 v_asr (v1:v) (v2:v) : v = word_asr_bv v1 v2
End

Definition v_eq:
 v_eq (v1:v) (v2:v) : v =
  if v1 = v2 then
    val_true
  else
    val_false
End

Definition v_neq:
 v_neq (v1:v) (v2:v) : v =
  if v1 = v2 then
    val_false
  else
    val_true
End

Definition v_lt:
 v_lt (v1:v) (v2:v) : v =
  if word_lo v1 v2 then
    val_true
  else
    val_false
End

Definition v_slt:
 v_slt (v1:v) (v2:v) : v =
  if word_lt v1 v2 then
    val_true
  else
    val_false
End

Definition v_le:
 v_le (v1:v) (v2:v) : v =
  if word_ls v1 v2 then
    val_true
  else
    val_false
End

Definition v_sle:
 v_sle (v1:v) (v2:v) : v =
  if word_le v1 v2 then
    val_true
  else
    val_false
End

Definition v_comp:
 v_comp (v:v) : v = word_1comp v
End

Definition v_not:
 v_not (v:v) : v =
  if v = val_false then
    val_true
  else
    val_false
End

(* sem_expr_exe: an executable instance of sem_expr *)
Definition sem_expr_exe:
 (sem_expr_exe (e_val v) s : v option = SOME v)
 /\
 (sem_expr_exe (e_name t) s = FLOOKUP s t)
 /\
 (sem_expr_exe (e_and e1 e2) s =
  case sem_expr_exe e1 s of
  | SOME v1 =>
    (case sem_expr_exe e2 s of
     | SOME v2 => SOME (v_and v1 v2)
     | NONE => NONE)
  | NONE => NONE)
 /\
 (sem_expr_exe (e_or e1 e2) s =
  case sem_expr_exe e1 s of
  | SOME v1 =>
    (case sem_expr_exe e2 s of
     | SOME v2 => SOME (v_or v1 v2)
     | NONE => NONE)
  | NONE => NONE)
 /\
 (sem_expr_exe (e_xor e1 e2) s =
  case sem_expr_exe e1 s of
  | SOME v1 =>
    (case sem_expr_exe e2 s of
     | SOME v2 => SOME (v_xor v1 v2)
     | NONE => NONE)
  | NONE => NONE)
 /\
 (sem_expr_exe (e_add e1 e2) s =
  case sem_expr_exe e1 s of
  | SOME v1 =>
    (case sem_expr_exe e2 s of
     | SOME v2 => SOME (v_add v1 v2)
     | NONE => NONE)
  | NONE => NONE)
 /\
 (sem_expr_exe (e_sub e1 e2) s =
  case sem_expr_exe e1 s of
  | SOME v1 =>
    (case sem_expr_exe e2 s of
     | SOME v2 => SOME (v_sub v1 v2)
     | NONE => NONE)
  | NONE => NONE)
 /\
 (sem_expr_exe (e_mul e1 e2) s =
  case sem_expr_exe e1 s of
  | SOME v1 =>
    (case sem_expr_exe e2 s of
     | SOME v2 => SOME (v_mul v1 v2)
     | NONE => NONE)
  | NONE => NONE)
 /\
 (sem_expr_exe (e_div e1 e2) s =
  case sem_expr_exe e1 s of
  | SOME v1 =>
    (case sem_expr_exe e2 s of
     | SOME v2 => SOME (v_div v1 v2)
     | NONE => NONE)
  | NONE => NONE)
 /\
 (sem_expr_exe (e_sdiv e1 e2) s =
  case sem_expr_exe e1 s of
  | SOME v1 =>
    (case sem_expr_exe e2 s of
     | SOME v2 => SOME (v_sdiv v1 v2)
     | NONE => NONE)
  | NONE => NONE)
 /\
 (sem_expr_exe (e_mod e1 e2) s =
  case sem_expr_exe e1 s of
  | SOME v1 =>
    (case sem_expr_exe e2 s of
     | SOME v2 => SOME (v_mod v1 v2)
     | NONE => NONE)
  | NONE => NONE)
 /\
 (sem_expr_exe (e_smod e1 e2) s =
  case sem_expr_exe e1 s of
  | SOME v1 =>
    (case sem_expr_exe e2 s of
     | SOME v2 => SOME (v_smod v1 v2)
     | NONE => NONE)
  | NONE => NONE)
 /\
 (sem_expr_exe (e_lsl e1 e2) s =
  case sem_expr_exe e1 s of
  | SOME v1 =>
    (case sem_expr_exe e2 s of
     | SOME v2 => SOME (v_lsl v1 v2)
     | NONE => NONE)
  | NONE => NONE)
 /\
 (sem_expr_exe (e_lsr e1 e2) s =
  case sem_expr_exe e1 s of
  | SOME v1 =>
    (case sem_expr_exe e2 s of
     | SOME v2 => SOME (v_lsr v1 v2)
     | NONE => NONE)
  | NONE => NONE)
 /\
 (sem_expr_exe (e_asr e1 e2) s =
  case sem_expr_exe e1 s of
  | SOME v1 =>
    (case sem_expr_exe e2 s of
     | SOME v2 => SOME (v_asr v1 v2)
     | NONE => NONE)
  | NONE => NONE)
 /\
 (sem_expr_exe (e_eq e1 e2) s =
  case sem_expr_exe e1 s of
  | SOME v1 =>
    (case sem_expr_exe e2 s of
     | SOME v2 => SOME (v_eq v1 v2)
     | NONE => NONE)
  | NONE => NONE)
 /\
 (sem_expr_exe (e_neq e1 e2) s =
  case sem_expr_exe e1 s of
  | SOME v1 =>
    (case sem_expr_exe e2 s of
     | SOME v2 => SOME (v_neq v1 v2)
     | NONE => NONE)
  | NONE => NONE)
 /\
 (sem_expr_exe (e_lt e1 e2) s =
  case sem_expr_exe e1 s of
  | SOME v1 =>
    (case sem_expr_exe e2 s of
     | SOME v2 => SOME (v_lt v1 v2)
     | NONE => NONE)
  | NONE => NONE)
 /\
 (sem_expr_exe (e_slt e1 e2) s =
  case sem_expr_exe e1 s of
  | SOME v1 =>
    (case sem_expr_exe e2 s of
     | SOME v2 => SOME (v_slt v1 v2)
     | NONE => NONE)
  | NONE => NONE)
 /\
 (sem_expr_exe (e_le e1 e2) s =
  case sem_expr_exe e1 s of
  | SOME v1 =>
    (case sem_expr_exe e2 s of
     | SOME v2 => SOME (v_le v1 v2)
     | NONE => NONE)
  | NONE => NONE)
 /\
 (sem_expr_exe (e_sle e1 e2) s =
  case sem_expr_exe e1 s of
  | SOME v1 =>
    (case sem_expr_exe e2 s of
     | SOME v2 => SOME (v_sle v1 v2)
     | NONE => NONE)
  | NONE => NONE)
 /\
 (sem_expr_exe (e_comp e) s =
   case sem_expr_exe e s of
   | NONE => NONE
   | SOME v => SOME (v_comp v))
 /\
 (sem_expr_exe (e_not e) s =
   case sem_expr_exe e s of
   | NONE => NONE
   | SOME v => SOME (v_not v))
End

(* translate_val for testing examples *)
Definition translate_val_list_test:
 translate_val_list_test (v:v) (t:t) : i list = []
End

Theorem sem_expr_exe_correct:
 (!e s. ~(?v. sem_expr_exe e s = SOME v) <=> ~(names_e e SUBSET FDOM s)) /\
 (!e s s'.
  (!t. t IN names_e e ==> FLOOKUP s t = FLOOKUP s' t) ==>
  sem_expr_exe e s = sem_expr_exe e s') /\
 (!v s. sem_expr_exe (e_val v) s = SOME v)
Proof
 rw [sem_expr_exe] >-
  (Induct_on `e` >>
   rw [sem_expr_exe,names_e,FLOOKUP_DEF] >>
   Cases_on `sem_expr_exe e s` >> rw [] >>
   Cases_on `sem_expr_exe e' s` >> rw []) >>
 Induct_on `e` >> rw [sem_expr_exe,names_e]
QED

(* some properties Xiaomo needs for his proofs *)
Theorem sem_expr_exe_e_name:
 !t s. sem_expr_exe (e_name t) s = FLOOKUP s t
Proof
 rw [sem_expr_exe]
QED

Theorem sem_expr_exe_e_not:
 !e s. sem_expr_exe (e_not e) s = SOME val_true ==>
  sem_expr_exe e s = SOME val_false
Proof
 rw [sem_expr_exe,v_not] >>
 Cases_on `sem_expr_exe e s` >> fs [] >>
 Cases_on `x = val_false` >> fs [val_true,val_false]
QED

Theorem sem_expr_exe_e_not':
 !e s v. sem_expr_exe (e_not e) s = SOME v /\ v <> val_false ==>
  sem_expr_exe e s = SOME val_false
Proof
 rw [sem_expr_exe,v_not] >>
 Cases_on `sem_expr_exe e s` >> fs [] >>
 Cases_on `x = val_false` >> fs [val_true,val_false]
QED

(* Examples for NONCONT_SUBLIST, no need for definitions *)

Theorem NONCONT_SUBLIST_ex_1[local]:
 NONCONT_SUBLIST [1] [1;1;1] = F
Proof
 EVAL_TAC
QED

Theorem NONCONT_SUBLIST_ex_2[local]:
 NONCONT_SUBLIST [1;2;3;4;5] [2;3] = T
Proof
 EVAL_TAC
QED

Theorem NONCONT_SUBLIST_ex_3[local]:
 NONCONT_SUBLIST [1;2;3;4;5] [2;5] = T
Proof
 EVAL_TAC
QED

Theorem max_bound_name_list_ex_1[local]:
 max_bound_name_list [] = 0
Proof
 EVAL_TAC
QED

Theorem max_bound_name_list_ex_2[local]:
 max_bound_name_list
  [i_assign 1 (e_val val_true) (o_store r 11 1);
   i_assign 2 (e_val val_true) (o_store r 21 2);
   i_assign 3 (e_val val_true) (o_store r 31 3);
   i_assign 4 (e_val val_true) (o_load r 41)] = 4
Proof
 EVAL_TAC
QED

Theorem sort_instr_bound_name_ex_1[local]:
 sort_bound_name_instr
   [i_assign 3 (e_val val_true) (o_store res_PC 1 2);
    i_assign 1 (e_val val_true) (o_internal (e_val val_zero));
    i_assign 2 (e_val val_true) (o_internal (e_val val_zero));
    i_assign 6 (e_val val_true) (o_store res_REG 4 5);
    i_assign 4 (e_val val_true) (o_internal (e_val val_one));
    i_assign 5 (e_val val_true) (o_internal (e_val val_zero))] =
   [i_assign 1 (e_val val_true) (o_internal (e_val val_zero));
    i_assign 2 (e_val val_true) (o_internal (e_val val_zero));
    i_assign 3 (e_val val_true) (o_store res_PC 1 2);
    i_assign 4 (e_val val_true) (o_internal (e_val val_one));
    i_assign 5 (e_val val_true) (o_internal (e_val val_zero));
    i_assign 6 (e_val val_true) (o_store res_REG 4 5)]
Proof
 EVAL_TAC
QED

(* --------------------- *)
(* str_may_list examples *)
(* --------------------- *)

Definition ex_str_may_list_template1:
 ex_str_may_list_template1 s t = str_may_list f_sem_expr (State_st_list [] s [] []) t
End

Definition ex_str_may_list_template2:
 ex_str_may_list_template2 s t c e =
  str_may_list f_sem_expr (State_st_list [i_assign t c (o_internal e)] s [] []) t
End

Definition ex_str_may_list_eg2:
 ex_str_may_list_eg2 =
  ex_str_may_list_template2 FEMPTY 0 (e_val val_true) (e_val val_true)
End

Definition ex_str_may_list_template3:
 ex_str_may_list_template3 s t c r ta =
  str_may_list f_sem_expr (State_st_list [i_assign t c (o_load r ta)] s [] []) t
End

Definition ex_str_may_list_eg3:
 ex_str_may_list_eg3 =
  ex_str_may_list_template3 FEMPTY 0 (e_val val_true) res_MEM 1
End

Definition ex_str_may_list_template4:
 ex_str_may_list_template4 s t c r ta tv =
  str_may_list f_sem_expr (State_st_list [i_assign t c (o_store r ta tv)] s [] []) t
End

Definition ex_str_may_list_eg4:
 ex_str_may_list_eg4 =
  ex_str_may_list_template4 FEMPTY 0 (e_val val_true) res_MEM 1 1
End

Definition ex_str_may_list_template5:
 ex_str_may_list_template5 s t0 t1 t2 t3 c r ta0 tv0 ta1 tv1 ta2 tv2 ta3 =
  let l = [i_assign t0 c (o_store r ta0 tv0);
           i_assign t1 c (o_store r ta1 tv1);
           i_assign t2 c (o_store r ta2 tv2);
           i_assign t3 c (o_load r ta3)] in
  str_may_list f_sem_expr (State_st_list l s [] []) t3
End

Definition ex_str_may_list_eg5:
 ex_str_may_list_eg5 =
  ex_str_may_list_template5 FEMPTY 0 1 2 3 (e_val val_true) res_MEM 1 1 0 2 1 3 1
End

(* --------------------- *)
(* str_may_list examples *)
(* --------------------- *)

Theorem str_may_list_ex_1[local]:
 ex_str_may_list_template1 s t = []
Proof
 EVAL_TAC
QED

Theorem str_may_list_ex_2[local]:
 ex_str_may_list_eg2 = []
Proof
 EVAL_TAC
QED

Theorem str_may_list_ex_3[local]:
 ex_str_may_list_eg3 = []
Proof
 EVAL_TAC
QED

Theorem str_may_list_ex_4[local]:
 ex_str_may_list_eg4 = []
Proof
 EVAL_TAC
QED

Theorem str_may_list_ex_5[local]:
 ex_str_may_list_eg5 =
  [i_assign 0 (e_val val_true) (o_store res_MEM 1 1);
   i_assign 1 (e_val val_true) (o_store res_MEM 0 2);
   i_assign 2 (e_val val_true) (o_store res_MEM 1 3)]
Proof
 EVAL_TAC
QED

(* --------------------- *)
(* str_act_list examples *)
(* --------------------- *)

Definition ex_str_act_list_template:
 ex_str_act_list_template s c r =
  let l =
    [i_assign 1 c (o_store r 11 1);
     i_assign 2 c (o_store r 21 2);
     i_assign 3 c (o_store r 31 3);
     i_assign 4 c (o_load r 41)] in
  str_act_list f_sem_expr (State_st_list l s [] []) 4
End

Definition ex_str_act_list_eg1:
 ex_str_act_list_eg1 =
  ex_str_act_list_template FEMPTY (e_val val_true) res_MEM
End

Definition ex_str_act_list_eg2:
 ex_str_act_list_eg2 =
  ex_str_act_list_template (FEMPTY |+ (11, 1w) |+ (31, 1w)) (e_val val_true) res_MEM
End

Definition ex_str_act_list_eg3:
 ex_str_act_list_eg3 =
  ex_str_act_list_template (FEMPTY |+ (11, 1w) |+ (31, 1w) |+ (41, 1w)) (e_val val_true) res_MEM
End

Theorem str_act_list_ex_1[local]:
 ex_str_act_list_eg1 =
  [i_assign 1 (e_val val_true) (o_store res_MEM 11 1);
   i_assign 2 (e_val val_true) (o_store res_MEM 21 2);
   i_assign 3 (e_val val_true) (o_store res_MEM 31 3)]
Proof
 EVAL_TAC
QED

Theorem str_act_list_ex_2[local]:
 ex_str_act_list_eg2 =
  [i_assign 2 (e_val val_true) (o_store res_MEM 21 2);
   i_assign 3 (e_val val_true) (o_store res_MEM 31 3)]
Proof
 EVAL_TAC
QED

Theorem str_act_list_ex_3[local]:
 ex_str_act_list_eg3 =
  [i_assign 3 (e_val val_true) (o_store res_MEM 31 3)]
Proof
 EVAL_TAC
QED

(* ---------------------- *)
(* sem_instr_exe examples *)
(* ---------------------- *)

Definition ex_sem_instr_exe_template:
 ex_sem_instr_exe_template s t1 t2 t3 t4 ta1 tv1 ta2 tv2 ta3 tv3 ta4 c r cs =
  let l =
   [i_assign t1 c (o_store r ta1 tv1);
    i_assign t2 c (o_store r ta2 tv2);
    i_assign t3 c (o_store r ta3 tv3);
    i_assign t4 c (o_load r ta4)] in
  sem_instr_exe sem_expr_exe (i_assign t4 c (o_load r ta4)) (State_st_list l s cs [])
End

Definition ex_sem_instr_exe_eg1:
 ex_sem_instr_exe_eg1 =
  ex_sem_instr_exe_template (FEMPTY |+ (11, 1w) |+ (31, 1w) |+ (41, 1w) |+ (3,1w))
  1 2 3 4 11 1 21 2 31 3 41 (e_val val_true) res_MEM []
End

Definition ex_sem_instr_exe_eg2:
 ex_sem_instr_exe_eg2 =
  sem_instr_exe sem_expr_exe (i_assign 0 (e_val val_true) (o_internal (e_name 0)))
  (State_st_list [] FEMPTY [] [])
End

Theorem sem_instr_exe_ex_1[local]:
 ex_sem_instr_exe_eg1 =
  SOME (1w,obs_internal)
Proof
 EVAL_TAC
QED

Theorem sem_instr_exe_ex_2[local]:
 ex_sem_instr_exe_eg2 =
  NONE
Proof
 EVAL_TAC
QED

(* ---------------------- *)
(* OoO_step_list examples *)
(* ---------------------- *)

Definition OoO_step_init_eg_1:
 OoO_step_init_eg_1 =
  (OoO_step_list translate_val_list_test sem_expr_exe
   (State_st_list (instrs_completed_store_list res_PC 0w 0w 1 2 3) FEMPTY [] []))
End

Definition OoO_step_init_eg_2:
  OoO_step_init_eg_2 =
   (OoO_step_list translate_val_list_test sem_expr_exe
    (State_st_list (instrs_completed_store_list res_PC 0w 0w 1 2 3) (FEMPTY |+ (1,0w)) [] []))
End

Definition OoO_step_init_eg_3:
  OoO_step_init_eg_3 s =
   (OoO_step_list translate_val_list_test sem_expr_exe
    (State_st_list (instrs_completed_store_list res_PC 0w 0w 1 2 3) (s |+ (1,0w) |+ (2,0w)) [] []))
End

Theorem OoO_step_list_ex_1[local]:
 OoO_step_init_eg_1 1 =
  SOME (ll_lb obs_internal act_exe_list 1,
   State_st_list
   [i_assign 1 (e_val 1w) (o_internal (e_val 0w));
    i_assign 2 (e_val 1w) (o_internal (e_val 0w));
    i_assign 3 (e_val 1w) (o_store res_PC 1 2)] (FEMPTY |+ (1,0w)) [] [])
Proof
 EVAL_TAC
QED

Theorem OoO_step_list_ex_2[local]:
 OoO_step_init_eg_1 2 =
  SOME (ll_lb obs_internal act_exe_list 2,
   State_st_list
    [i_assign 1 (e_val 1w) (o_internal (e_val 0w));
     i_assign 2 (e_val 1w) (o_internal (e_val 0w));
     i_assign 3 (e_val 1w) (o_store res_PC 1 2)] (FEMPTY |+ (2,0w)) [] [])
Proof
 EVAL_TAC
QED

Theorem OoO_step_list_ex_3[local]:
 OoO_step_init_eg_1 3 =
  NONE
Proof
 EVAL_TAC
QED

Theorem OoO_step_list_ex_4[local]:
 OoO_step_init_eg_2 1 =
  NONE
Proof
 EVAL_TAC
QED

Theorem OoO_step_list_ex_5[local]:
 OoO_step_init_eg_2 2 =
  SOME (ll_lb obs_internal act_exe_list 2,
   State_st_list
    [i_assign 1 (e_val 1w) (o_internal (e_val 0w));
     i_assign 2 (e_val 1w) (o_internal (e_val 0w));
     i_assign 3 (e_val 1w) (o_store res_PC 1 2)] (FEMPTY |+ (1,0w) |+ (2,0w)) [] [])
Proof
 EVAL_TAC
QED

Theorem OoO_step_list_ex_6[local]:
 OoO_step_init_eg_2 3 =
  NONE
Proof
 EVAL_TAC
QED

Theorem OoO_step_list_ex_7[local]:
 OoO_step_init_eg_3 FEMPTY 3 =
  SOME (ll_lb obs_internal act_exe_list 3,
   State_st_list
    [i_assign 1 (e_val 1w) (o_internal (e_val 0w));
     i_assign 2 (e_val 1w) (o_internal (e_val 0w));
     i_assign 3 (e_val 1w) (o_store res_PC 1 2)]
     (FEMPTY |+ (1,0w) |+ (2,0w) |+ (3,0w)) [] [])
Proof
 EVAL_TAC
QED

Theorem OoO_step_list_ex_8[local]:
 OoO_step_init_eg_3 (FEMPTY |+ (3,0w)) 3 =
  SOME (ll_lb (obs_il 0w) (act_ftc_list []) 3,
   State_st_list
    [i_assign 1 (e_val 1w) (o_internal (e_val 0w));
     i_assign 2 (e_val 1w) (o_internal (e_val 0w));
     i_assign 3 (e_val 1w) (o_store res_PC 1 2)]
    (FEMPTY |+ (3,0w) |+ (1,0w) |+ (2,0w)) [] [3])
Proof
 EVAL_TAC
QED

(* --------------------- *)
(* IO_step_list examples *)
(* --------------------- *)

(* state template for the conditional example *)
Definition conditional_example_state_template:
  conditional_example_state_template s =
  State_st_list
  [ (* initial stores for PC and REG *)
    i_assign 1 (e_val val_true) (o_internal (e_val val_zero));
    i_assign 2 (e_val val_true) (o_internal (e_val val_zero));
    i_assign 3 (e_val val_true) (o_store res_PC 1 2);
    i_assign 4 (e_val val_true) (o_internal (e_val val_one));
    i_assign 5 (e_val val_true) (o_internal (e_val val_zero));
    i_assign 6 (e_val val_true) (o_store res_REG 4 5);
    (* example conditional *)
    i_assign 7 (e_val val_true) (o_internal (e_val val_zero));
    i_assign 8 (e_val val_true) (o_internal (e_val val_one));
    i_assign 9 (e_val val_true) (o_load res_REG 8);
    i_assign 10 (e_val val_true) (o_internal (e_eq (e_name 9) (e_val val_one)));
    i_assign 11 (e_val val_true) (o_load res_PC 7);
    i_assign 12 (e_val val_true) (o_internal (e_val (4w:v)));
    i_assign 13 (e_name 10) (o_store res_PC 7 12);
    i_assign 14 (e_val val_true) (o_internal (e_add (e_name 11) (e_val 4w)));
    i_assign 15 (e_not (e_name 10)) (o_store res_PC 7 14)]
     (s |+ (1,0w) |+ (2,0w) |+ (3,0w) |+ (4,1w) |+ (5,0w) |+ (6,0w)) [] [3]
End

Definition IO_step_list_conditional_example:
 IO_step_list_conditional_example s t =
  IO_step_list translate_val_list_test sem_expr_exe (conditional_example_state_template s) t
End

Theorem IO_step_list_ex_1[local]:
 IO_step_list_conditional_example FEMPTY 7 =
  SOME (ll_lb obs_internal act_exe_list 7,
  State_st_list
   [i_assign 1 (e_val 1w) (o_internal (e_val 0w));
    i_assign 2 (e_val 1w) (o_internal (e_val 0w));
    i_assign 3 (e_val 1w) (o_store res_PC 1 2);
    i_assign 4 (e_val 1w) (o_internal (e_val 1w));
    i_assign 5 (e_val 1w) (o_internal (e_val 0w));
    i_assign 6 (e_val 1w) (o_store res_REG 4 5);
    i_assign 7 (e_val 1w) (o_internal (e_val 0w));
    i_assign 8 (e_val 1w) (o_internal (e_val 1w));
    i_assign 9 (e_val 1w) (o_load res_REG 8);
    i_assign 10 (e_val 1w) (o_internal (e_eq (e_name 9) (e_val 1w)));
    i_assign 11 (e_val 1w) (o_load res_PC 7);
    i_assign 12 (e_val 1w) (o_internal (e_val 4w));
    i_assign 13 (e_name 10) (o_store res_PC 7 12);
    i_assign 14 (e_val 1w) (o_internal (e_add (e_name 11) (e_val 4w)));
    i_assign 15 (e_not (e_name 10)) (o_store res_PC 7 14)]
    (FEMPTY |+ (1,0w) |+ (2,0w) |+ (3,0w) |+ (4,1w) |+ (5,0w) |+
    (6,0w) |+ (7,0w)) [] [3])
Proof
 EVAL_TAC
QED

Theorem IO_step_list_ex_2[local]:
 IO_step_list_conditional_example (FEMPTY |+ (7,0w)) 8 =
  SOME (ll_lb obs_internal act_exe_list 8,
  State_st_list
  [i_assign 1 (e_val 1w) (o_internal (e_val 0w));
   i_assign 2 (e_val 1w) (o_internal (e_val 0w));
   i_assign 3 (e_val 1w) (o_store res_PC 1 2);
   i_assign 4 (e_val 1w) (o_internal (e_val 1w));
   i_assign 5 (e_val 1w) (o_internal (e_val 0w));
   i_assign 6 (e_val 1w) (o_store res_REG 4 5);
   i_assign 7 (e_val 1w) (o_internal (e_val 0w));
   i_assign 8 (e_val 1w) (o_internal (e_val 1w));
   i_assign 9 (e_val 1w) (o_load res_REG 8);
   i_assign 10 (e_val 1w) (o_internal (e_eq (e_name 9) (e_val 1w)));
   i_assign 11 (e_val 1w) (o_load res_PC 7);
   i_assign 12 (e_val 1w) (o_internal (e_val 4w));
   i_assign 13 (e_name 10) (o_store res_PC 7 12);
   i_assign 14 (e_val 1w) (o_internal (e_add (e_name 11) (e_val 4w)));
   i_assign 15 (e_not (e_name 10)) (o_store res_PC 7 14)]
  (FEMPTY |+ (7,0w) |+ (1,0w) |+ (2,0w) |+ (3,0w) |+ (4,1w) |+
  (5,0w) |+ (6,0w) |+ (8,1w)) [] [3])
Proof
 EVAL_TAC
QED

Theorem IO_step_list_ex_3[local]:
 IO_step_list_conditional_example (FEMPTY |+ (7,0w) |+ (8,1w)) 9 =
  SOME (ll_lb obs_internal act_exe_list 9,
        State_st_list
          [i_assign 1 (e_val 1w) (o_internal (e_val 0w));
           i_assign 2 (e_val 1w) (o_internal (e_val 0w));
           i_assign 3 (e_val 1w) (o_store res_PC 1 2);
           i_assign 4 (e_val 1w) (o_internal (e_val 1w));
           i_assign 5 (e_val 1w) (o_internal (e_val 0w));
           i_assign 6 (e_val 1w) (o_store res_REG 4 5);
           i_assign 7 (e_val 1w) (o_internal (e_val 0w));
           i_assign 8 (e_val 1w) (o_internal (e_val 1w));
           i_assign 9 (e_val 1w) (o_load res_REG 8);
           i_assign 10 (e_val 1w) (o_internal (e_eq (e_name 9) (e_val 1w)));
           i_assign 11 (e_val 1w) (o_load res_PC 7);
           i_assign 12 (e_val 1w) (o_internal (e_val 4w));
           i_assign 13 (e_name 10) (o_store res_PC 7 12);
           i_assign 14 (e_val 1w) (o_internal (e_add (e_name 11) (e_val 4w)));
           i_assign 15 (e_not (e_name 10)) (o_store res_PC 7 14)]
          (FEMPTY |+ (7,0w) |+ (8,1w) |+ (1,0w) |+ (2,0w) |+ (3,0w) |+
           (4,1w) |+ (5,0w) |+ (6,0w) |+ (9,0w)) [] [3])
Proof
 EVAL_TAC
QED

Theorem IO_step_list_ex_4[local]:
 IO_step_list_conditional_example (FEMPTY |+ (7,0w) |+ (8,1w) |+ (9,0w)) 10 =
  SOME (ll_lb obs_internal act_exe_list 10,
        State_st_list
          [i_assign 1 (e_val 1w) (o_internal (e_val 0w));
           i_assign 2 (e_val 1w) (o_internal (e_val 0w));
           i_assign 3 (e_val 1w) (o_store res_PC 1 2);
           i_assign 4 (e_val 1w) (o_internal (e_val 1w));
           i_assign 5 (e_val 1w) (o_internal (e_val 0w));
           i_assign 6 (e_val 1w) (o_store res_REG 4 5);
           i_assign 7 (e_val 1w) (o_internal (e_val 0w));
           i_assign 8 (e_val 1w) (o_internal (e_val 1w));
           i_assign 9 (e_val 1w) (o_load res_REG 8);
           i_assign 10 (e_val 1w) (o_internal (e_eq (e_name 9) (e_val 1w)));
           i_assign 11 (e_val 1w) (o_load res_PC 7);
           i_assign 12 (e_val 1w) (o_internal (e_val 4w));
           i_assign 13 (e_name 10) (o_store res_PC 7 12);
           i_assign 14 (e_val 1w) (o_internal (e_add (e_name 11) (e_val 4w)));
           i_assign 15 (e_not (e_name 10)) (o_store res_PC 7 14)]
          (FEMPTY |+ (7,0w) |+ (8,1w) |+ (9,0w) |+ (1,0w) |+ (2,0w) |+
           (3,0w) |+ (4,1w) |+ (5,0w) |+ (6,0w) |+ (10,0w)) [] [3])
Proof
 EVAL_TAC
QED

Theorem IO_step_list_ex_5[local]:
 IO_step_list_conditional_example
  (FEMPTY |+ (7,0w) |+ (8,1w) |+ (9,0w) |+ (10,0w)) 11 =
  SOME (ll_lb obs_internal act_exe_list 11,
        State_st_list
          [i_assign 1 (e_val 1w) (o_internal (e_val 0w));
           i_assign 2 (e_val 1w) (o_internal (e_val 0w));
           i_assign 3 (e_val 1w) (o_store res_PC 1 2);
           i_assign 4 (e_val 1w) (o_internal (e_val 1w));
           i_assign 5 (e_val 1w) (o_internal (e_val 0w));
           i_assign 6 (e_val 1w) (o_store res_REG 4 5);
           i_assign 7 (e_val 1w) (o_internal (e_val 0w));
           i_assign 8 (e_val 1w) (o_internal (e_val 1w));
           i_assign 9 (e_val 1w) (o_load res_REG 8);
           i_assign 10 (e_val 1w) (o_internal (e_eq (e_name 9) (e_val 1w)));
           i_assign 11 (e_val 1w) (o_load res_PC 7);
           i_assign 12 (e_val 1w) (o_internal (e_val 4w));
           i_assign 13 (e_name 10) (o_store res_PC 7 12);
           i_assign 14 (e_val 1w) (o_internal (e_add (e_name 11) (e_val 4w)));
           i_assign 15 (e_not (e_name 10)) (o_store res_PC 7 14)]
          (FEMPTY |+ (7,0w) |+ (8,1w) |+ (9,0w) |+ (10,0w) |+ (1,0w) |+
           (2,0w) |+ (3,0w) |+ (4,1w) |+ (5,0w) |+ (6,0w) |+ (11,0w)) [] [3])
Proof
 EVAL_TAC
QED

Theorem IO_step_list_ex_6[local]:
 IO_step_list_conditional_example
  (FEMPTY |+ (7,0w) |+ (8,1w) |+ (9,0w) |+ (10,0w) |+ (11,0w)) 12 =
  SOME (ll_lb obs_internal act_exe_list 12,
        State_st_list
          [i_assign 1 (e_val 1w) (o_internal (e_val 0w));
           i_assign 2 (e_val 1w) (o_internal (e_val 0w));
           i_assign 3 (e_val 1w) (o_store res_PC 1 2);
           i_assign 4 (e_val 1w) (o_internal (e_val 1w));
           i_assign 5 (e_val 1w) (o_internal (e_val 0w));
           i_assign 6 (e_val 1w) (o_store res_REG 4 5);
           i_assign 7 (e_val 1w) (o_internal (e_val 0w));
           i_assign 8 (e_val 1w) (o_internal (e_val 1w));
           i_assign 9 (e_val 1w) (o_load res_REG 8);
           i_assign 10 (e_val 1w) (o_internal (e_eq (e_name 9) (e_val 1w)));
           i_assign 11 (e_val 1w) (o_load res_PC 7);
           i_assign 12 (e_val 1w) (o_internal (e_val 4w));
           i_assign 13 (e_name 10) (o_store res_PC 7 12);
           i_assign 14 (e_val 1w) (o_internal (e_add (e_name 11) (e_val 4w)));
           i_assign 15 (e_not (e_name 10)) (o_store res_PC 7 14)]
          (FEMPTY |+ (7,0w) |+ (8,1w) |+ (9,0w) |+ (10,0w) |+ (11,0w) |+
           (1,0w) |+ (2,0w) |+ (3,0w) |+ (4,1w) |+ (5,0w) |+ (6,0w) |+
         (12,4w)) [] [3])
Proof
 EVAL_TAC
QED

Theorem IO_step_list_ex_7[local]:
 IO_step_list_conditional_example
  (FEMPTY |+ (7,0w) |+ (8,1w) |+ (9,0w) |+ (10,0w) |+ (11,0w) |+ (12,4w)) 13 =
  NONE
Proof
 EVAL_TAC
QED

Theorem IO_step_list_ex_8[local]:
 IO_step_list_conditional_example
  (FEMPTY |+ (7,0w) |+ (8,1w) |+ (9,0w) |+ (10,0w) |+ (11,0w) |+ (12,4w)) 14 =
  SOME (ll_lb obs_internal act_exe_list 14,
        State_st_list
          [i_assign 1 (e_val 1w) (o_internal (e_val 0w));
           i_assign 2 (e_val 1w) (o_internal (e_val 0w));
           i_assign 3 (e_val 1w) (o_store res_PC 1 2);
           i_assign 4 (e_val 1w) (o_internal (e_val 1w));
           i_assign 5 (e_val 1w) (o_internal (e_val 0w));
           i_assign 6 (e_val 1w) (o_store res_REG 4 5);
           i_assign 7 (e_val 1w) (o_internal (e_val 0w));
           i_assign 8 (e_val 1w) (o_internal (e_val 1w));
           i_assign 9 (e_val 1w) (o_load res_REG 8);
           i_assign 10 (e_val 1w) (o_internal (e_eq (e_name 9) (e_val 1w)));
           i_assign 11 (e_val 1w) (o_load res_PC 7);
           i_assign 12 (e_val 1w) (o_internal (e_val 4w));
           i_assign 13 (e_name 10) (o_store res_PC 7 12);
           i_assign 14 (e_val 1w) (o_internal (e_add (e_name 11) (e_val 4w)));
           i_assign 15 (e_not (e_name 10)) (o_store res_PC 7 14)]
          (FEMPTY |+ (7,0w) |+ (8,1w) |+ (9,0w) |+ (10,0w) |+ (11,0w) |+
           (12,4w) |+ (1,0w) |+ (2,0w) |+ (3,0w) |+ (4,1w) |+ (5,0w) |+
           (6,0w) |+ (14,4w)) [] [3])
Proof
 EVAL_TAC
QED

Theorem IO_step_list_ex_9[local]:
 IO_step_list_conditional_example
  (FEMPTY |+ (7,0w) |+ (8,1w) |+ (9,0w) |+ (10,0w) |+ (11,0w) |+ (12,4w) |+ (14,4w)) 15 =
  SOME (ll_lb obs_internal act_exe_list 15,
        State_st_list
          [i_assign 1 (e_val 1w) (o_internal (e_val 0w));
           i_assign 2 (e_val 1w) (o_internal (e_val 0w));
           i_assign 3 (e_val 1w) (o_store res_PC 1 2);
           i_assign 4 (e_val 1w) (o_internal (e_val 1w));
           i_assign 5 (e_val 1w) (o_internal (e_val 0w));
           i_assign 6 (e_val 1w) (o_store res_REG 4 5);
           i_assign 7 (e_val 1w) (o_internal (e_val 0w));
           i_assign 8 (e_val 1w) (o_internal (e_val 1w));
           i_assign 9 (e_val 1w) (o_load res_REG 8);
           i_assign 10 (e_val 1w) (o_internal (e_eq (e_name 9) (e_val 1w)));
           i_assign 11 (e_val 1w) (o_load res_PC 7);
           i_assign 12 (e_val 1w) (o_internal (e_val 4w));
           i_assign 13 (e_name 10) (o_store res_PC 7 12);
           i_assign 14 (e_val 1w) (o_internal (e_add (e_name 11) (e_val 4w)));
           i_assign 15 (e_not (e_name 10)) (o_store res_PC 7 14)]
          (FEMPTY |+ (7,0w) |+ (8,1w) |+ (9,0w) |+ (10,0w) |+ (11,0w) |+
           (12,4w) |+ (14,4w) |+ (1,0w) |+ (2,0w) |+ (3,0w) |+ (4,1w) |+
           (5,0w) |+ (6,0w) |+ (15,4w)) [] [3])
Proof
 EVAL_TAC
QED

Theorem IO_step_list_ex_10[local]:
 IO_step_list_conditional_example
  (FEMPTY |+ (7,0w) |+ (8,1w) |+ (9,0w) |+ (10,0w) |+ (11,0w) |+ (12,4w) |+ (14,4w) |+ (15,4w)) 15 =
  SOME (ll_lb (obs_il 4w) (act_ftc_list []) 15,
        State_st_list
          [i_assign 1 (e_val 1w) (o_internal (e_val 0w));
           i_assign 2 (e_val 1w) (o_internal (e_val 0w));
           i_assign 3 (e_val 1w) (o_store res_PC 1 2);
           i_assign 4 (e_val 1w) (o_internal (e_val 1w));
           i_assign 5 (e_val 1w) (o_internal (e_val 0w));
           i_assign 6 (e_val 1w) (o_store res_REG 4 5);
           i_assign 7 (e_val 1w) (o_internal (e_val 0w));
           i_assign 8 (e_val 1w) (o_internal (e_val 1w));
           i_assign 9 (e_val 1w) (o_load res_REG 8);
           i_assign 10 (e_val 1w) (o_internal (e_eq (e_name 9) (e_val 1w)));
           i_assign 11 (e_val 1w) (o_load res_PC 7);
           i_assign 12 (e_val 1w) (o_internal (e_val 4w));
           i_assign 13 (e_name 10) (o_store res_PC 7 12);
           i_assign 14 (e_val 1w) (o_internal (e_add (e_name 11) (e_val 4w)));
           i_assign 15 (e_not (e_name 10)) (o_store res_PC 7 14)]
          (FEMPTY |+ (7,0w) |+ (8,1w) |+ (9,0w) |+ (10,0w) |+ (11,0w) |+
           (12,4w) |+ (14,4w) |+ (15,4w) |+ (1,0w) |+ (2,0w) |+ (3,0w) |+
           (4,1w) |+ (5,0w) |+ (6,0w)) [] [15; 3])
Proof
 EVAL_TAC
QED

Theorem initialize_state_list_ex_1[local]:
 initialize_state_list [(0w,0w)] [(0w,0w)] 0w =
 (State_st_list
   [i_assign 1 (e_val 1w) (o_internal (e_val 0w));
    i_assign 2 (e_val 1w) (o_internal (e_val 0w));
    i_assign 3 (e_val 1w) (o_store res_MEM 1 2);
    i_assign 4 (e_val 1w) (o_internal (e_val 0w));
    i_assign 5 (e_val 1w) (o_internal (e_val 0w));
    i_assign 6 (e_val 1w) (o_store res_REG 4 5);
    i_assign 7 (e_val 1w) (o_internal (e_val 0w));
    i_assign 8 (e_val 1w) (o_internal (e_val 0w));
    i_assign 9 (e_val 1w) (o_store res_PC 7 8)]
   (FEMPTY |+ (1,0w) |+ (2,0w) |+ (3,0w) |+ (4,0w) |+ (5,0w) |+
    (6,0w) |+ (7,0w) |+ (8,0w) |+ (9,0w)) [3] [9],
   9)
Proof
 EVAL_TAC
QED

Theorem initialize_state_without_pc_fetch_list_ex_1[local]:
 initialize_state_without_pc_fetch_list [(0w,0w)] [(0w,0w)] 0w =
 (State_st_list
   [i_assign 1 (e_val 1w) (o_internal (e_val 0w));
    i_assign 2 (e_val 1w) (o_internal (e_val 0w));
    i_assign 3 (e_val 1w) (o_store res_MEM 1 2);
    i_assign 4 (e_val 1w) (o_internal (e_val 0w));
    i_assign 5 (e_val 1w) (o_internal (e_val 0w));
    i_assign 6 (e_val 1w) (o_store res_REG 4 5);
    i_assign 7 (e_val 1w) (o_internal (e_val 0w));
    i_assign 8 (e_val 1w) (o_internal (e_val 0w));
    i_assign 9 (e_val 1w) (o_store res_PC 7 8)]
   (FEMPTY |+ (1,0w) |+ (2,0w) |+ (3,0w) |+ (4,0w) |+ (5,0w) |+
    (6,0w) |+ (7,0w) |+ (8,0w) |+ (9,0w)) [3] [],
   9)
Proof
 EVAL_TAC
QED

val _ = export_theory ();
