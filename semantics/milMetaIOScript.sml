open HolKernel boolLib Parse bossLib wordsTheory finite_mapTheory pred_setTheory milTheory milUtilityTheory milTracesTheory milMetaTheory;

(* -------------------------------------- *)
(* Metatheory of MIL's In-Order Semantics *)
(* -------------------------------------- *)

val _ = new_theory "milMetaIO";

(* Sanity-checking: a discarded microinstruction is completed *)
Theorem discarded_implies_completed[local]:
 !I s C Fs t c mop.
  sem_expr c s = SOME val_false ==>
  Completed (State_st I s C Fs) (i_assign t c mop)
Proof
 rw [] >>
 Cases_on `mop` >| [
   rw [Completed],
   rw [Completed],
   Cases_on `r` >> rw [Completed]
 ]
QED

(* Sanity-checking: a microinstruction which is a committed memory store is completed *)
Theorem committed_implies_completed[local]:
 !I s C Fs t c t1 t2.
  t IN C ==>
  Completed (State_st I s C Fs) (i_assign t c (o_store res_MEM t1 t2))
Proof
  rw [Completed]
QED

(* Sanity-checking: a microinstruction which is a fetched PC store is completed *)
Theorem fetched_implies_completed[local]:
 !I s C Fs t c t1 t2.
  t IN Fs ==>
  Completed (State_st I s C Fs) (i_assign t c (o_store res_PC t1 t2))
Proof
  rw [Completed]
QED

Theorem load_in_fdom_completed[local]:
 !I s C Fs t ta c r.
  t IN FDOM s ==>
  Completed (State_st I s C Fs) (i_assign t c (o_load r ta))
Proof
 rw [Completed]
QED

Theorem internal_in_fdom_completed[local]:
 !I s C Fs t c e.
  t IN FDOM s ==>
  Completed (State_st I s C Fs) (i_assign t c (o_internal e))
Proof
 rw [Completed]
QED

Theorem store_reg_in_fdom_completed[local]:
 !I s C Fs t c ta tv.
  t IN FDOM s ==>
  Completed (State_st I s C Fs) (i_assign t c (o_store res_REG ta tv))
Proof
 rw [Completed]
QED

Theorem store_PC_notin_completed[local]:
 !I s C Fs t c ta tv.
  t NOTIN Fs ==>
  sem_expr c s <> SOME val_false ==>
  ~(Completed (State_st I s C Fs) (i_assign t c (o_store res_PC ta tv)))
Proof
 rw [Completed]
QED

Theorem store_mem_notin_completed[local]:
 !I s C Fs t c ta tv.
  t NOTIN C ==>
  sem_expr c s <> SOME val_false ==>
  ~(Completed (State_st I s C Fs) (i_assign t c (o_store res_MEM ta tv)))
Proof
 rw [Completed]
QED

(* Lemma:
 * In a well-formed state, any committed or fetched microinstruction is already executed.
 *)
Theorem committed_or_fetched_implies_executed[local]:
 !I s C Fs t.
  well_formed_state (State_st I s C Fs) ==>
  (t IN C \/ t IN Fs) ==>
  t IN FDOM s
Proof
  METIS_TAC [well_formed_in_C_in_s,well_formed_in_F_in_s]
QED

(* Lemma:
 * For any OoO transition that involves a microinstruction,
 * the microinstruction was not completed in the previous state.
 *)
Theorem OoO_transition_t_incompleted:
 !I s C Fs S' obs al t.
  well_formed_state (State_st I s C Fs) ==>
  out_of_order_step (State_st I s C Fs) (l_lb obs al t) S' ==>
  ?c mop. i_assign t c mop IN I /\ ~(Completed (State_st I s C Fs) (i_assign t c mop))
Proof
 rw [out_of_order_step_cases] >| [
   (* OoO_Exe *)
   `t NOTIN FDOM s`
     by METIS_TAC [map_up, map_down, flookup_thm] >>
   `~((sem_expr c s = SOME val_false) \/ (t IN FDOM s))`
     by rw [] >>
   Cases_on `op` >| [
     Q.EXISTS_TAC `c` >> Q.EXISTS_TAC `o_internal e` >> METIS_TAC [Completed],
     Q.EXISTS_TAC `c` >> Q.EXISTS_TAC `o_load r n` >> METIS_TAC [Completed],
     Q.EXISTS_TAC `c` >> Q.EXISTS_TAC `o_store r n n0` >>
     `~((sem_expr c s = SOME val_false) \/ (t IN C))`
       by METIS_TAC [committed_or_fetched_implies_executed] >>
     `~((sem_expr c s = SOME val_false) \/ (t IN Fs))`
       by METIS_TAC [committed_or_fetched_implies_executed] >>
     Cases_on `r` >> METIS_TAC [Completed]
   ],
   (* OoO_Cmt *)
   `t IN FDOM s` by METIS_TAC [map_down,flookup_thm] >>
   `i_assign t c (o_store res_MEM t1 t2) IN I'` by METIS_TAC [Completed] >>
   `?v. sem_expr c s = SOME v /\ v <> val_false` by METIS_TAC [map_down,wfs_flookup_condition_not_false] >>
   `~((sem_expr c s = SOME val_false) \/ (t IN C))` by rw [] >>
   METIS_TAC [Completed],
   (* OoO_Ftc *)
   `t IN FDOM s` by METIS_TAC [map_down, flookup_thm] >>
   `i_assign t c (o_store res_PC t1 t2) IN I'` by METIS_TAC [Completed] >>
   `?v. sem_expr c s = SOME v /\ v <> val_false` by METIS_TAC [wfs_flookup_condition_not_false] >>
   `~((sem_expr c s = SOME val_false) \/ (t IN Fs))` by rw [] >>
   METIS_TAC [Completed]
 ]
QED

(* Lemma:
 * There is only one minimum incompleted microinstruction to be completed next in order,
 * if it exists.
 *)
Theorem incompleted_minimum_t_unique[local]:
 !I s C Fs t1 c1 op1 t2 c2 op2.
  i_assign t1 c1 op1 IN I ==>
  i_assign t2 c2 op2 IN I ==>
  (~(Completed (State_st I s C Fs) (i_assign t1 c1 op1)) /\
   !i. i IN I ==> bound_name_instr i < t1 ==> Completed (State_st I s C Fs) i) ==>
  (~(Completed (State_st I s C Fs) (i_assign t2 c2 op2)) /\
   !i. i IN I ==> bound_name_instr i < t2 ==> Completed (State_st I s C Fs) i) ==>
  t1 = t2
Proof
 rw [] >>
 `t1 = t2 \/ t1 < t2 \/ t1 > t2` by DECIDE_TAC >-
 METIS_TAC [Completed, bound_name_instr] >>
 `t2 < t1` by DECIDE_TAC >>
 METIS_TAC [Completed, bound_name_instr]
QED

(* Theorem: In-order transitions are deterministic *)
Theorem IO_transition_deterministic:
 !State0 State1 State2 l1 l2.
  well_formed_state State0 ==>
  in_order_step State0 l1 State1 ==>
  in_order_step State0 l2 State2 ==>
  l1 = l2 /\ State1 = State2
Proof
 REPEAT GEN_TAC >> REPEAT DISCH_TAC >>
 Cases_on `State0` >> rename1 `State_st I0 s0 C0 F0` >>
 fs [in_order_step_cases] >>
 `?i c op. i IN I0 /\ i = i_assign t c op /\ ~(Completed (State_st I0 s0 C0 F0) i)`
   by METIS_TAC [OoO_transition_t_incompleted,instr_in_State] >>
 `?i c op. i IN I0 /\ i = i_assign t' c op /\ ~(Completed (State_st I0 s0 C0 F0) i)`
   by METIS_TAC [OoO_transition_t_incompleted, instr_in_State] >>
 `t = t'` by METIS_TAC [incompleted_minimum_t_unique, instr_in_State] >>
 `act = act'` by METIS_TAC [OoO_transition_deterministic] >>
 METIS_TAC [OoO_transition_deterministic]
QED

(* Sanity-checking:
 * For any IO transition,
 * there is a microinstruction which was not completed in the previous state.
 *)
Theorem IO_transition_t_incompleted[local]:
 !I s C Fs S' l t.
  well_formed_state (State_st I s C Fs) ==>
  in_order_step (State_st I s C Fs) l S' ==>
  ?t' c mop. i_assign t' c mop IN I /\ ~(Completed (State_st I s C Fs) (i_assign t' c mop))
Proof
 rw [in_order_step_cases] >>
 METIS_TAC [OoO_transition_t_incompleted]
QED

Theorem well_formed_IO_transition_well_formed:
 step_invariant in_order_step well_formed_state
Proof
 rw [step_invariant,in_order_step_cases] >>
 METIS_TAC [well_formed_OoO_transition_well_formed,step_invariant]
QED

Theorem well_formed_IO_LTC_invariant:
 LTC_invariant in_order_step well_formed_state
Proof
 METIS_TAC [well_formed_IO_transition_well_formed,step_invariant_LTC_invariant]
QED

Theorem step_execution_mid_IO_well_formed_state:
 !e e' S1 l1 S2 S3 l2 S4. well_formed_state S1 ==>
  step_execution in_order_step ((S1,l1,S2)::e' ++ (S3,l2,S4)::e) ==>
  well_formed_state S4
Proof
 METIS_TAC [step_execution_mid_LTC_invariant,well_formed_IO_LTC_invariant]
QED

Theorem step_execution_mid_FST_OoO_well_formed_state:
 !e e' S1 l1 S2 S3 l2 S4. well_formed_state S1 ==>
  step_execution in_order_step ((S1,l1,S2)::e' ++ (S3,l2,S4)::e) ==>
  well_formed_state S3
Proof
 METIS_TAC [step_execution_mid_FST_LTC_invariant,well_formed_IO_LTC_invariant]
QED

(* Incomplete_t *)
Definition Incomplete_t:
 Incomplete_t (State_st I s C Fs) t =
 (?i. i IN I /\ bound_name_instr i = t /\ ~(Completed (State_st I s C Fs) i))
End

Theorem OoO_transition_incomplete:
 !I s C Fs S' obs al t.
  well_formed_state (State_st I s C Fs) ==>
  out_of_order_step (State_st I s C Fs) (l_lb obs al t) S' ==>
  Incomplete_t (State_st I s C Fs) t
Proof
 rw [out_of_order_step_cases,Incomplete_t] >| [
   (* OoO_Exe *)
   `t NOTIN FDOM s`
     by METIS_TAC [map_up, map_down, flookup_thm] >>
   `~((sem_expr c s = SOME val_false) \/ (t IN FDOM s))`
     by rw [] >>
   Q.EXISTS_TAC `i_assign t c op` >>
   Cases_on `op` >> fs [bound_name_instr] >| [
     METIS_TAC [Completed],
     METIS_TAC [Completed],
     `~((sem_expr c s = SOME val_false) \/ (t IN C))`
       by METIS_TAC [committed_or_fetched_implies_executed] >>
     `~((sem_expr c s = SOME val_false) \/ (t IN Fs))`
       by METIS_TAC [committed_or_fetched_implies_executed] >>
     Cases_on `r` >> METIS_TAC [Completed]
   ],
   (* OoO_Cmt *)
   `t IN FDOM s` by METIS_TAC [map_down,flookup_thm] >>
   `i_assign t c (o_store res_MEM t1 t2) IN I'` by METIS_TAC [Completed] >>
   `?v. sem_expr c s = SOME v /\ v <> val_false` by METIS_TAC [map_down,wfs_flookup_condition_not_false] >>
   `~((sem_expr c s = SOME val_false) \/ (t IN C))` by rw [] >>
   METIS_TAC [Completed,bound_name_instr],
   (* OoO_Ftc *)
   `t IN FDOM s` by METIS_TAC [map_down, flookup_thm] >>
   `i_assign t c (o_store res_PC t1 t2) IN I'` by METIS_TAC [Completed] >>
   `?v. sem_expr c s = SOME v /\ v <> val_false` by METIS_TAC [wfs_flookup_condition_not_false] >>
   `~((sem_expr c s = SOME val_false) \/ (t IN Fs))` by rw [] >>
   METIS_TAC [Completed,bound_name_instr]
 ]
QED

Theorem IO_transition_incomplete:
 !I s C Fs S' ob ac t.
   well_formed_state (State_st I s C Fs) ==>
   in_order_step (State_st I s C Fs) (l_lb ob ac t) S' ==>
   Incomplete_t (State_st I s C Fs) t
Proof
  rw [in_order_step_cases] >>
  METIS_TAC [OoO_transition_incomplete]
QED

val _ = export_theory ();
