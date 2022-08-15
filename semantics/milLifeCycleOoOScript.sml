open HolKernel Parse boolLib bossLib finite_mapTheory pred_setTheory milUtilityTheory milTheory milSemanticsUtilityTheory milTracesTheory milMetaTheory;

(* ============================================ *)
(* MIL instruction lifecycles for OoO semantics *)
(* ============================================ *)

val _ = new_theory "milLifeCycleOoO";

Datatype:
 out_of_order_lifecycle =
 | out_of_order_lifecycle_Decoded
 | out_of_order_lifecycle_Executed
 | out_of_order_lifecycle_Committed
 | out_of_order_lifecycle_Fetched
End

val out_of_order_lifecycle_distinct = fetch "-" "out_of_order_lifecycle_distinct";

Definition out_of_order_lifecycle_pred:
 (out_of_order_lifecycle_pred out_of_order_lifecycle_Decoded (State_st I' s Cs Fs) t =
  (t IN bound_names_program I' /\ map_up s t /\ t NOTIN Cs UNION Fs))
 /\
 (out_of_order_lifecycle_pred out_of_order_lifecycle_Executed (State_st I' s Cs Fs) t =
  (map_down s t /\ t NOTIN Cs UNION Fs))
 /\
 (out_of_order_lifecycle_pred out_of_order_lifecycle_Committed (State_st I' s Cs Fs) t =
  (map_down s t /\ t IN Cs /\ t NOTIN Fs))
 /\
 (out_of_order_lifecycle_pred out_of_order_lifecycle_Fetched (State_st I' s Cs Fs) t =
  (map_down s t /\ t NOTIN Cs /\ t IN Fs))
End

Inductive out_of_order_lifecycle_tr:
 (out_of_order_lifecycle_tr
   out_of_order_lifecycle_Decoded act_exe out_of_order_lifecycle_Executed)
 /\
 (!a v. out_of_order_lifecycle_tr
   out_of_order_lifecycle_Executed (act_cmt a v) out_of_order_lifecycle_Committed)
 /\
 (!I'. out_of_order_lifecycle_tr
   out_of_order_lifecycle_Executed (act_ftc I') out_of_order_lifecycle_Fetched)
End

(* names which have an abstract state are in the program *)
Theorem out_of_order_lifecycle_pred_name_in_state:
 !lc State t. well_formed_state State ==>
  out_of_order_lifecycle_pred lc State t ==>
  name_instr_in_State t State
Proof
 Cases_on `lc` >> Cases_on `State` >> rename1 `State_st I' s Cs Fs` >>
 rw [out_of_order_lifecycle_pred,name_instr_in_State,map_down] >>
 `t IN FDOM s` by fs [FLOOKUP_DEF] >>
 METIS_TAC [wfs_FDOM_SUBSET_bound_names,SUBSET_DEF] 
QED

(* names are in precisely one abstract state *)
Theorem out_of_order_lifecycle_pred_exclusive:
 !lc lc' State t.
  out_of_order_lifecycle_pred lc State t ==>
  out_of_order_lifecycle_pred lc' State t ==>
  lc = lc'
Proof
 Cases_on `lc` >> Cases_on `lc'` >>
 Cases_on `State` >> rename1 `State_st I' s Cs Fs` >>
 rw [out_of_order_lifecycle_pred,map_down,map_up]
QED

(* all program names have some abstract state *)
Theorem out_of_order_lifecycle_pred_exists:
 !State t. well_formed_state State ==>
   name_instr_in_State t State ==>
   ?lc. out_of_order_lifecycle_pred lc State t
Proof
 Cases_on `State` >> rename1 `State_st I' s Cs Fs` >>
 rw [name_instr_in_State] >>
 Cases_on `t NOTIN FDOM s` >> fs [] >-
  (Q.EXISTS_TAC `out_of_order_lifecycle_Decoded` >>
   rw [out_of_order_lifecycle_pred,map_up,map_down] >| [
     rw [FLOOKUP_DEF],
     METIS_TAC [wfs_C_SUBSET_FDOM,SUBSET_DEF],
     METIS_TAC [wfs_F_SUBSET_FDOM,SUBSET_DEF]
   ]) >>
 Cases_on `t IN Cs` >-
  (Q.EXISTS_TAC `out_of_order_lifecycle_Committed` >>
   rw [out_of_order_lifecycle_pred,map_down] >-
   rw [FLOOKUP_DEF] >>
   strip_tac >>
   `Cs INTER Fs = {}` by METIS_TAC [well_formed_CF_empty] >>
   fs [INTER_DEF,EXTENSION] >>
   METIS_TAC []) >>
 Cases_on `t IN Fs` >-
  (Q.EXISTS_TAC `out_of_order_lifecycle_Fetched` >>
   rw [out_of_order_lifecycle_pred,map_down,FLOOKUP_DEF]) >>
 Q.EXISTS_TAC `out_of_order_lifecycle_Executed` >>
 rw [out_of_order_lifecycle_pred,map_down,FLOOKUP_DEF] 
QED

(* names added by fetches are all initially in Decoded state *)
Theorem out_of_order_lifecycle_step_initial_decoded:
 !State lb State' t. well_formed_state State ==>
  out_of_order_step State lb State' ==>
  ~name_instr_in_State t State ==>
  name_instr_in_State t State' ==>
  out_of_order_lifecycle_pred out_of_order_lifecycle_Decoded State' t
Proof
 Cases_on `State` >> Cases_on `State'` >>
 rw [name_instr_in_State] >>
 rename1 `out_of_order_step (State_st I1 s1 C1 F1) lb (State_st I2 s2 C2 F2)` >>
 `well_formed_state (State_st I2 s2 C2 F2)`
  by METIS_TAC [well_formed_OoO_transition_well_formed,step_invariant] >>
 rw [out_of_order_lifecycle_pred,map_up,map_down] >| [
   strip_tac >>
   `t IN FDOM s2` by fs [FLOOKUP_DEF] >>
   `t NOTIN FDOM s1` by METIS_TAC [wfs_FDOM_SUBSET_bound_names,SUBSET_DEF] >>
   `FDOM s1 <> FDOM s2` by METIS_TAC [EXTENSION] >>
   `s1 <> s2` by METIS_TAC [fmap_EQ] >>
   Cases_on `lb` >> rename1 `l_lb ob ac t'` >>
   `ac = act_exe` by METIS_TAC [OoO_transition_s_neq_then_exe] >>
   rw [] >>
   `I1 = I2` by fs [out_of_order_step_cases] >>
   rw [] >> fs [],

   strip_tac >>
   `t IN FDOM s2` by METIS_TAC [wfs_C_SUBSET_FDOM,SUBSET_DEF] >>
   `t NOTIN FDOM s1` by METIS_TAC [wfs_FDOM_SUBSET_bound_names,SUBSET_DEF] >>
   `FDOM s1 <> FDOM s2` by METIS_TAC [EXTENSION] >>
   `s1 <> s2` by METIS_TAC [fmap_EQ] >>
   Cases_on `lb` >> rename1 `l_lb ob ac t'` >>
   `ac = act_exe` by METIS_TAC [OoO_transition_s_neq_then_exe] >>
   rw [] >>
   `I1 = I2` by fs [out_of_order_step_cases] >>
   rw [] >> fs [],

   strip_tac >>
   `t IN FDOM s2` by METIS_TAC [wfs_F_SUBSET_FDOM,SUBSET_DEF] >>
   `t NOTIN FDOM s1` by METIS_TAC [wfs_FDOM_SUBSET_bound_names,SUBSET_DEF] >>
   `FDOM s1 <> FDOM s2` by METIS_TAC [EXTENSION] >>
   `s1 <> s2` by METIS_TAC [fmap_EQ] >>
   Cases_on `lb` >> rename1 `l_lb ob ac t'` >>
   `ac = act_exe` by METIS_TAC [OoO_transition_s_neq_then_exe] >>
   rw [] >>
   `I1 = I2` by fs [out_of_order_step_cases] >>
   rw [] >> fs []
 ]
QED

(* the abstract states of non-transition names are unaffected by a transition *)
Theorem out_of_order_lifecycle_simulation_other:
 !State State' lc ob ac t t'. well_formed_state State ==>
  out_of_order_step State (l_lb ob ac t) State' ==>
  t' <> t ==>
  out_of_order_lifecycle_pred lc State t' ==>
  out_of_order_lifecycle_pred lc State' t'
Proof
 Cases_on `State` >> Cases_on `State'` >>
 Cases_on `lc` >> rw [out_of_order_lifecycle_pred] >>
 rename1 `out_of_order_step (State_st I1 s1 C1 F1) (l_lb ob ac t) (State_st I2 s2 C2 F2)` >>
 Cases_on `ac` >> fs [out_of_order_step_cases] >> rw [] >| [
  rw [bound_names_program_union],
  fs [map_up,map_down] >>
  rw [FLOOKUP_DEF,FDOM_FUNION] >>
  strip_tac >>
  METIS_TAC [FLOOKUP_DEF],

  fs [map_down] >>
  Q.EXISTS_TAC `v''` >>
  fs [FLOOKUP_DEF,NOT_EQ_FAPPLY],

  fs [map_down] >>
  Q.EXISTS_TAC `v''` >>
  fs [FLOOKUP_DEF,NOT_EQ_FAPPLY],

  fs [map_down] >>
  Q.EXISTS_TAC `v''` >>
  fs [FLOOKUP_DEF,NOT_EQ_FAPPLY]
 ] 
QED

(* abstract transitions for names are consistent with labeled transitions *)
Theorem out_of_order_lifecycle_simulation_name:
 !State State' ob ac t. well_formed_state State ==>
  out_of_order_step State (l_lb ob ac t) State' ==>
  ?lc lc'. out_of_order_lifecycle_pred lc State t /\
    out_of_order_lifecycle_tr lc ac lc' /\
    out_of_order_lifecycle_pred lc' State' t
Proof
 rw [] >>
 sg `name_instr_in_State t State` >-
  (Cases_on `State` >>
   rw [name_instr_in_State,bound_names_program] >>
   fs [out_of_order_step_cases] >>
   METIS_TAC [bound_name_instr]) >>
 `?lc. out_of_order_lifecycle_pred lc State t`
  by METIS_TAC [out_of_order_lifecycle_pred_exists] >>
 Q.EXISTS_TAC `lc` >> rw [] >>
 Cases_on `State` >> Cases_on `State'` >>
 rename1 `out_of_order_step (State_st I1 s1 C1 F1) (l_lb ob ac t) (State_st I2 s2 C2 F2)` >>
 Cases_on `lc` >| [
   Q.EXISTS_TAC `out_of_order_lifecycle_Executed` >>
   fs [out_of_order_lifecycle_pred,map_up,map_down] >>
   `t NOTIN FDOM s1` by fs [FLOOKUP_DEF] >>
   Cases_on `ac` >>
   fs [out_of_order_step_cases,out_of_order_lifecycle_tr_rules] >-
   rw [FLOOKUP_DEF,FDOM_FUPDATE] >>
   rw [] >> fs [map_down],

   fs [out_of_order_step_cases,out_of_order_lifecycle_pred,map_down,map_up] >>
   rw [] >- METIS_TAC [] >-
    (Q.EXISTS_TAC `out_of_order_lifecycle_Committed` >>
     fs [out_of_order_lifecycle_tr_rules,out_of_order_lifecycle_pred,map_down]) >>
   Q.EXISTS_TAC `out_of_order_lifecycle_Fetched` >>
   fs [out_of_order_lifecycle_tr_rules,out_of_order_lifecycle_pred,map_down],

   fs [out_of_order_lifecycle_pred,map_down] >>
   `t IN FDOM s1` by fs [FLOOKUP_DEF] >>
   fs [out_of_order_step_cases,map_up,map_down] >> rw [] >>
   `?t1 t2 c'. i_assign t c' (o_store res_MEM t1 t2) IN I1`
    by METIS_TAC [wfs_C_exists_store_mem] >>
   `i_assign t c (o_store res_PC t1 t2) = i_assign t c' (o_store res_MEM t1' t2')`
    by METIS_TAC [bound_name_instr,wfs_unique_instr_names] >>
   fs [],

   fs [out_of_order_lifecycle_pred,map_down] >>
   `t IN FDOM s1` by fs [FLOOKUP_DEF] >>
   fs [out_of_order_step_cases,map_up,map_down] >> rw [] >>
   `?t1 t2 c'. i_assign t c' (o_store res_PC t1 t2) IN I1`
    by METIS_TAC [wfs_F_exists_store_pc] >>
   `i_assign t c (o_store res_MEM t1 t2) = i_assign t c' (o_store res_PC t1' t2')`
    by METIS_TAC [bound_name_instr,wfs_unique_instr_names] >>
   fs []
 ]
QED

val _ = export_theory ();
