open HolKernel boolLib Parse bossLib finite_mapTheory pred_setTheory listTheory arithmeticTheory relationTheory ottTheory milUtilityTheory milTheory milSemanticsUtilityTheory milTracesTheory milMetaTheory milPermutationTheory;

(* ================================================= *)
(* MIL transition reordering definitions and results *)
(* ================================================= *)

val _ = new_theory "milReorder";

(* ---------------------- *)
(* Reordering definitions *)
(* ---------------------- *)

Definition same_act_name_l:
 same_act_name_l (l1:l) (l2:l) =
  (act_of_l l1 = act_of_l l2 /\ name_of_l l1 = name_of_l l2)
End

Definition same_act_name_elt:
  same_act_name_elt (e1:'state # l # 'state) (e2:'state # l # 'state) =
  (same_act_name_l (FST (SND e1)) (FST (SND e2)))
End

(* NOTE: "i <= j" should also work. *)
Definition ordered_execution:
 ordered_execution pi =
  (!i j ei ej.
   NTH i pi = SOME ei ==>
   NTH j pi = SOME ej ==>
   i < j ==>
   name_of_l (FST (SND ei)) <= name_of_l (FST (SND ej)))
End

Definition ordered_version:
 ordered_version (pi1:('state # l # 'state) list) (pi2:('state # l # 'state) list) =
  ((FST (HD pi1) = FST (HD pi2)) /\
  (SND (SND (LAST pi1)) = SND (SND (LAST pi2))) /\
  (!a. commits pi1 a = commits pi2 a) /\
  (ordered_execution pi2) /\
  (PERM_REL same_act_name_elt pi1 pi2))
End

(* automation works better with this property wrapped *)
Definition between_name_of_l_gt:
 between_name_of_l_gt pi n i t =
  (!j ej. i <= j /\ j < SUC n ==> NTH j pi = SOME ej ==> name_of_l (FST (SND ej)) > t)
End

Definition incomplete_instrs_State_bound:
 incomplete_instrs_State_bound (State_st I0 s0 C0 F0) t =
 { i | i IN I0 /\ ~(Completed (State_st I0 s0 C0 F0) i) /\ bound_name_instr i <= t }
End

Definition incomplete_names_State_bound:
 incomplete_names_State_bound (State_st I0 s0 C0 F0) t =
  { t' | t' IN bound_names_program I0 /\ ~(Completed_t (State_st I0 s0 C0 F0) t') /\ t' <= t }
End

(* -------------------------- *)
(* Reordering utility results *)
(* -------------------------- *)

(* sanity checking *)
Theorem ordered_version_LENGTH[local]:
 !pi pi'. ordered_version pi pi' ==> LENGTH pi = LENGTH pi'
Proof
 METIS_TAC [ordered_version,PERM_REL_LENGTH]
QED

(* sanity checking *)
Theorem ordered_version_well_formed_state[local]:
 !pi pi'. ordered_version pi pi' ==>
  well_formed_state (FST (HD pi)) ==>
  well_formed_state (FST (HD pi'))
Proof
 fs [ordered_version]
QED

Theorem ordered_version_singleton_refl:
  !e. ordered_version [e] [e]
Proof
 Cases_on `e` >> Cases_on `r` >> fs [ordered_version] >>
 rw [ordered_execution] >-
  (Cases_on `i` >> fs [NTH] >> Cases_on `j` >> fs [NTH]) >>
 `reflexive same_act_name_elt`
  suffices_by METIS_TAC [PERM_REL_reflexive,reflexive_def] >>
 fs [reflexive_def,same_act_name_elt,same_act_name_l]
QED

Theorem equivalence_same_act_name_elt:
 equivalence same_act_name_elt
Proof
 fs [equivalence_def,transitive_def,symmetric_def,reflexive_def,same_act_name_elt,same_act_name_l] >>
 rw [] >> EQ_TAC >> rw []
QED

Theorem ordered_execution_nth_rel_le:
 !n n' i pi pi' sa sa' sb sb' si si' ob ob' a a' li.
  n' < n ==>
  ordered_execution (pi ++ [(sa,l_lb ob a n,sa')]) ==>
  NTH i pi' = SOME (si,li,si') ==>
  PERM_REL same_act_name_elt (pi ++ [(sb,l_lb ob' a' n',sb')]) pi' ==>
  name_of_l li <= n
Proof
 rw [] >> Cases_on `li` >> rw [name_of_l] >>
 fs [ordered_execution] >>
 sg `!k ek. NTH k pi = SOME ek ==> name_of_l (FST (SND ek)) <= n` >-
  (rw [] >>
   `name_of_l (FST (SND ek)) <= name_of_l (FST (SND (sa,l_lb ob a n,sa')))` 
    suffices_by fs [name_of_l] >>
   `NTH k pi <> NONE` by fs [] >>
   `k < LENGTH pi` by METIS_TAC [NTH_SOME] >>
   `NTH (LENGTH pi) (pi ++ [(sa,l_lb ob a n,sa')]) = SOME (sa,l_lb ob a n,sa')` by fs [NTH_app2,NTH] >>
   `NTH k (pi ++ [(sa,l_lb ob a n,sa')]) = SOME ek` by METIS_TAC [NTH_app1] >>
   METIS_TAC []) >>
 sg `!e. MEM e pi ==> name_of_l (FST (SND e)) <= n` >-
  (rw [] >> `?k'. NTH k' pi = SOME e` by METIS_TAC [MEM_NTH] >> METIS_TAC []) >>
 sg `!e. MEM_REL same_act_name_elt e (pi ++ [(sb,l_lb ob' a' n',sb')]) ==> name_of_l (FST (SND e)) <= n` >-
  (rw [] >>
   `MEM_REL same_act_name_elt e pi \/
    MEM_REL same_act_name_elt e [(sb,l_lb ob' a' n',sb')]` by METIS_TAC [MEM_REL_app] >-
   (`?e'. same_act_name_elt e e' /\ MEM e' pi` by METIS_TAC [MEM_REL_alt_left] >>
    `name_of_l (FST (SND e')) <= n` by METIS_TAC [] >>
    fs [same_act_name_elt,same_act_name_l]) >>
   `?y. same_act_name_elt e y /\ MEM y [(sb,l_lb ob' a' n',sb')]` by METIS_TAC [MEM_REL_alt_left] >>
   fs [] >> rw [] >> fs [same_act_name_elt,same_act_name_l,name_of_l]) >>
 `!e. MEM_REL same_act_name_elt e pi' ==> name_of_l (FST (SND e)) <= n`
  by METIS_TAC [equivalence_same_act_name_elt,PERM_REL_LIST_MEM_REL,LIST_MEM_REL] >>
 `MEM (si,l_lb o' a'' n'',si') pi'` by METIS_TAC [NTH_MEM] >>
 `MEM_REL same_act_name_elt (si,l_lb o' a'' n'',si') pi'`
  by METIS_TAC [equivalence_same_act_name_elt,equivalence_def,reflexive_def,MEM_REL_alt_right] >>
 `name_of_l (FST (SND (si,l_lb o' a'' n'',si'))) <= n` by fs [] >>
 fs [name_of_l]
QED

Theorem act_cmt_neq[local]:
 !al1 al2.
 (!a. (?v. al2 = act_cmt a v) ==> ~(?v. al1 = act_cmt a v)) <=>
 (!a v. al2 = act_cmt a v ==> !v'. al1 <> act_cmt a v')
Proof
 rw [] >> EQ_TAC >> fs []
QED

Theorem act_cmt_commits_swap_eq:
 !act1 act2 a s1 s2 s3 s4 s5 s6 s7 s8 ob1 ob2 ob3 ob4 n1 n2 n3 n4.
  (!a0. (?v. act1 = act_cmt a0 v) ==> !v'. act2 <> act_cmt a0 v') ==>
  commits [(s1,l_lb ob1 act2 n1,s2);(s3,l_lb ob2 act1 n2,s4)] a =
  commits [(s5,l_lb ob3 act1 n3,s6);(s7,l_lb ob4 act2 n4,s8)] a
Proof
 rw [] >> Cases_on `act1` >> Cases_on `act2` >> rw [commits]
QED

Theorem name_instr_in_State_step_invariant:
 !t. step_invariant out_of_order_step (name_instr_in_State t)
Proof
 rw [step_invariant] >>
 Cases_on `s` >> rename1 `State_st I0 s0 C0 F0` >>
 Cases_on `l` >> rename1 `l_lb ob ac t'` >>
 Cases_on `s'` >> rename1 `State_st I1 s1 C1 F1` >>
 fs [name_instr_in_State,bound_names_program] >>
 Cases_on `i` >> rename1 `i_assign n e mop` >>
 fs [bound_name_instr] >> rw [] >>
 Q.EXISTS_TAC `i_assign n e mop` >> rw [bound_name_instr] >>
 METIS_TAC [OoO_transition_monotonicity_I_C_F,SUBSET_DEF]
QED

Theorem name_instr_in_State_LTC_invariant:
 !t. LTC_invariant out_of_order_step (name_instr_in_State t)
Proof
 METIS_TAC [name_instr_in_State_step_invariant,step_invariant_LTC_invariant]
QED

Theorem OoO_instr_in_fst_in_last:
 !pi. step_execution out_of_order_step pi ==>
  !t. name_instr_in_State t (FST (HD pi)) ==>
  name_instr_in_State t (SND (SND (LAST pi)))
Proof
 rw [] >>
 `pi <> []` by METIS_TAC [step_execution_not_empty_list] >>
 Cases_on `pi` >> rw [] >>
 Cases_on `h` >> Cases_on `r` >> rename1 `(s1,l1,s2)` >>
 sg `?s3 l2 s4. LAST ((s1,l1,s2)::t') = (s3,l2,s4)` >-
  (`t' = [] \/ ?x l. t' = SNOC x l` by METIS_TAC [SNOC_CASES] >> rw [] >>
   Cases_on `x` >> Cases_on `r` >> rw [LAST_DEF]) >>
 fs [] >>
 `LTC out_of_order_step s1 s4` by METIS_TAC [step_execution_LTC] >>
 METIS_TAC [name_instr_in_State_LTC_invariant,LTC_invariant]
QED

Theorem well_formed_state_gt_max_name_not_mapped[local]:
 !S. well_formed_state S ==>
 !t. t > max_name_in_State S ==>
 ~(name_mapped_in_State t S)
Proof
 rw [] >> Cases_on `S'` >>
 rename1 `State_st I0 s0 C0 F0` >>
 fs [max_name_in_State,name_mapped_in_State] >>
 `FINITE (bound_names_program I0)`
  by METIS_TAC [well_formed_state,finite_bound_names_program] >>
 `t IN FDOM s0 ==> F` suffices_by METIS_TAC [] >>
 STRIP_TAC >>
 `t IN bound_names_program I0` by METIS_TAC [SUBSET_DEF,well_formed_state] >>
 `t <= MAX_SET (bound_names_program I0)` suffices_by DECIDE_TAC >>
 `bound_names_program I0 <> {}` by METIS_TAC [MEMBER_NOT_EMPTY] >>
 METIS_TAC [MAX_SET_DEF]
QED

Theorem well_formed_incomplete_instrs_eq_incomplete_names[local]:
 !State t. well_formed_state State ==>
  bound_names_program (incomplete_instrs_State_bound State t) =
  incomplete_names_State_bound State t
Proof
 rw [] >> Cases_on `State` >>
 rename1 `State_st I0 s0 C0 F0` >>
 rw [
  incomplete_instrs_State_bound,
  incomplete_names_State_bound,
  bound_names_program,
  Completed_t,
  EXTENSION
 ] >> EQ_TAC >> rw [] >| [
   METIS_TAC [],
   Cases_on `i' IN I0` >> rw [] >>
   `i = i'` suffices_by METIS_TAC [] >>
   METIS_TAC [wfs_unique_instr_names],
   rw [],
   Q.PAT_X_ASSUM `!i'. P` (STRIP_ASSUME_TAC o Q.SPEC `i`) >>
   rw [] >> Q.EXISTS_TAC `i` >> rw []
 ]
QED

(* FIXME: use incomplete_names_State_bound *)
Theorem well_formed_not_all_completed_exists_least[local]:
 !State. well_formed_state State ==>
  !t. name_instr_in_State t State /\ ~(Completed_t State t) ==>
  ?t'. name_instr_in_State t' State /\ ~(Completed_t State t') /\
   !t''. name_instr_in_State t'' State /\ t'' < t' ==> Completed_t State t''
Proof
 rw [] >>
 Cases_on `State` >> rename1 `State_st I0 s0 C0 F0` >>
 fs [name_instr_in_State] >>
 Q.ABBREV_TAC `cpl = {t0 | t0 IN bound_names_program I0 /\
  ~(Completed_t (State_st I0 s0 C0 F0) t0)}` >>
 `t IN cpl` by fs [Abbr `cpl`] >>
 `cpl <> {}` by METIS_TAC [MEMBER_NOT_EMPTY] >>
 Q.EXISTS_TAC `MIN_SET cpl` >> rw [] >| [
   fs [IN_DEF] >> MATCH_MP_TAC MIN_SET_ELIM >>
   rw [] >> fs [Abbr `cpl`],
   Q.ABBREV_TAC `P = \x. ~Completed_t (State_st I0 s0 C0 F0) x` >>
   `P (MIN_SET cpl)` suffices_by METIS_TAC [] >>
   MATCH_MP_TAC MIN_SET_ELIM >> fs [Abbr `P`] >>
   rw [] >> fs [Abbr `cpl`],
   Cases_on `Completed_t (State_st I0 s0 C0 F0) t''` >> rw [] >>
   `MIN_SET cpl <= t''` suffices_by DECIDE_TAC >>
   `t'' IN cpl` suffices_by METIS_TAC [MIN_SET_LEM] >>
   fs [Abbr `cpl`]
 ]
QED

(* FIXME: maybe better to address inside out_of_order_exists_reordering proof *)
Theorem OoO_transitions_exist_cases[local]:
 !I0 s0 C0 F0 obs1 al1 t1 I1 s1 C1 F1 obs2 al2 t2 I2 s2 C2 F2.
  well_formed_state (State_st I0 s0 C0 F0) ==>
  out_of_order_step (State_st I0 s0 C0 F0) (l_lb obs1 al1 t1) (State_st I1 s1 C1 F1) ==>
  out_of_order_step (State_st I1 s1 C1 F1) (l_lb obs2 al2 t2) (State_st I2 s2 C2 F2) ==>
  t2 < t1 ==>
   ?I' s' C' F' obs2' obs1'.
   out_of_order_step (State_st I0 s0 C0 F0) (l_lb obs2' al2 t2) (State_st I' s' C' F') /\
   out_of_order_step (State_st I' s' C' F') (l_lb obs1' al1 t1) (State_st I2 s2 C2 F2) /\
   (!a. (?v. al2 = act_cmt a v) ==> ~(?v. al1 = act_cmt a v))
Proof
 rw [] >>
 MP_TAC (Q.SPECL [
   `State_st I0 s0 C0 F0`,
   `obs1`,`al1`,`t1`,
   `State_st I1 s1 C1 F1`,
   `obs2`,`al2`,`t2`,
   `State_st I2 s2 C2 F2`
  ] OoO_transitions_exist) >>
 rw [] >>
 Cases_on `State'` >>
 METIS_TAC []
QED

(* --------------------- *)
(* Reordering metatheory *)
(* --------------------- *)

Theorem out_of_order_exists_reordering:
 !pi. step_execution out_of_order_step pi ==>
  well_formed_state (FST (HD pi)) ==>
  ?pi'. ordered_version pi pi' /\ step_execution out_of_order_step pi'
Proof
 `!n pi. LENGTH pi = n ==>
   step_execution out_of_order_step pi ==>
   well_formed_state (FST (HD pi)) ==>
   ?pi'. ordered_version pi pi' /\ step_execution out_of_order_step pi'` suffices_by METIS_TAC [] >>
 HO_MATCH_MP_TAC COMPLETE_INDUCTION >> rw [] >>
 Cases_on `LENGTH pi` >-
 (fs [LENGTH_NIL] >> METIS_TAC [step_execution_not_empty_list]) >>
 Cases_on `n` >-
 (Cases_on `pi` >> fs [SING_HD] >>
  Q.EXISTS_TAC `[h]` >> rw [] >>
  METIS_TAC [ordered_version_singleton_refl]) >>
 sg `?pi1 e1 e2. pi = pi1 ++ [e1;e2] /\ LENGTH pi1 = n'` >-
  (`?pi11 e. pi = pi11 ++ [e] /\ LENGTH pi11 = SUC n'`
    by METIS_TAC [LENGTH_SUC_split] >>
   `?pi12 e'. pi11 = pi12 ++ [e'] /\ LENGTH pi12 = n'`
    by METIS_TAC [LENGTH_SUC_split] >>
    rw []) >>
 `LENGTH (pi1 ++ [e1]) = SUC n'` by fs [] >>
 sg `step_execution out_of_order_step (pi1 ++ [e1])` >-
   (`pi1 ++ [e1] <> []` by fs [] >>
    rw [] >> `pi1 ++ [e1;e2] = (pi1 ++ [e1]) ++ [e2]` by fs [] >>
    `step_execution out_of_order_step ((pi1 ++ [e1]) ++ [e2])` by METIS_TAC [] >>
    Cases_on `e2` >> Cases_on `r` >>
    METIS_TAC [step_execution_reduce_one]) >>
 `well_formed_state (FST (HD (pi1 ++ [e1])))` by (Cases_on `pi1` >> fs []) >>
 `SUC n' < SUC (SUC n')` by rw [] >>
 `?pi'. ordered_version (pi1 ++ [e1]) pi' /\ step_execution out_of_order_step pi'`
  by METIS_TAC [] >>
 `LENGTH pi' = SUC n'` by METIS_TAC [ordered_version_LENGTH] >>
 `?pi1' e1'. pi' = pi1' ++ [e1']`  by METIS_TAC [LENGTH_SUC_split] >>
 `SND (SND e1) = SND (SND e1')` by fs [ordered_version] >>
 sg `SND (SND e1') = FST e2` >-
  (`SND (SND e1) = FST e2` suffices_by fs [] >>
   Cases_on `e1` >> Cases_on `r` >>
   Cases_on `e2` >> Cases_on `r` >>
   `r' = q''` suffices_by fs [] >>
   METIS_TAC [step_execution_append_eq_state_base]) >>
 Cases_on `name_of_l (FST (SND e1')) <= name_of_l (FST (SND e2))` >-
  (sg `step_execution out_of_order_step (pi' ++ [e2])` >-
    (Cases_on `e2` >> Cases_on `r` >>
     `SND (SND (LAST pi')) = q` by fs [] >>
     `out_of_order_step q q' r'` suffices_by METIS_TAC [step_execution_append_one] >>
     `pi1 ++ [e1] <> []` by fs [] >>
     `pi1 ++ [e1;(q,q',r')] = (pi1 ++ [e1]) ++ [(q,q',r')]` by fs [] >>
     METIS_TAC [step_execution_reduce_one]) >>
   sg `ordered_version pi (pi' ++ [e2])` >-
    (rw [ordered_version] >| [
      `FST (HD (pi1 ++ [e1;e2])) = FST (HD (pi1 ++ [e1]))` by (Cases_on `pi1` >> fs []) >>
      `FST (HD (pi1' ++ [e1'])) = FST (HD (pi1' ++ [e1'] ++ [e2]))` by (Cases_on `pi1'` >> fs []) >>
      METIS_TAC [ordered_version],

      `pi1 ++ [e1; e2] = pi1 ++ [e1] ++ [e2]` by fs [] >>
      `pi1' ++ [e1'; e2] = pi1' ++ [e1'] ++ [e2]` by fs [] >>
      METIS_TAC [commits_app,ordered_version],

      `ordered_execution (pi1' ++ [e1'])` by fs [ordered_version] >>
      rw [ordered_execution] >>
      `LENGTH (pi1' ++ [e1'] ++ [e2]) = SUC (SUC (LENGTH pi1'))` by fs [] >>
       `NTH j (pi1' ++ [e1'] ++ [e2]) <> NONE` by fs [] >>
      `j < SUC (SUC (LENGTH pi1'))` by METIS_TAC [NTH_SOME] >>
      `j < LENGTH (pi1' ++ [e1'] ++ [e2])` by METIS_TAC [NTH_SOME] >>
      Cases_on `j < SUC (LENGTH pi1')` >-
       (`j < LENGTH (pi1' ++ [e1'])` by fs [] >>
        `NTH j ((pi1' ++ [e1']) ++ [e2]) = NTH j (pi1' ++ [e1'])` by fs [NTH_app1] >>
        `i < LENGTH (pi1' ++ [e1'])` by DECIDE_TAC >>
        `NTH i ((pi1' ++ [e1']) ++ [e2]) = NTH i (pi1' ++ [e1'])` by fs [NTH_app1] >>
        METIS_TAC [ordered_execution]) >>
      `j = SUC (LENGTH pi1')` by DECIDE_TAC >>
      sg `ej = e2` >-
       (`NTH j (pi1' ++ [e1'] ++ [e2]) = SOME e2` suffices_by fs [NTH] >>
        rw [] >> fs [NTH_app2] >>
        `SUC (LENGTH pi1') - (LENGTH pi1' + 1) = 0` by DECIDE_TAC >> 
        `NTH 0 [e2] = SOME ej` by METIS_TAC [] >> fs [NTH]) >>
      `i = LENGTH pi1' \/ i < LENGTH pi1'` by DECIDE_TAC >-
       (`ei = e1'` suffices_by rw [] >>
        `NTH (LENGTH pi1') (pi1' ++ ([e1'] ++ [e2])) = SOME e1'` suffices_by fs [] >>
        fs [NTH_app2,NTH]) >>
      `NTH i (pi1' ++ [e1']) = SOME ei` by fs [NTH_app1] >>
      `name_of_l (FST (SND ei)) <= name_of_l (FST (SND e1'))` suffices_by fs [] >>
      `NTH (LENGTH pi1') (pi1' ++ [e1']) = SOME e1'` by fs [NTH_app2,NTH] >>
      METIS_TAC [ordered_execution],

      `PERM_REL same_act_name_elt (pi1 ++ [e1]) (pi1' ++ [e1'])` by fs [ordered_version] >>
      `pi1 ++ [e1; e2] = (pi1 ++ [e1]) ++ [e2]` by fs [] >>
      rw [] >>
      METIS_TAC [PERM_REL_app_tail,equivalence_same_act_name_elt]
     ]) >>
   Q.EXISTS_TAC `pi' ++ [e2]` >>
   METIS_TAC []) >>
 `name_of_l (FST (SND e2)) < name_of_l (FST (SND e1'))` by DECIDE_TAC >>
 (* setup for applying step reordering lemma *)
 `well_formed_state (FST (HD (pi1' ++ [e1'])))`
  by METIS_TAC [ordered_version_well_formed_state] >>
 sg `well_formed_state (FST e1')` >-
  (Cases_on `pi1'` >> fs [] >>
   Cases_on `h` >> Cases_on `r` >>
   `(q,q',r')::(t ++ [e1']) = (q,q',r')::t ++ [e1']` by fs [] >>
   Cases_on `e1'` >> Cases_on `r` >>
   `well_formed_state q''` suffices_by fs [] >>
   `step_execution out_of_order_step ((q,q',r')::t ++ [(q'',q''',r'')])` by fs [] >>
   `well_formed_state q` by fs [] >>
   METIS_TAC [well_formed_OoO_LTC_invariant,step_execution_mid_FST_LTC_invariant]) >>
 sg `out_of_order_step (FST e1') (FST (SND e1')) (SND (SND e1'))` >-
  (Cases_on `e1'` >> Cases_on `r` >>
   `out_of_order_step q q' r'` suffices_by fs [] >>
   Cases_on `pi1'` >- (fs [] >> rw [] >> METIS_TAC [step_execution_singleton]) >>
   fs [] >> rw [] >>
   `h::t <> []` by fs [] >>
   `h::(t ++ [(q,q',FST e2)]) = h::t ++ [(q,q',FST e2)]` by fs [] >>
   METIS_TAC [step_execution_reduce_one]) >>
 sg `out_of_order_step (SND (SND e1')) (FST (SND e2)) (SND (SND e2))` >-
  (Cases_on `e2` >> Cases_on `r` >>
   `out_of_order_step q q' r'` suffices_by fs [] >>
   `pi = (pi1 ++ [e1]) ++ [(q,q',r')]` by fs [] >>
   `pi1 ++ [e1] <> []` by (Cases_on `pi1` >> fs []) >>
   METIS_TAC [step_execution_reduce_one]) >>
 sg `?s'' l1 l2.
  out_of_order_step (FST e1') l1 s'' /\
  out_of_order_step s'' l2 (SND (SND e2)) /\
  same_act_name_l (FST (SND e1')) l2 /\
  same_act_name_l (FST (SND e2)) l1 /\
  (!a. (?v. act_of_l l1 = act_cmt a v) ==> ~(?v. act_of_l l2 = act_cmt a v))` >-
  (Cases_on `e1'` >> Cases_on `r` >>
   Cases_on `e2` >> Cases_on `r` >> 
   Cases_on `e1` >> Cases_on `r` >> fs [] >> rw [] >>
   Cases_on `q'` >> Cases_on `q'''` >>
   rw [same_act_name_l,act_of_l] >>
   fs [name_of_l] >>
   Cases_on `q` >> Cases_on `r''` >> Cases_on `q''` >>
   `?I' s' C' F' obs2' obs1'.
     out_of_order_step (State_st f f0 f1 f2) (l_lb obs2' a' n'') (State_st I' s' C' F') /\
     out_of_order_step (State_st I' s' C' F') (l_lb obs1' a n) (State_st f' f0' f1' f2') /\
     (!a0. (?v. a' = act_cmt a0 v) ==> ~(?v. a = act_cmt a0 v))`
    suffices_by METIS_TAC [name_of_l,act_of_l] >>
   METIS_TAC [OoO_transitions_exist_cases]) >>
 sg `step_execution out_of_order_step (pi1' ++ [(FST e1', l1, s'')])` >-
  (`pi1' = [] \/ ?e pi1''. pi1' = SNOC e pi1''` by rw [SNOC_CASES] >-
  (fs [] >> METIS_TAC [step_execution_rules]) >>
  `pi1' = pi1'' ++ [e]` by fs [] >>
  Cases_on `e` >> Cases_on `r` >>
  Cases_on `e1'` >> Cases_on `r` >> fs [] >>
  `r' = q''` by METIS_TAC [step_execution_append_eq_state_base] >>
  rw [] >>
  `SND (SND (LAST (pi1'' ++ [(q,q',q'')]))) = q''` by fs [] >>
  `step_execution out_of_order_step (pi1'' ++ [(q,q',q'')])`
   suffices_by METIS_TAC [step_execution_append_one] >>
  METIS_TAC [step_execution_rest]) >>
 sg `LENGTH (pi1' ++ [(FST e1',l1,s'')]) = SUC n'` >-
  (rw [LENGTH_APPEND] >> fs []) >>
 sg `well_formed_state (FST (HD (pi1' ++ [(FST e1',l1,s'')])))` >-
  (Cases_on `pi1'` >> fs []) >>
 sg `?pi''. ordered_version (pi1' ++ [(FST e1',l1,s'')]) pi'' /\ 
   step_execution out_of_order_step pi''` >-
  (`SUC n' < SUC (SUC n')` by DECIDE_TAC >> METIS_TAC []) >>
 sg `FST (HD pi) = FST (HD (pi'' ++ [(s'',l2,SND (SND e2))]))` >-
  (fs [ordered_version] >> rw [HD_APPEND] >>
   `FST (HD (pi1' ++ [e1'])) = FST (HD (pi1' ++ [(FST e1',l1,SND (SND (LAST pi'')))]))` by rw [FST_HD_tuple] >>
   `FST (HD pi'') = FST (HD (pi'' ++ [(SND (SND (LAST pi'')),l2,SND (SND e2))]))` suffices_by rw [] >>
   `pi'' <> []` by METIS_TAC [step_execution_not_empty_list] >>
   Cases_on `pi''` >> rw []) >>
 `SND (SND (LAST pi)) = SND (SND (LAST (pi'' ++ [(s'',l2,SND (SND e2))])))` by fs [] >>
 sg `!a. commits pi a = commits (pi'' ++ [(s'',l2,SND (SND e2))]) a` >-
  (fs [ordered_version] >> rw [commits_app] >>
   `commits (pi1 ++ [e1]) a = commits pi1' a ++ commits [e1'] a` by METIS_TAC [commits_app] >>
   `[e1;e2] = [e1] ++ [e2]` by fs [] >>
   `commits [e1;e2] a = commits ([e1] ++ [e2]) a` by fs [] >>
   `commits [e1;e2] a = commits [e1] a ++ commits [e2] a` by METIS_TAC [commits_app] >>
   `commits pi1 a ++ commits [e1; e2] a = commits pi1' a ++ commits [e1'] a ++ commits [e2] a` by fs [commits_app] >>
   `commits pi'' a = commits pi1' a ++ commits [(FST e1',l1,SND (SND (LAST pi'')))] a` by METIS_TAC [commits_app] >>
   Cases_on `e1'` >> Cases_on `r` >> Cases_on `q'` >>
   Cases_on `e2` >> Cases_on `r` >> Cases_on `q''` >>
   Cases_on `l1` >> Cases_on `l2` >> fs [same_act_name_l,name_of_l,act_of_l] >>
   rw [] >>
   `[(q,l_lb o' a' n,SND (SND e1))] ++ [(SND (SND e1),l_lb o'' a'' n'',r'')] =
    [(q,l_lb o' a' n,SND (SND e1));(SND (SND e1),l_lb o'' a'' n'',r'')]` by fs [] >>
   `commits [(q,l_lb o' a' n,SND (SND e1))] a ++ commits [(SND (SND e1),l_lb o'' a'' n'',r'')] a =
    commits [(q,l_lb o' a' n,SND (SND e1));(SND (SND e1),l_lb o'' a'' n'',r'')] a` by METIS_TAC [commits_app] >>
   `[(q,l_lb o''' a'' n'',SND (SND (LAST pi'')))] ++ [(SND (SND (LAST pi'')),l_lb o'''' a' n,r'')] =
    [(q,l_lb o''' a'' n'',SND (SND (LAST pi'')));(SND (SND (LAST pi'')),l_lb o'''' a' n,r'')]` by fs [] >>
   `commits [(q,l_lb o''' a'' n'',SND (SND (LAST pi'')))] a ++ commits [(SND (SND (LAST pi'')),l_lb o'''' a' n,r'')] a =
    commits [(q,l_lb o''' a'' n'',SND (SND (LAST pi'')));(SND (SND (LAST pi'')),l_lb o'''' a' n,r'')] a` by METIS_TAC [commits_app] >>
   METIS_TAC [act_cmt_commits_swap_eq]) >>
 sg `ordered_execution (pi'' ++ [(s'',l2,SND (SND e2))])` >-
  (rw [ordered_execution] >>
   `j < LENGTH pi'' \/ j >= LENGTH pi''` by DECIDE_TAC >-
     (`i < LENGTH pi''` by DECIDE_TAC >>
      `NTH i pi'' = SOME ei` by METIS_TAC [NTH_app1] >>
      `NTH j pi'' = SOME ej` by METIS_TAC [NTH_app1] >>
      METIS_TAC [ordered_version,ordered_execution]) >>
   `LENGTH (pi'' ++ [(s'',l2,SND (SND e2))]) = SUC (LENGTH pi'')` by fs [] >>
   `NTH j (pi'' ++ [(s'',l2,SND (SND e2))]) <> NONE` by rw [] >>
   `j < LENGTH (pi'' ++ [(s'',l2,SND (SND e2))])` by fs [NTH_SOME] >>
   `j = LENGTH pi''` by DECIDE_TAC >> rw [] >>
   `i < LENGTH (pi'' ++ [(s'',l2,SND (SND e2))])` by fs [] >>
   `NTH i (pi'' ++ [(s'',l2,SND (SND e2))]) = SOME ei` by METIS_TAC [NTH_app1] >>
   `NTH (LENGTH pi'') (pi'' ++ [(s'',l2,SND (SND e2))]) = SOME (s'',l2,SND (SND e2))` by fs [NTH_app2,NTH] >>
   `ej = (s'',l2,SND (SND e2))` by fs [] >> rw [] >>
   Cases_on `e1'` >> Cases_on `r` >> fs [] >>
   Cases_on `e2` >> Cases_on `r` >> fs [] >>
   Cases_on `q'` >> Cases_on `q'''` >> fs [same_act_name_l] >>
   Cases_on `l1` >> Cases_on `l2` >> fs [act_of_l,name_of_l] >> rw [] >>
   `NTH i pi'' = SOME ei` by METIS_TAC [NTH_app1] >>
   `ordered_execution (pi1' ++ [(q,l_lb o' a n,SND (SND e1))])` by fs [ordered_version] >>
   `PERM_REL same_act_name_elt (pi1' ++ [(q,l_lb o''' a' n',s'')]) pi''` by fs [ordered_version] >>
   Cases_on `ei` >> Cases_on `r` >> rw [] >>
   METIS_TAC [ordered_execution_nth_rel_le]) >>
 sg `PERM_REL same_act_name_elt pi (pi'' ++ [(s'',l2,SND (SND e2))])` >-
  (`PERM_REL same_act_name_elt (pi1 ++ [e1]) pi'` by fs [ordered_version] >>
   `PERM_REL same_act_name_elt (pi1' ++ [(FST e1',l1,s'')]) pi''` by fs [ordered_version] >>
   rw [] >>
   sg `PERM_REL same_act_name_elt (pi1 ++ [e1;e2]) (pi1' ++ [e1'] ++ [e2])` >-
    (`pi1 ++ [e1;e2] = pi1 ++ [e1] ++ [e2]` by fs [] >>
     rw [] >>
     METIS_TAC [PERM_REL_app_tail,equivalence_same_act_name_elt]) >>
   sg `PERM_REL same_act_name_elt (pi1' ++ [e1'] ++ [e2]) (pi1' ++ [e1';e2])` >-
    (`pi1' ++ [e1'] ++ [e2] = pi1' ++ [e1';e2]` by fs [] >> rw [] >>
     METIS_TAC [equivalence_same_act_name_elt,equivalence_def,PERM_REL_reflexive,reflexive_def]) >>
   sg `PERM_REL same_act_name_elt (pi1' ++ [e1';e2]) (pi1' ++ [(FST e1',l1,s'');(s'',l2,SND (SND e2))])` >-
    (`same_act_name_elt e1' (s'',l2,SND (SND e2)) /\ same_act_name_elt e2 (FST e1',l1,s'')`
      suffices_by METIS_TAC [PERM_REL_append_two_swap,equivalence_same_act_name_elt] >>
      fs [same_act_name_elt]) >>
   sg `PERM_REL same_act_name_elt (pi1' ++ [(FST e1',l1,s'');(s'',l2,SND (SND e2))])
    (pi1' ++ [(FST e1',l1,s'')] ++ [(s'',l2,SND (SND e2))])` >-
    (`pi1' ++ [(FST e1',l1,s'');(s'',l2,SND (SND e2))] = pi1' ++ [(FST e1',l1,s'')] ++ [(s'',l2,SND (SND e2))]` by fs [] >>
     METIS_TAC [equivalence_same_act_name_elt,equivalence_def,PERM_REL_reflexive,reflexive_def]) >>
   `PERM_REL same_act_name_elt (pi1' ++ [(FST e1',l1,s'')] ++ [(s'',l2,SND (SND e2))]) (pi'' ++ [(s'',l2,SND (SND e2))])`
    by METIS_TAC [PERM_REL_REL_append_one,equivalence_def,reflexive_def,equivalence_same_act_name_elt] >>
   METIS_TAC [PERM_REL_transitive,transitive_def]) >>
 sg `step_execution out_of_order_step (pi'' ++ [(s'',l2,SND (SND e2))])` >-
  (`SND (SND (LAST pi'')) = s''` suffices_by METIS_TAC [step_execution_append_one] >>
   fs [ordered_version]) >>
 Q.EXISTS_TAC `pi'' ++ [(s'',l2,SND (SND e2))]` >>
 METIS_TAC [ordered_version]
QED

(* FIXME: more intuitive to write j <= n? *)
(* "Complete consistent lemma A1" *)
Theorem out_of_order_complete_consistent:
 !pi. step_execution out_of_order_step pi ==>
  well_formed_state (FST (HD pi)) ==>
  !n i t ei en.
   LENGTH pi = SUC n ==>
   between_name_of_l_gt pi n i t ==>
   NTH i pi = SOME ei ==>
   NTH n pi = SOME en ==>
   Completed_t (SND (SND en)) t ==>
   Completed_t (SND (SND ei)) t
Proof
 STRIP_TAC >> STRIP_TAC >>
 STRIP_TAC >> STRIP_TAC >>
 Induct_on `SUC n - i` >> rw [] >-
  (`i < SUC n` suffices_by DECIDE_TAC >>
   `NTH i pi <> NONE` by fs [] >>
   METIS_TAC [NTH_SOME]) >>
 `i < SUC n` by (`NTH i pi <> NONE` by fs [] >> METIS_TAC [NTH_SOME]) >>
 `v = n - i` by DECIDE_TAC >>
 Cases_on `v` >> rw [] >-
  (fs [] >> `n = i` by DECIDE_TAC >>
   rw [] >> `ei = en` by fs [] >> rw []) >>
 `SUC n' = SUC n - SUC i` by DECIDE_TAC >>
 `SUC i < SUC n` by DECIDE_TAC >>
 sg `!j ej. SUC i <= j /\ j < SUC n ==> NTH j pi = SOME ej ==> name_of_l (FST (SND ej)) > t` >-
  (rw [] >> `i <= j /\ j < SUC n` by DECIDE_TAC >> METIS_TAC [between_name_of_l_gt]) >>
 Cases_on `NTH (SUC i) pi` >- METIS_TAC [NTH_SOME] >>
 `Completed_t (SND (SND x)) t` by METIS_TAC [between_name_of_l_gt] >>
 `i <= SUC i /\ SUC i < SUC n` by DECIDE_TAC >>
 `name_of_l (FST (SND x)) > t` by METIS_TAC [between_name_of_l_gt] >>
 `?pi1 pi2. pi = pi1 ++ [ei;x] ++ pi2` by METIS_TAC [NTH_SUC_mid] >>
 Cases_on `ei` >> Cases_on `r` >>
 Cases_on `x` >> Cases_on `r` >>
 rename1 `[(s1,l1,s1');(s2,l2,s2')]` >>
 `s1' = s2` by METIS_TAC [step_execution_append_eq_state] >>
 fs [] >> rw [] >>
 sg `out_of_order_step s1 l1 s1'` >-
  (`pi1 ++ [(s1,l1,s1'); (s1',l2,s2')] ++ pi2 =
    pi1 ++ (s1,l1,s1')::(s1',l2,s2')::pi2` by fs [] >>
   METIS_TAC [step_execution_mid]) >>
 sg `out_of_order_step s1' l2 s2'` >-
  (`pi1 ++ [(s1,l1,s1'); (s1',l2,s2')] ++ pi2 =
   (pi1 ++ [(s1,l1,s1')]) ++ (s1',l2,s2')::pi2` by fs [] >>
   METIS_TAC [step_execution_mid]) >>
 sg `well_formed_state s1` >-
  (Cases_on `pi1` >> fs [] >>
   Cases_on `h` >> Cases_on `r` >> fs [] >>
   `(q,q',r')::(t' ++ [(s1,l1,s1'); (s1',l2,s2')] ++ pi2) =
    (q,q',r')::t' ++ (s1,l1,s1')::(s1',l2,s2')::pi2` by fs [] >>
   METIS_TAC [well_formed_OoO_LTC_invariant,step_execution_mid_FST_LTC_invariant]) >>
 `well_formed_state s1'` by METIS_TAC [well_formed_OoO_transition_well_formed,step_invariant] >>
 `well_formed_state s2'` by METIS_TAC [well_formed_OoO_transition_well_formed,step_invariant] >>
 `?I' s' C' F'. s2' = State_st I' s' C' F'` by (Cases_on `s2'` >> rw []) >>
 `?I0 s0 C0 F0. s1' = State_st I0 s0 C0 F0` by (Cases_on `s1'` >> rw []) >>
 fs [Completed_t] >> rw [] >>
 Q.EXISTS_TAC `i'` >> rw [] >-
  (Cases_on `i'` >> Cases_on `l2` >>
   METIS_TAC [OoO_instr_in_after_in_before,name_of_l,bound_name_instr]) >>
 Cases_on `i'` >> rename1 `(i_assign t c mop)` >>
 Cases_on `l2` >> fs [name_of_l,bound_name_instr] >>
 METIS_TAC [OoO_completed_after_completed_before]
QED

(* "Execution lemma A2" *)
Theorem out_of_order_execution_result:
 !pi. step_execution out_of_order_step pi ==>
  well_formed_state (FST (HD pi)) ==>
  ordered_execution pi ==>
  !n i en ei tmax.
   LENGTH pi = SUC n ==>
   NTH n pi = SOME en ==>
   NTH i pi = SOME ei ==>
   (!t. t > tmax ==> ~(name_mapped_in_State t (SND (SND en)))) ==>
   name_of_l (FST (SND ei)) <= tmax
Proof
 STRIP_TAC >> STRIP_TAC >>
 STRIP_TAC >> STRIP_TAC >>
 Induct_on `SUC n - i` >> rw [] >-
  (`NTH i pi <> NONE` by fs [] >>
   `i < LENGTH pi` suffices_by DECIDE_TAC >>
   METIS_TAC [NTH_SOME]) >>
 Cases_on `v` >> rw [] >-
  (fs [] >> `n = i` by DECIDE_TAC >>
   rw [] >> `ei = en` by fs [] >> rw [] >>
   `?pi1 pi2. pi = pi1 ++ ei::pi2` by METIS_TAC [NTH_split] >>
   Cases_on `ei` >> Cases_on `r` >>
   Cases_on `q'` >> Cases_on `r'` >>
   fs [name_of_l] >>
   Cases_on `q` >>
   sg `out_of_order_step (State_st f' f0' f1' f2') (l_lb o' a n) (State_st f f0 f1 f2)` >-
    (fs [] >> rw [] >>
    `pi1 ++ [(State_st f' f0' f1' f2',l_lb o' a n,State_st f f0 f1 f2)] ++ pi2 =
     pi1 ++ (State_st f' f0' f1' f2',l_lb o' a n,State_st f f0 f1 f2)::pi2` by fs [] >>
    METIS_TAC [step_execution_mid]) >>
   sg `well_formed_state (State_st f' f0' f1' f2')` >-
    (Cases_on `pi1` >> fs [] >>
     Cases_on `h` >> Cases_on `r` >>
     fs [] >>
     `(q,q',r')::(t ++ [(State_st f' f0' f1' f2',l_lb o' a n,State_st f f0 f1 f2)] ++ pi2) =
      (q,q',r')::t ++ (State_st f' f0' f1' f2',l_lb o' a n,State_st f f0 f1 f2)::pi2` by fs [] >>
     METIS_TAC [well_formed_OoO_LTC_invariant,step_execution_mid_FST_LTC_invariant]) >>
   Cases_on `n <= tmax` >> rw [] >>
   `n > tmax` by DECIDE_TAC >>
   `~ name_mapped_in_State n (State_st f f0 f1 f2)` by METIS_TAC [] >>
   fs [name_mapped_in_State,out_of_order_step_cases] >> rw [] >- fs [FDOM_FUPDATE] >>
   fs [map_down,flookup_thm]) >>
 `i < SUC n` by DECIDE_TAC >>
 `SUC n' = SUC n - SUC i` by DECIDE_TAC >>
 `SUC i < SUC n` by DECIDE_TAC >>
 Cases_on `NTH (SUC i) pi` >- METIS_TAC [NTH_SOME] >>
 `name_of_l (FST (SND x)) <= tmax` by METIS_TAC [] >>
 `?pi1 pi2. pi = pi1 ++ [ei;x] ++ pi2` by METIS_TAC [NTH_SUC_mid] >>
 `name_of_l (FST (SND ei)) <= name_of_l (FST (SND x))` suffices_by DECIDE_TAC >>
 `i < SUC i` by DECIDE_TAC >>
 METIS_TAC [ordered_execution]
QED

Theorem OoO_ordered_in_order_prefix[local]:
 !pi. step_execution out_of_order_step pi ==>
  well_formed_state (FST (HD pi)) ==>
  ordered_execution pi ==>
  (?tmax.
   (!t. name_instr_in_State t (SND (SND (LAST pi))) /\ t <= tmax ==> Completed_t (SND (SND (LAST pi))) t) /\
   (!t. t > tmax ==> ~(name_mapped_in_State t (SND (SND (LAST pi)))))) ==>
  !pi'. pi' <> [] ==> pi' <<= pi ==>
  step_execution in_order_step pi'
Proof
 STRIP_TAC >> STRIP_TAC >>
 STRIP_TAC >> STRIP_TAC >> STRIP_TAC >>
 HO_MATCH_MP_TAC SNOC_INDUCT >> rw [] >>
 `pi' ++ [x] <<= pi` by METIS_TAC [SNOC_APPEND] >>
 Cases_on `pi' = []` >-
  (rw [] >> fs [] >>
   Cases_on `pi` >> fs [] >> rw [] >>
   `h::t = [] ++ h::t` by rw [] >>
   Cases_on `h` >> Cases_on `r` >>
   `out_of_order_step q q' r'` by METIS_TAC [step_execution_mid] >>
   `in_order_step q q' r'` suffices_by METIS_TAC [step_execution_rules] >>
   Cases_on `q'` >>
   `!i. instr_in_State i q ==> bound_name_instr i < n ==> Completed q i`
    suffices_by METIS_TAC [in_order_step_rules,clause_name_def] >>
   Cases_on `q` >> rename1 `State_st I0 s0 C0 F0` >>
   rw [instr_in_State] >>
   Cases_on `r'` >>
   rename1 `(State_st I0 s0 C0 F0,l_lb ob ac t',State_st I1 s1 C1 F1)::pi'` >>
   Q.ABBREV_TAC `pi = (State_st I0 s0 C0 F0,l_lb ob ac t',State_st I1 s1 C1 F1)::pi'` >>
   Cases_on `i` >> rename1 `i_assign t e mop` >> fs [bound_name_instr] >>
   `Completed_t (State_st I0 s0 C0 F0) t`
    suffices_by METIS_TAC [Completed_t,bound_name_instr,well_formed_state] >>
   `?n. LENGTH pi = SUC n` by fs [Abbr `pi`] >>
   `NTH 0 pi = SOME (State_st I0 s0 C0 F0,l_lb ob ac t',State_st I1 s1 C1 F1)`
    by rw [Abbr `pi`,NTH] >>
   sg `between_name_of_l_gt pi n 0 t` >-
     (rw [between_name_of_l_gt] >>
      Cases_on `j` >- (fs [] >> rw [name_of_l]) >>
      `0 < SUC n'` by DECIDE_TAC >>
      `t' <= name_of_l (FST (SND ej))` suffices_by DECIDE_TAC >>
      `name_of_l (FST (SND (State_st I0 s0 C0 F0,l_lb ob ac t',State_st I1 s1 C1 F1))) <= name_of_l (FST (SND ej))`
       suffices_by fs [name_of_l] >>
      METIS_TAC [ordered_execution]) >>
   `NTH n pi = SOME (LAST pi)` by METIS_TAC [NTH_LENGTH_LAST] >>
   `well_formed_state (FST (HD pi))` by fs [Abbr `pi`] >>
   sg `t <= tmax` >-
    (`t' <= tmax` suffices_by DECIDE_TAC >>
     `name_of_l (FST (SND (State_st I0 s0 C0 F0,l_lb ob ac t',State_st I1 s1 C1 F1))) <= tmax`
      suffices_by fs [name_of_l] >>
     METIS_TAC [out_of_order_execution_result]) >>
   sg `name_instr_in_State t (SND (SND (LAST pi)))` >-
    (`t = bound_name_instr (i_assign t e mop)` by fs [bound_name_instr] >>
     `name_instr_in_State t (State_st I0 s0 C0 F0)`
      by (fs [name_instr_in_State,bound_names_program] >> METIS_TAC []) >>
     `name_instr_in_State t (FST (HD pi))` by fs [Abbr `pi`] >>
     METIS_TAC [OoO_instr_in_fst_in_last]) >>
   `Completed_t (SND (SND (LAST pi))) t` by METIS_TAC [] >>
   `Completed_t (SND (SND (State_st I0 s0 C0 F0,l_lb ob ac t',State_st I1 s1 C1 F1))) t`
    by METIS_TAC [out_of_order_complete_consistent] >>
   fs [Completed_t] >>
   Q.EXISTS_TAC `i` >>
   Cases_on `i` >> fs [bound_name_instr] >>
   `t' > n'` by DECIDE_TAC >>
   rw [] >> METIS_TAC [OoO_instr_in_after_in_before,OoO_completed_after_completed_before]) >>
 `pi' <<= pi` by METIS_TAC [isPREFIX_SNOC] >>
 `step_execution in_order_step pi'` by METIS_TAC [] >>
 `step_execution in_order_step (pi' ++ [x])` suffices_by rw [SNOC_APPEND] >>
 `?pi''. pi = pi' ++ [x] ++ pi''` by METIS_TAC [isPREFIX_split] >>
 Cases_on `x` >> Cases_on `r` >> rename1 `(s3,l2,s4)` >>
 `pi' = [] \/ ?x pi0. pi' = pi0 ++ [x]` by METIS_TAC [SNOC_CASES,SNOC_APPEND] >>
 Cases_on `x` >> Cases_on `r` >> rw [] >> rename1 `(s1,l1,s2)` >>
 `pi0 ++ [(s1,l1,s2)] ++ [(s3,l2,s4)] = pi0 ++ [(s1,l1,s2);(s3,l2,s4)]` by fs [] >>
 `s2 = s3` by METIS_TAC [step_execution_append_eq_state] >>
 rw [] >>
 sg `well_formed_state s1` >-
  (Cases_on `pi0` >> fs [] >> rw [] >>
   Cases_on `h` >> Cases_on `r` >>
   `(q,q',r')::(t ++ [(s1,l1,s2)] ++ [(s2,l2,s4)] ++ pi'') =
    (q,q',r')::t ++ (s1,l1,s2)::(s2,l2,s4)::pi''` by fs [] >>
   `well_formed_state q` by fs [] >>
   METIS_TAC [well_formed_OoO_LTC_invariant,step_execution_mid_FST_LTC_invariant]) >>
 sg `out_of_order_step s1 l1 s2` >-
  (`pi0 ++ [(s1,l1,s2)] ++ [(s2,l2,s4)] ++ pi'' =
   pi0 ++ (s1,l1,s2)::(s2,l2,s4)::pi''` by fs [] >>
   METIS_TAC [step_execution_mid]) >>
 `well_formed_state s2` by METIS_TAC [well_formed_OoO_transition_well_formed,step_invariant] >>
 sg `out_of_order_step s2 l2 s4` >-
  (`pi0 ++ [(s1,l1,s2)] ++ [(s2,l2,s4)] ++ pi'' =
   pi0 ++ [(s1,l1,s2)] ++ (s2,l2,s4)::pi''` by fs [] >>
   METIS_TAC [step_execution_mid]) >>
 `well_formed_state s4` by METIS_TAC [well_formed_OoO_transition_well_formed,step_invariant] >>
 sg `in_order_step s1 l1 s2` >-
  (Cases_on `pi0 = []` >-
   (fs [] >> METIS_TAC [step_execution_singleton]) >>
   METIS_TAC [step_execution_reduce_one]) >>
 sg `name_of_l l1 <= name_of_l l2` >-
  (`LENGTH pi0 < SUC (LENGTH pi0)` by DECIDE_TAC >>
   `LENGTH pi0 <= LENGTH pi0` by DECIDE_TAC >>
   `LENGTH pi0 - LENGTH pi0 = 0` by DECIDE_TAC >>
   `pi0 ++ [(s1,l1,s2)] ++ [(s2,l2,s4)] ++ pi'' =
    pi0 ++ (s1,l1,s2)::(s2,l2,s4)::pi''` by fs [] >>
   `NTH (LENGTH pi0) (pi0 ++ [(s1,l1,s2)] ++ [(s2,l2,s4)] ++ pi'') = SOME (s1,l1,s2)`
    by METIS_TAC [NTH_app2,NTH] >>
   `LENGTH pi0 <= SUC (LENGTH pi0)` by DECIDE_TAC >>
   `SUC (LENGTH pi0) - LENGTH pi0 = 1` by DECIDE_TAC >>
   sg `NTH (SUC (LENGTH pi0)) (pi0 ++ [(s1,l1,s2)] ++ [(s2,l2,s4)] ++ pi'') = SOME (s2,l2,s4)` >-
    (`NTH 1 ((s1,l1,s2)::(s2,l2,s4)::pi'') = SOME (s2,l2,s4)` suffices_by METIS_TAC [NTH_app2,NTH] >>
     `1 = SUC 0` by DECIDE_TAC >>
     METIS_TAC [NTH]) >>
   `l1 = FST (SND (s1,l1,s2))` by rw [] >>
   `l2 = FST (SND (s2,l2,s4))` by rw [] >>
   METIS_TAC [ordered_execution]) >>
 `in_order_step s2 l2 s4` suffices_by METIS_TAC [step_execution_rules] >>
 Cases_on `s1` >> rename1 `(State_st I0 s0 C0 F0)` >>
 Cases_on `l1` >> rename1 `l_lb ob1 a1 t1` >>
 Cases_on `s2` >> rename1 `(State_st I1 s1 C1 F1)` >>
 Cases_on `l2` >> rename1 `l_lb ob2 a2 t2` >>
 Cases_on `s4` >>
 fs [in_order_step_cases,name_of_l,instr_in_State] >> rw [] >>
 Cases_on `i` >> rename1 `i_assign t c mop` >>
 fs [bound_name_instr] >>
 `Completed_t (State_st I1 s1 C1 F1) t`
  suffices_by METIS_TAC [Completed_t,bound_name_instr,well_formed_state] >>
 Q.ABBREV_TAC `pi = pi0 ++
  [(State_st I0 s0 C0 F0,l_lb ob1 a1 t1,State_st I1 s1 C1 F1)] ++
  [(State_st I1 s1 C1 F1,l_lb ob2 a2 t2,State_st f f0 f1 f2)] ++ pi''` >>
 sg `?n. LENGTH pi = SUC n` >-
  (fs [Abbr `pi`] >> Q.EXISTS_TAC `LENGTH pi'' + SUC (LENGTH pi0)` >> fs []) >>
 sg `?s l s'. LAST pi = (s,l,s')` >-
  (`pi = pi0 ++ [(State_st I0 s0 C0 F0,l_lb ob1 a1 t1,State_st I1 s1 C1 F1)] ++ 
   (State_st I1 s1 C1 F1,l_lb ob2 a2 t2,State_st f f0 f1 f2)::pi''` by fs [Abbr `pi`] >>
   rw [] >> `pi'' = [] \/ ?l x. pi'' = SNOC x l` by METIS_TAC [SNOC_CASES] >> rw [] >>
   Cases_on `x` >> Cases_on `r` >> fs [LAST_DEF] >> rw [LAST_SNOC]) >>
 `NTH n pi = SOME (s,l,s')` by fs [NTH_LENGTH_LAST] >>
 sg `NTH (SUC (LENGTH pi0)) pi = SOME (State_st I1 s1 C1 F1,l_lb ob2 a2 t2,State_st f f0 f1 f2)` >-
  (`pi = pi0 ++ (State_st I0 s0 C0 F0,l_lb ob1 a1 t1,State_st I1 s1 C1 F1)::
    (State_st I1 s1 C1 F1,l_lb ob2 a2 t2,State_st f f0 f1 f2)::pi''` by fs [Abbr `pi`] >>
   `LENGTH pi0 <= SUC (LENGTH pi0)` by DECIDE_TAC >>
   `SUC (LENGTH pi0) - LENGTH pi0 = 1` by DECIDE_TAC >>
   `NTH 1 ((State_st I0 s0 C0 F0,l_lb ob1 a1 t1,State_st I1 s1 C1 F1)::
    (State_st I1 s1 C1 F1,l_lb ob2 a2 t2,State_st f f0 f1 f2)::pi'') = 
    SOME (State_st I1 s1 C1 F1,l_lb ob2 a2 t2,State_st f f0 f1 f2)`
    suffices_by METIS_TAC [NTH_app2,NTH] >>
   `1 = SUC 0` by DECIDE_TAC >>
   METIS_TAC [NTH]) >>
 sg `between_name_of_l_gt pi n (SUC (LENGTH pi0)) t` >-
  (rw [between_name_of_l_gt] >>
   Cases_on `j <= SUC (LENGTH pi0)` >-
    (`j = SUC (LENGTH pi0)` by DECIDE_TAC >>
     rw [] >> fs [name_of_l]) >>
   `SUC (LENGTH pi0) < j` by DECIDE_TAC >>
   `t2 <= name_of_l (FST (SND ej))` suffices_by DECIDE_TAC >>
   `name_of_l (FST (SND (State_st I1 s1 C1 F1,l_lb ob2 a2 t2,State_st f f0 f1 f2))) <= name_of_l (FST (SND ej))`
    suffices_by fs [name_of_l] >>
   METIS_TAC [ordered_execution]) >>
 `NTH n pi = SOME (LAST pi)` by METIS_TAC [NTH_LENGTH_LAST] >>
 sg `t <= tmax` >-
   (`t2 <= tmax` suffices_by DECIDE_TAC >>
    `name_of_l (FST (SND (State_st I1 s1 C1 F1,l_lb ob2 a2 t2,State_st f f0 f1 f2))) <= tmax`
     suffices_by fs [name_of_l] >>
    METIS_TAC [out_of_order_execution_result]) >>
 sg `name_instr_in_State t (SND (SND (LAST pi)))` >-
  (`t = bound_name_instr (i_assign t c mop)` by fs [bound_name_instr] >>
   `name_instr_in_State t (State_st I1 s1 C1 F1)`
    by (fs [name_instr_in_State,bound_names_program] >> METIS_TAC []) >>
   `pi = pi0 ++ [(State_st I0 s0 C0 F0,l_lb ob1 a1 t1,State_st I1 s1 C1 F1)] ++
    (State_st I1 s1 C1 F1,l_lb ob2 a2 t2,State_st f f0 f1 f2)::pi''` by fs [Abbr `pi`] >>
   `step_execution out_of_order_step ((State_st I1 s1 C1 F1,l_lb ob2 a2 t2,State_st f f0 f1 f2)::pi'')`
    by METIS_TAC [step_execution_mid_execution] >>
   sg `SND (SND (LAST pi)) = SND (SND (LAST ((State_st I1 s1 C1 F1,l_lb ob2 a2 t2,State_st f f0 f1 f2)::pi'')))` >-
    (`SND (SND (LAST (pi0 ++ [(State_st I0 s0 C0 F0,l_lb ob1 a1 t1,State_st I1 s1 C1 F1)] ++
      (State_st I1 s1 C1 F1,l_lb ob2 a2 t2,State_st f f0 f1 f2)::pi''))) =
      SND (SND (LAST ((State_st I1 s1 C1 F1,l_lb ob2 a2 t2,State_st f f0 f1 f2)::pi'')))` suffices_by rw [] >>
     fs [LAST_APPEND_CONS]) >>
   `name_instr_in_State t (SND (SND (LAST ((State_st I1 s1 C1 F1,l_lb ob2 a2 t2,State_st f f0 f1 f2)::pi''))))`
    suffices_by fs [] >>
   `name_instr_in_State t (FST (HD ((State_st I1 s1 C1 F1,l_lb ob2 a2 t2,State_st f f0 f1 f2)::pi'')))` by fs [] >>
   METIS_TAC [OoO_instr_in_fst_in_last]) >>
 `Completed_t (SND (SND (LAST pi))) t` by METIS_TAC [] >>
 `Completed_t (SND (SND (State_st I1 s1 C1 F1,l_lb ob2 a2 t2,State_st f f0 f1 f2))) t`
  by METIS_TAC [out_of_order_complete_consistent] >>
 fs [Completed_t] >>
 Q.EXISTS_TAC `i` >>
 Cases_on `i` >> fs [bound_name_instr] >>
 `t2 > n'` by DECIDE_TAC >>
 rw [] >> METIS_TAC [OoO_instr_in_after_in_before,OoO_completed_after_completed_before]
QED

Theorem OoO_ordered_in_order:
 !pi. step_execution out_of_order_step pi ==>
  well_formed_state (FST (HD pi)) ==>
  ordered_execution pi ==>
  (?tmax.
   (!t. name_instr_in_State t (SND (SND (LAST pi))) /\ t <= tmax ==> Completed_t (SND (SND (LAST pi))) t) /\
   (!t. t > tmax ==> ~(name_mapped_in_State t (SND (SND (LAST pi)))))) ==>
  step_execution in_order_step pi
Proof
 rw [] >>
 `pi <> []` by METIS_TAC [step_execution_not_empty_list] >>
 METIS_TAC [OoO_ordered_in_order_prefix,isPREFIX_refl]
QED

Theorem OoO_step_instr_in_State_lt[local]:
 !I0 s0 C0 F0 l I1 s1 C1 F1. well_formed_state (State_st I0 s0 C0 F0) ==>
  out_of_order_step (State_st I0 s0 C0 F0) l (State_st I1 s1 C1 F1) ==>
  !i. i IN I1 ==> i NOTIN I0 ==> !i'. i' IN I0 ==> bound_name_instr i' < bound_name_instr i
Proof
 rw [] >> fs [out_of_order_step_cases] >> rw [] >> fs [] >>
 `FINITE I0` by METIS_TAC [wfs_FINITE] >>
 METIS_TAC [translate_val_max_name_lt]
QED

Theorem OoO_extend_instr_to_completed[local]:
 !pi. step_execution out_of_order_step pi ==>
  well_formed_initialized_state (FST (HD pi)) ==>
  !t. name_instr_in_State t (SND (SND (LAST pi))) ==>
  ~(Completed_t (SND (SND (LAST pi))) t) ==>
  (!t'. name_instr_in_State t' (SND (SND (LAST pi))) /\ t' < t ==> Completed_t (SND (SND (LAST pi))) t') ==>
  ?pi'. step_execution out_of_order_step (pi ++ pi') /\ Completed_t (SND (SND (LAST (pi ++ pi')))) t /\
   (!t'. t' <> t ==> (name_mapped_in_State t' (SND (SND (LAST pi))) <=>
    name_mapped_in_State t' (SND (SND (LAST (pi ++ pi')))))) /\
   (!i. instr_in_State i (SND (SND (LAST pi))) ==> instr_in_State i (SND (SND (LAST (pi ++ pi'))))) /\
   (!i. instr_in_State i (SND (SND (LAST (pi ++ pi')))) ==> ~(instr_in_State i (SND (SND (LAST pi)))) ==>
     !i'. instr_in_State i' (SND (SND (LAST pi))) ==> bound_name_instr i' < bound_name_instr i) /\
   (!t'. Completed_t (SND (SND (LAST pi))) t' ==> Completed_t (SND (SND (LAST (pi ++ pi')))) t')
Proof
 rw [] >>
 sg `well_formed_initialized_state (SND (SND (LAST pi)))` >-
  (Cases_on `pi` >> fs [] >> rw [] >- METIS_TAC [step_execution_not_empty_list] >>
   Cases_on `h` >> Cases_on `r` >> rename1 `(s1,l1,s2)` >>
   `t' = [] \/ ?e t''. t' = SNOC e t''` by rw [SNOC_CASES] >> rw [] >-
     (fs [] >>
      METIS_TAC [
       step_execution_singleton,
       step_invariant,
       well_formed_initialized_state_OoO_step_invariant
      ]) >>
   Cases_on `e` >> Cases_on `r` >> rename1 `SNOC (s3,l2,s4) t''` >>
   fs [LAST_DEF] >>
   `SNOC (s3,l2,s4) t'' = t'' ++ [(s3,l2,s4)]` by fs [] >>
   `(s1,l1,s2)::SNOC (s3,l2,s4) t'' = (s1,l1,s2)::t'' ++ (s3,l2,s4)::[]` by fs [] >>
   `step_execution out_of_order_step ((s1,l1,s2)::t'' ++ (s3,l2,s4)::[])` by METIS_TAC [] >>
   METIS_TAC [step_execution_mid_OoO_well_formed_initialized_state]) >>
 `well_formed_state (SND (SND (LAST pi)))` by fs [well_formed_initialized_state] >>
 `initialized_all_resources (SND (SND (LAST pi)))` by fs [well_formed_initialized_state] >>
 sg `?pi'' State l State'. pi = pi'' ++ [(State,l,State')]` >-
  (`pi = [] \/ ?e pi''. pi = SNOC e pi''` by rw [SNOC_CASES] >> rw [] >-
   METIS_TAC [step_execution_not_empty_list] >>
   Cases_on `e` >> Cases_on `r` >> METIS_TAC []) >>
 rw [] >> fs [] >>
 Cases_on `State'` >> rename1 `State_st I0 s0 C0 F0` >>
 sg `?c mop. i_assign t c mop IN I0` >-
  (fs [name_instr_in_State,bound_names_program] >>
   Cases_on `i` >> METIS_TAC [bound_name_instr]) >>
 sg `~(Completed (State_st I0 s0 C0 F0) (i_assign t c mop))` >-
  (fs [Completed_t] >> METIS_TAC [bound_name_instr]) >>
 sg `!t' c' mop'. i_assign t' c' mop' IN I0 /\ t' < t ==>
  Completed (State_st I0 s0 C0 F0) (i_assign t' c' mop')` >-
  (rw [] >> fs [name_instr_in_State] >>
   `t' IN bound_names_program I0`
    by (fs [bound_names_program] >> METIS_TAC [bound_name_instr]) >>
   `Completed_t (State_st I0 s0 C0 F0) t'` by METIS_TAC [] >>
   fs [Completed_t] >>
   `i = i_assign t' c' mop'` suffices_by METIS_TAC [] >>
   METIS_TAC [bound_name_instr,well_formed_state]) >>
 qsuff_tac `(?l State. out_of_order_step (State_st I0 s0 C0 F0) l State /\ Completed_t State t /\
   !t'. t' <> t ==> (name_mapped_in_State t' (State_st I0 s0 C0 F0) <=> name_mapped_in_State t' State)) \/
   ?l State l' State'. out_of_order_step (State_st I0 s0 C0 F0) l State /\
    out_of_order_step State l' State' /\ Completed_t State' t /\
     !t'. t' <> t ==> (name_mapped_in_State t' (State_st I0 s0 C0 F0) <=> name_mapped_in_State t' State')` >-
  (rw [] >-
   (Q.EXISTS_TAC `[(State_st I0 s0 C0 F0,l',State')]` >>
    rw [] >| [
     `pi'' ++ [(State,l,State_st I0 s0 C0 F0)] ++ [(State_st I0 s0 C0 F0,l',State')] =
      pi'' ++ [(State,l,State_st I0 s0 C0 F0);(State_st I0 s0 C0 F0,l',State')]` by fs [] >-
     METIS_TAC [step_execution_rules],
     Cases_on `State'` >> fs [instr_in_State] >> Cases_on `l'` >>
     METIS_TAC [OoO_transition_monotonicity_I_C_F,SUBSET_DEF],
     Cases_on `State'` >> fs [instr_in_State] >> Cases_on `l'` >>
     METIS_TAC [OoO_step_instr_in_State_lt],
     Cases_on `State'` >> Cases_on `l'` >>
     METIS_TAC [well_formed_state_OoO_completed_t_preserved]
    ]) >>
   Q.EXISTS_TAC `[(State_st I0 s0 C0 F0,l',State');(State',l'',State'')]` >>
   rw [] >| [
    `pi'' ++ [(State,l,State_st I0 s0 C0 F0)] ++ [(State_st I0 s0 C0 F0,l',State')] =
    pi'' ++ [(State,l,State_st I0 s0 C0 F0);(State_st I0 s0 C0 F0,l',State')]` by fs [] >>
    METIS_TAC [step_execution_rules],
    Cases_on `State'` >> Cases_on `State''` >>
    rename1 `out_of_order_step (State_st I1 s1 C1 F1) l'' (State_st I2 s2 C2 F2)` >>
    fs [instr_in_State] >> Cases_on `l'` >> Cases_on `l''` >>
    `i IN I1` suffices_by METIS_TAC [OoO_transition_monotonicity_I_C_F,SUBSET_DEF] >>
    METIS_TAC [OoO_transition_monotonicity_I_C_F,SUBSET_DEF],
    Cases_on `State'` >> Cases_on `State''` >>
    rename1 `out_of_order_step (State_st I1 s1 C1 F1) l'' (State_st I2 s2 C2 F2)` >>
    fs [instr_in_State] >> Cases_on `l'` >> Cases_on `l''` >>
    Cases_on `i IN I1` >- METIS_TAC [OoO_step_instr_in_State_lt] >>
    `i' IN I1` by METIS_TAC [OoO_transition_monotonicity_I_C_F,SUBSET_DEF] >>
    `well_formed_state (State_st I1 s1 C1 F1)`
     by METIS_TAC [well_formed_OoO_transition_well_formed,step_invariant] >>
    METIS_TAC [OoO_step_instr_in_State_lt],
    Cases_on `State'` >> Cases_on `State''` >>
    rename1 `out_of_order_step (State_st I1 s1 C1 F1) l'' (State_st I2 s2 C2 F2)` >>
    Cases_on `l'` >> Cases_on `l''` >>
    `well_formed_state (State_st I1 s1 C1 F1)`
     by METIS_TAC [well_formed_OoO_transition_well_formed,step_invariant] >>
    METIS_TAC [well_formed_state_OoO_completed_t_preserved]
  ]) >>
 MP_TAC (Q.SPECL [`I0`,`s0`,`C0`,`F0`,`t`,`c`,`mop`] OoO_least_incomplete_instruction_then_completable) >>
 rw []
QED

Theorem incomplete_names_State_bound_SUBSET[local]:
 !State State' t i. well_formed_state State ==>
  instr_in_State i State ==>
  t <= max_name_in_State State ==>
  (!i'. instr_in_State i' State ==> instr_in_State i' State') ==>
  (!i'. instr_in_State i' State' ==> ~(instr_in_State i' State) ==>
   !i''. instr_in_State i'' State ==> bound_name_instr i'' < bound_name_instr i') ==>
  (!t'. Completed_t State t' ==> Completed_t State' t') ==>
  incomplete_names_State_bound State' t SUBSET incomplete_names_State_bound State t
Proof
 rw [] >> Cases_on `State` >> Cases_on `State'` >>
 rename1 `incomplete_names_State_bound (State_st I1 s1 C1 F1) t SUBSET incomplete_names_State_bound (State_st I0 s0 C0 F0) t` >>
 fs [max_name_in_State] >>
 `FINITE I0` by METIS_TAC [wfs_FINITE] >>
 `FINITE (bound_names_program I0)` by METIS_TAC [finite_bound_names_program] >>
 sg `!i'. i' IN I0 ==> bound_name_instr i' <= MAX_SET (bound_names_program I0)` >-
  (rw [] >>
   `bound_name_instr i' IN bound_names_program I0`
    by (fs [bound_names_program] >> METIS_TAC []) >>
   `bound_names_program I0 <> {}` by METIS_TAC [NOT_IN_EMPTY] >>
   METIS_TAC [MAX_SET_DEF,finite_bound_names_program]) >>
 sg `bound_names_program I0 <> {}` >-
  (`bound_name_instr i IN bound_names_program I0` suffices_by METIS_TAC [NOT_IN_EMPTY] >>
   fs [bound_names_program] >> METIS_TAC [instr_in_State]) >>
 sg `?i'. i' IN I0 /\ bound_name_instr i' = MAX_SET (bound_names_program I0)` >-
  (`MAX_SET (bound_names_program I0) IN bound_names_program I0` by fs [MAX_SET_DEF] >>
   fs [bound_names_program] >> METIS_TAC []) >>
 fs [instr_in_State,Completed_t,incomplete_names_State_bound,SUBSET_DEF] >> rw [] >-
  (`?i''. i'' IN I1 /\ bound_name_instr i'' = x`
    by (fs [bound_names_program] >> METIS_TAC []) >>
   Cases_on `i'' IN I0` >- (fs [bound_names_program] >> METIS_TAC []) >>
   `bound_name_instr i' < x` by METIS_TAC [] >>
   `x <= bound_name_instr i'` suffices_by DECIDE_TAC >>
   rw []) >>
 Cases_on `i'' IN I0` >> rw [] >>
 `i'' IN I1` by METIS_TAC [] >>
 METIS_TAC []
QED

Theorem incomplete_names_State_bound_non_empty_least[local]:
 !State t. well_formed_state State ==>
  incomplete_names_State_bound State t <> {} ==>
  ?t'. t' IN incomplete_names_State_bound State t /\
   !t''. name_instr_in_State t'' State /\ t'' < t' ==> Completed_t State t''
Proof
 rw [] >>
 `?t'. t' IN incomplete_names_State_bound State t` by METIS_TAC [MEMBER_NOT_EMPTY] >>
 Cases_on `State` >> rename1 `State_st I0 s0 C0 F0` >>
 fs [incomplete_names_State_bound] >>
 `name_instr_in_State t' (State_st I0 s0 C0 F0)` by fs [name_instr_in_State] >>
 `?t'. name_instr_in_State t' (State_st I0 s0 C0 F0) /\ ~(Completed_t (State_st I0 s0 C0 F0) t') /\
   !t''. name_instr_in_State t'' (State_st I0 s0 C0 F0) /\ t'' < t' ==> Completed_t (State_st I0 s0 C0 F0) t''`
  by METIS_TAC [well_formed_not_all_completed_exists_least] >>
 Q.EXISTS_TAC `t''` >> rw [] >- fs [name_instr_in_State] >>
 Cases_on `t < t''` >- (`t' < t''` by DECIDE_TAC >> METIS_TAC []) >>
 DECIDE_TAC
QED

Theorem step_execution_gt_max_name_in_state_not_name_mapped[local]:
 !pi t. step_execution out_of_order_step pi ==>
  well_formed_initialized_state (FST (HD pi)) ==>
  t > max_name_in_State (SND (SND (LAST pi))) ==>
  ~(name_mapped_in_State t (SND (SND (LAST pi))))
Proof
 rw [] >>
 sg `well_formed_initialized_state (SND (SND (LAST pi)))` >- (* FIXME: factor out into lemma *)
  (Cases_on `pi` >> fs [] >> rw [] >- METIS_TAC [step_execution_not_empty_list] >>
   Cases_on `h` >> Cases_on `r` >> rename1 `(s1,l1,s2)` >>
   `t' = [] \/ ?e t''. t' = SNOC e t''` by rw [SNOC_CASES] >> rw [] >-
     (fs [] >>
      METIS_TAC [
       step_execution_singleton,
       step_invariant,
       well_formed_initialized_state_OoO_step_invariant
      ]) >>
   Cases_on `e` >> Cases_on `r` >> rename1 `SNOC (s3,l2,s4) t''` >>
   fs [LAST_DEF] >>
   `SNOC (s3,l2,s4) t'' = t'' ++ [(s3,l2,s4)]` by fs [] >>
   `(s1,l1,s2)::SNOC (s3,l2,s4) t'' = (s1,l1,s2)::t'' ++ (s3,l2,s4)::[]` by fs [] >>
   `step_execution out_of_order_step ((s1,l1,s2)::t'' ++ (s3,l2,s4)::[])` by METIS_TAC [] >>
   METIS_TAC [step_execution_mid_OoO_well_formed_initialized_state]) >>
 `well_formed_state (SND (SND (LAST pi)))` by fs [well_formed_initialized_state] >>
 METIS_TAC [well_formed_state_gt_max_name_not_mapped]
QED

Theorem incomplete_names_State_bound_FINITE[local]:
 !State t. well_formed_state State ==>
  FINITE (incomplete_names_State_bound State t)
Proof
 rw [] >>
 Cases_on `State` >> rename1 `State_st I0 s0 C0 F0` >>
 `FINITE I0` by METIS_TAC [wfs_FINITE] >>
 `FINITE (bound_names_program I0)` by METIS_TAC [finite_bound_names_program] >>
 `incomplete_names_State_bound (State_st I0 s0 C0 F0) t SUBSET bound_names_program I0`
  suffices_by METIS_TAC [SUBSET_FINITE] >>
 rw [incomplete_names_State_bound,SUBSET_DEF]
QED

Theorem incomplete_names_State_bound_empty_completed_t[local]:
 !State t t'. incomplete_names_State_bound State t = {} ==>
  name_instr_in_State t' State ==>
  t' <= t ==>
  Completed_t State t'
Proof
 Cases_on `State` >> rename1 `State_st I0 s0 C0 F0` >>
 rw [name_instr_in_State] >>
 `t' NOTIN incomplete_names_State_bound (State_st I0 s0 C0 F0) t`
  by METIS_TAC [MEMBER_NOT_EMPTY] >>
 fs [incomplete_names_State_bound] >>
 METIS_TAC []
QED

(* OUTLINE:
- point of name bound is to have a constant such that the incomplete set does not grow over transitions
- if all instructions are complete, we are done
- if not all instructions are complete:
  * find instruction with least name such that all previous instructions are complete
  * apply OoO_extend_instr_to_completed to extend trace to where selected instruction is complete
  * since the completed instruction set became smaller, apply complete-induction hypothesis to extend trace further
*)
Theorem OoO_extend_well_formed_initialized_max_name_in_State:
 !pi. step_execution out_of_order_step pi ==>
  well_formed_initialized_state (FST (HD pi)) ==>
  ?pi'. step_execution out_of_order_step (pi ++ pi') /\
   (!t. name_instr_in_State t (SND (SND (LAST (pi ++ pi')))) /\ t <= max_name_in_State (SND (SND (LAST pi))) ==>
     Completed_t (SND (SND (LAST (pi ++ pi')))) t) /\
   (!t. t > max_name_in_State (SND (SND (LAST pi))) ==> ~(name_mapped_in_State t (SND (SND (LAST (pi ++ pi'))))))
Proof
 qsuff_tac `!n pi t. t <= max_name_in_State (SND (SND (LAST pi))) ==>
  (!t'. t' > t ==> ~(name_mapped_in_State t' (SND (SND (LAST pi))))) ==>
  CARD (incomplete_names_State_bound (SND (SND (LAST pi))) t) = n ==>
  step_execution out_of_order_step pi ==>
  well_formed_initialized_state (FST (HD pi)) ==>
  ?pi'. step_execution out_of_order_step (pi ++ pi') /\
   (!t'. name_instr_in_State t' (SND (SND (LAST (pi ++ pi')))) /\ t' <= t ==>
     Completed_t (SND (SND (LAST (pi ++ pi')))) t') /\
   (!t'. t' > t ==> ~(name_mapped_in_State t' (SND (SND (LAST (pi ++ pi'))))))` >-
  (rw [] >>
   Q.PAT_X_ASSUM `!pi t. P` (STRIP_ASSUME_TAC o (Q.SPECL [`pi`,`max_name_in_State (SND (SND (LAST (pi :(State # l # State) list))))`])) >>
   rw [] >> fs [] >>
   `!t'. t' > max_name_in_State (SND (SND (LAST pi))) ==> ~(name_mapped_in_State t' (SND (SND (LAST pi))))`
    suffices_by METIS_TAC [] >>
   rw [] >>
   METIS_TAC [step_execution_gt_max_name_in_state_not_name_mapped]) >>
 HO_MATCH_MP_TAC COMPLETE_INDUCTION >> rw [] >>
 sg `well_formed_initialized_state (SND (SND (LAST pi)))` >- (* FIXME: factor out into lemma *)
  (Cases_on `pi` >> fs [] >> rw [] >- METIS_TAC [step_execution_not_empty_list] >>
   Cases_on `h` >> Cases_on `r` >> rename1 `(s1,l1,s2)` >>
   `t' = [] \/ ?e t''. t' = SNOC e t''` by rw [SNOC_CASES] >> rw [] >-
     (fs [] >>
      METIS_TAC [
       step_execution_singleton,
       step_invariant,
       well_formed_initialized_state_OoO_step_invariant
      ]) >>
   Cases_on `e` >> Cases_on `r` >> rename1 `SNOC (s3,l2,s4) t''` >>
   fs [LAST_DEF] >>
   `SNOC (s3,l2,s4) t'' = t'' ++ [(s3,l2,s4)]` by fs [] >>
   `(s1,l1,s2)::SNOC (s3,l2,s4) t'' = (s1,l1,s2)::t'' ++ (s3,l2,s4)::[]` by fs [] >>
   `step_execution out_of_order_step ((s1,l1,s2)::t'' ++ (s3,l2,s4)::[])` by METIS_TAC [] >>
   METIS_TAC [step_execution_mid_OoO_well_formed_initialized_state]) >>
 `well_formed_state (SND (SND (LAST pi)))` by fs [well_formed_initialized_state] >>
 Cases_on `CARD (incomplete_names_State_bound (SND (SND (LAST pi))) t)` >-
  (`incomplete_names_State_bound (SND (SND (LAST pi))) t = {}`
    by METIS_TAC [incomplete_names_State_bound_FINITE,CARD_EQ_0] >>
   Q.EXISTS_TAC `[]` >> rw [] >>
   METIS_TAC [incomplete_names_State_bound_empty_completed_t]) >>
 `CARD (incomplete_names_State_bound (SND (SND (LAST pi))) t) <> 0` by DECIDE_TAC >>
 `incomplete_names_State_bound (SND (SND (LAST pi))) t <> {}`
  by METIS_TAC [incomplete_names_State_bound_FINITE,CARD_EQ_0] >>
 `?t'. t' IN incomplete_names_State_bound (SND (SND (LAST pi))) t /\
   !t''. name_instr_in_State t'' (SND (SND (LAST pi))) /\ t'' < t' ==>
    Completed_t (SND (SND (LAST pi))) t''`
  by METIS_TAC [incomplete_names_State_bound_non_empty_least] >>
 `name_instr_in_State t' (SND (SND (LAST pi))) /\ t' <= t /\ ~(Completed_t (SND (SND (LAST pi))) t')`
  by (Cases_on `SND (SND (LAST pi))` >> fs [incomplete_names_State_bound,name_instr_in_State]) >>
 `?pi'. step_execution out_of_order_step (pi ++ pi') /\ Completed_t (SND (SND (LAST (pi ++ pi')))) t' /\
   (!t''. t'' <> t' ==> (name_mapped_in_State t'' (SND (SND (LAST pi))) <=>
    name_mapped_in_State t'' (SND (SND (LAST (pi ++ pi')))))) /\
   (!i. instr_in_State i (SND (SND (LAST pi))) ==> instr_in_State i (SND (SND (LAST (pi ++ pi'))))) /\
   (!i. instr_in_State i (SND (SND (LAST (pi ++ pi')))) ==> ~(instr_in_State i (SND (SND (LAST pi)))) ==>
     !i'. instr_in_State i' (SND (SND (LAST pi))) ==> bound_name_instr i' < bound_name_instr i) /\
   (!t''. Completed_t (SND (SND (LAST pi))) t'' ==> Completed_t (SND (SND (LAST (pi ++ pi')))) t'')`
  by METIS_TAC [OoO_extend_instr_to_completed] >>
 `well_formed_initialized_state (FST (HD (pi ++ pi')))`
  by (Cases_on `pi` >> fs [] >> METIS_TAC [step_execution_not_empty_list]) >>
 sg `CARD (incomplete_names_State_bound (SND (SND (LAST (pi ++ pi')))) t) <
  CARD (incomplete_names_State_bound (SND (SND (LAST pi))) t)` >-
  (`FINITE (incomplete_names_State_bound (SND (SND (LAST pi))) t)`
    by METIS_TAC [incomplete_names_State_bound_FINITE] >>
   `t' NOTIN incomplete_names_State_bound (SND (SND (LAST (pi ++ pi')))) t`
    by (Cases_on `SND (SND (LAST (pi ++ pi')))` >> fs [incomplete_names_State_bound]) >>
   sg `incomplete_names_State_bound (SND (SND (LAST (pi ++ pi')))) t SUBSET
    incomplete_names_State_bound (SND (SND (LAST pi))) t` >-
    (sg `?i. instr_in_State i (SND (SND (LAST pi)))` >-
      (Cases_on `SND (SND (LAST pi))` >>
       fs [instr_in_State,name_instr_in_State,bound_names_program] >>
       METIS_TAC []) >>
     METIS_TAC [incomplete_names_State_bound_SUBSET]) >>
   METIS_TAC [SUBSET_without_member_CARD_lt]) >>
 sg `t <= max_name_in_State (SND (SND (LAST (pi ++ pi'))))` >-
  (Cases_on `SND (SND (LAST pi))` >> rename1 `State_st I0 s0 C0 F0` >>
   Cases_on `SND (SND (LAST (pi ++ pi')))` >> rename1 `State_st I1 s1 C1 F1` >>
   fs [max_name_in_State,name_instr_in_State] >>
   `bound_names_program I0 <> {}` by METIS_TAC [MEMBER_NOT_EMPTY] >>
   `FINITE I0` by METIS_TAC [wfs_FINITE] >>
   `FINITE (bound_names_program I0)` by METIS_TAC [finite_bound_names_program] >>
   `MAX_SET (bound_names_program I0) IN bound_names_program I0` by METIS_TAC [MAX_SET_DEF] >>
   `?i. i IN I0 /\ bound_name_instr i = MAX_SET (bound_names_program I0)`
    by (fs [bound_names_program,bound_name_instr] >> METIS_TAC []) >>
   `i IN I1` by METIS_TAC [instr_in_State] >>
   `MAX_SET (bound_names_program I0) IN bound_names_program I1`
    by (fs [bound_names_program,bound_name_instr] >> METIS_TAC []) >>
   `bound_names_program I1 <> {}` by METIS_TAC [MEMBER_NOT_EMPTY] >>
   `MAX_SET (bound_names_program I0) <= MAX_SET (bound_names_program I1)`
    suffices_by DECIDE_TAC >>
   `FINITE (bound_names_program I1)` suffices_by METIS_TAC [MAX_SET_DEF] >>
   `FINITE I1` suffices_by METIS_TAC [finite_bound_names_program] >>
   `well_formed_state (SND (SND (LAST (pi ++ pi'))))` suffices_by METIS_TAC [wfs_FINITE] >>
   `well_formed_initialized_state (SND (SND (LAST (pi ++ pi'))))`
    suffices_by rw [well_formed_initialized_state] >> (* FIXME: use lemma *)
   Cases_on `pi ++ pi'` >> fs [] >> rw [] >> rename1 `e::l` >>
   Cases_on `e` >> Cases_on `r` >>
   `l = [] \/ ?e l'. l = SNOC e l'` by rw [SNOC_CASES] >> rw [] >-
     (fs [] >>
      METIS_TAC [
       step_execution_singleton,
       step_invariant,
       well_formed_initialized_state_OoO_step_invariant
      ]) >>
   Cases_on `e` >> Cases_on `r` >> rename1 `SNOC (s3,l2,s4) l'` >>
   fs [LAST_DEF] >>
   `SNOC (s3,l2,s4) l' = l' ++ [(s3,l2,s4)]` by fs [] >>
   `(q,q',r')::SNOC (s3,l2,s4) l' = (q,q',r')::l' ++ (s3,l2,s4)::[]` by fs [] >>
   `step_execution out_of_order_step ((q,q',r')::l' ++ (s3,l2,s4)::[])` by METIS_TAC [] >>
   METIS_TAC [step_execution_mid_OoO_well_formed_initialized_state]) >>
 sg `!t'. t' > t ==> ~(name_mapped_in_State t' (SND (SND (LAST (pi ++ pi')))))` >-
  (rw [] >> STRIP_TAC >>
   `t'' <> t'` by DECIDE_TAC >> METIS_TAC []) >>
 `?pi''. step_execution out_of_order_step ((pi ++ pi') ++ pi'') /\
  (!t'. name_instr_in_State t' (SND (SND (LAST ((pi ++ pi') ++ pi'')))) /\ t' <= t ==>
    Completed_t (SND (SND (LAST ((pi ++ pi') ++ pi'')))) t') /\
  !t'. t' > t ==> ~(name_mapped_in_State t' (SND (SND (LAST ((pi ++ pi') ++ pi'')))))`
  by METIS_TAC [] >>
 Q.EXISTS_TAC `pi' ++ pi''` >> rw []
QED

(* FIXME: need subtypes for well-formedness in memory_consistent *)
Theorem OoO_IO_well_formed_memory_consistent:
 !pi. well_formed_initialized_state (FST (HD pi)) ==>
  step_execution out_of_order_step pi ==>
  ?pi'. step_execution in_order_step pi' /\
   FST (HD pi') = FST (HD pi) /\
   !a. commits pi a <<= commits pi' a
Proof
 rw [] >>
 `well_formed_state (FST (HD pi))` by fs [well_formed_initialized_state] >>
 `?pi'. step_execution out_of_order_step (pi ++ pi') /\
   (!t. name_instr_in_State t (SND (SND (LAST (pi ++ pi')))) /\ t <= max_name_in_State (SND (SND (LAST pi))) ==>
     Completed_t (SND (SND (LAST (pi ++ pi')))) t) /\
   (!t. t > max_name_in_State (SND (SND (LAST pi))) ==> ~(name_mapped_in_State t (SND (SND (LAST (pi ++ pi'))))))`
  by METIS_TAC [OoO_extend_well_formed_initialized_max_name_in_State] >>
 sg `HD pi = HD (pi ++ pi')` >-
  (`pi <> []` suffices_by METIS_TAC [HD_APPEND_reduce] >>
   METIS_TAC [step_execution_not_empty_list]) >> 
 `well_formed_state (FST (HD (pi ++ pi')))` by METIS_TAC [] >>
 `?pi''. ordered_version (pi ++ pi') pi'' /\ step_execution out_of_order_step pi''`
  by METIS_TAC [out_of_order_exists_reordering] >>
 `!a. commits pi'' a = commits (pi ++ pi') a` by METIS_TAC [ordered_version] >>
 `FST (HD (pi ++ pi')) = FST (HD pi'')` by METIS_TAC [ordered_version] >>
 `SND (SND (LAST (pi ++ pi'))) = SND (SND (LAST pi''))` by METIS_TAC [ordered_version] >>
 `ordered_execution pi''` by METIS_TAC [ordered_version] >>
 Q.EXISTS_TAC `pi''` >> rw [] >-
 METIS_TAC [OoO_ordered_in_order] >>
 rw [commits_app]
QED

Theorem step_execution_in_order_then_out_of_order:
 !pi. step_execution in_order_step pi ==>
  step_execution out_of_order_step pi
Proof
 MATCH_MP_TAC step_execution_ind >>
 rw [] >> fs [in_order_step_cases] >> rw [] >-
 METIS_TAC [step_execution_cases] >>
 METIS_TAC [step_execution_rules]
QED

Theorem IO_OoO_memory_consistent:
 !pi. step_execution in_order_step pi ==>
  ?pi'. step_execution out_of_order_step pi' /\
   FST (HD pi') = FST (HD pi) /\
   !a. commits pi a <<= commits pi' a
Proof
 rw [] >> Q.EXISTS_TAC `pi` >>
 rw [step_execution_in_order_then_out_of_order]
QED

val _ = export_theory ();
