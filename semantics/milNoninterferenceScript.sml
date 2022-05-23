open HolKernel boolLib bossLib listTheory pairTheory relationTheory bisimulationTheory milTheory milMetaTheory milTracesTheory milUtilityTheory;

(* ================================================ *)
(* MIL conditional noninterference and bisimulation *)
(* ================================================ *)

val _ = new_theory "milNoninterference";

(* Definition of out-of-order step with value-independent labels *)
Definition out_of_order_step':
  (out_of_order_step' S (l_lb obs (act_cmt a v) t) S' =
   ((v = 0w) /\ ?v. out_of_order_step S (l_lb obs (act_cmt a v) t) S')) /\
  (out_of_order_step' S l S' = out_of_order_step S l S')
End

(* Definition of in-order step with value-independent labels *)
Definition in_order_step':
  (in_order_step' S (l_lb obs (act_cmt a v) t) S' =
   ((v = 0w) /\ ?v. in_order_step S (l_lb obs (act_cmt a v) t) S')) /\
  (in_order_step' S l S' = in_order_step S l S')
End

(* Definition of trace indistinguishability
   NOTE: we fix two parameters of trace: obs_of_label = obs_of_l, visible = obs_visible *)
Definition trace_indist:
  trace_indist step S1 S2 =
  ((!pi1. step_execution step pi1 ==> FST (HD pi1) = S1 ==>
          ?pi2. step_execution step pi2 /\ FST (HD pi2) = S2 /\
                trace obs_of_l obs_visible pi1 = trace obs_of_l obs_visible pi2) /\
   (!pi2. step_execution step pi2 ==> FST (HD pi2) = S2 ==>
          ?pi1. step_execution step pi1 /\ FST (HD pi1) = S1 /\
                trace obs_of_l obs_visible pi1 = trace obs_of_l obs_visible pi2))
End

Definition trace_indist_IO:
  trace_indist_IO = trace_indist in_order_step'
End

Definition trace_indist_OoO:
  trace_indist_OoO = trace_indist out_of_order_step'
End

Theorem trace_indist_is_symmetric:
  ! step. symmetric (trace_indist step)
Proof
  rw [trace_indist, symmetric_def] >>
  EQ_TAC >> METIS_TAC []
QED

Theorem trace_indist_IO_is_symmetric:
  symmetric trace_indist_IO
Proof
  rw [trace_indist_IO, trace_indist_is_symmetric]
QED

Theorem trace_indist_OoO_is_symmetric:
  symmetric trace_indist_OoO
Proof
  rw [trace_indist_OoO, trace_indist_is_symmetric]
QED

(* Definition of MIL noninterference
   NOTE: secpol is not required to be an equivalence *)
Definition NI:
  NI step_p secpol =
  (!S1 S2. secpol S1 S2 ==> trace_indist step_p S1 S2)
End

Definition NI_IO:
  NI_IO = NI in_order_step'
End

Definition NI_OoO:
  NI_OoO = NI out_of_order_step'
End

(* Definition of MIL conditional noninterference
   NOTE: secpol is not required to be an equivalence *)
Definition CNI:
  CNI step_r step_t secpol =
  (!S1 S2. secpol S1 S2 ==> trace_indist step_r S1 S2 ==> trace_indist step_t S1 S2)
End

Definition CNI_IO_OoO:
  CNI_IO_OoO = CNI in_order_step' out_of_order_step'
End

Theorem NI_implies_CNI:
  ! secpol step_r step_t .
    NI step_t secpol ==> CNI step_r step_t secpol
Proof
  rw [NI, CNI]
QED

Theorem NI_OoO_implies_CNI_IO_OoO:
  ! secpol . NI_OoO secpol ==> CNI_IO_OoO secpol
Proof
  rw [NI_OoO, CNI_IO_OoO, NI, CNI]
QED

(* Lemma: bisimulation implies trace indistinguishability in OoO *)
Theorem BISIM_implies_trace_indist_OoO:
  ! S1 S2 .
    (?R. BISIM out_of_order_step' R /\ R S1 S2 /\ symmetric R) ==> trace_indist_OoO S1 S2
Proof
  rw [trace_indist_OoO] >>
  REWRITE_TAC [trace_indist] >>
  fs [BISIM_def] >>
  Q.ABBREV_TAC `step = out_of_order_step'` >>

  `(! pi1 . step_execution step pi1 ==> FST (HD pi1) = S1 ==>
            ? pi2 . step_execution step pi2 /\ FST (HD pi2) = S2 /\
                    trace obs_of_l obs_visible pi1 = trace obs_of_l obs_visible pi2 /\
                    R ((SND o SND) (LAST pi1)) ((SND o SND) (LAST pi2))) /\
   (! pi2 . step_execution step pi2 ==> FST (HD pi2) = S2 ==>
            ? pi1 . step_execution step pi1 /\ FST (HD pi1) = S1 /\
                    trace obs_of_l obs_visible pi1 = trace obs_of_l obs_visible pi2 /\
                    R ((SND o SND) (LAST pi2)) ((SND o SND) (LAST pi1)))`
    suffices_by METIS_TAC [] >>
  rw [] >| [

    Induct_on `pi1` using SNOC_INDUCT >| [
      (* impossible case: an execution is never empty *)
      METIS_TAC [step_execution_not_empty_list],

      Induct_on `pi1` using SNOC_INDUCT >>
      rw [] >| [
        (* base case: singleton execution *)
        Cases_on `x` >> Cases_on `r` >>
        rename1 `(S1, lb, S1')` >>

        `step S1 lb S1'`
          by fs [step_execution_single] >>
        `R S1 S2`
          by fs [] >>

        Cases_on `lb` >>
        rename1 `l_lb obs act t` >>
        `? S2' . step S2 (l_lb obs act t) S2' /\ R S1' S2'`
          by METIS_TAC [] >>

        (* there exists pi2 *)
        Q.EXISTS_TAC `[(S2, l_lb obs act t, S2')]` >>
        rw [] >| [
          METIS_TAC [step_execution_cases],
          fs [trace]
        ],

        (* inductive case *)
        Cases_on `x` >> Cases_on `r` >>
        Cases_on `x'` >> Cases_on `r` >>
        rename1 `SNOC (Sp1'', l1'', S1'') (SNOC (Sp1', l1', S1') pi1)` >>

        `step_execution step (pi1 ++ [(Sp1', l1', S1'); (Sp1'', l1'', S1'')])`
          by fs [SNOC_APPEND, APPEND_CONS] >>

        (* premise 1 for applying IH *)
        Q.ABBREV_TAC `S1 = FST (HD (SNOC (Sp1', l1', S1') pi1))` >>
        `S1 = FST (HD (SNOC (Sp1'', l1'', S1'') (SNOC (Sp1', l1', S1') pi1)))`
          by fs [HD_APPEND_reduce, SNOC_APPEND] >>
        `R (FST (HD (SNOC (Sp1', l1', S1') pi1))) S2`
           by fs [] >>

        (* premise 2 for applying IH *)
        `step_execution step (pi1 ++ [(Sp1', l1', S1')])`
          by METIS_TAC [step_execution_rest] >>

        (* premise 1 for applying one-step bisimulation *)
        `step Sp1'' l1'' S1''`
          by METIS_TAC [step_execution_rest] >>
        `S1' = Sp1''`
          by METIS_TAC [step_execution_append_eq_state_base] >>
        `step S1' l1'' S1''`
          by fs [] >>

        (* by IH, we get another premise for applying one-step bisimulation *)
        `? pi2. FST (HD pi2) = S2 /\ step_execution step pi2 /\
                trace obs_of_l obs_visible (SNOC (Sp1', l1', S1') pi1) =
                trace obs_of_l obs_visible pi2 /\
                R S1' ((SND o SND) (LAST pi2))`
          by METIS_TAC [SNOC_APPEND, LAST_SNOC, combinTheory.o_THM, SND] >>
        Q.ABBREV_TAC `S2' = (SND o SND) (LAST pi2)` >>

        (* now we have:
           - R S1' S2'
           - step S1' l1'' S1''
           apply one-step bisimulation to extend pi2 with: S2' -l1''-> S2''
         *)
        Cases_on `l1''` >>
        rename1 `l_lb obs act t` >>
        `? S2'' . step S2' (l_lb obs act t) S2'' /\ R S1'' S2''`
          by METIS_TAC [] >>

        (* there exists an extended pi2 *)
        Q.EXISTS_TAC `pi2 ++ [(S2', l_lb obs act t, S2'')]` >>
        rw [] >| [
          (* extended pi2 is still an execution *)
          fs [step_execution_append_one],

          (* initial state of pi2 is still S2 *)
          `pi2 <> []` by METIS_TAC [step_execution_not_empty_list] >>
          fs [HD_APPEND_reduce],

          (* extended pi2 still has the same trace as extended pi1 *)
          `trace obs_of_l obs_visible (pi1 ++ [(Sp1', l1', S1')] ++ [(S1', l_lb obs act t, S1'')]) =
           trace obs_of_l obs_visible (pi2 ++ [(S2', l_lb obs act t, S2'')])`
            by fs [trace_append_eq_label] >>
          fs []
        ]
      ]
    ],

    Induct_on `pi2` using SNOC_INDUCT >| [
      METIS_TAC [step_execution_not_empty_list],

      Induct_on `pi2` using SNOC_INDUCT >>
      rw [] >| [
        Cases_on `x` >> Cases_on `r` >>
        rename1 `(S2, lb, S2')` >>

        `step S2 lb S2'`
          by fs [step_execution_single] >>
        `R S2 S1`  (* R should be symmetric! *)
          by fs [symmetric_def] >>

        Cases_on `lb` >>
        rename1 `l_lb obs act t` >>
        `? S1' . step S1 (l_lb obs act t) S1' /\ R S2' S1'`
          by METIS_TAC [] >>

        Q.EXISTS_TAC `[(S1, l_lb obs act t, S1')]` >>
        rw [] >| [
          METIS_TAC [step_execution_cases],
          fs [trace]
        ],

        Cases_on `x` >> Cases_on `r` >>
        Cases_on `x'` >> Cases_on `r` >>
        rename1 `SNOC (Sp2'', l2'', S2'') (SNOC (Sp2', l2', S2') pi2)` >>

        `step_execution step (pi2 ++ [(Sp2', l2', S2'); (Sp2'', l2'', S2'')])`
          by fs [SNOC_APPEND, APPEND_CONS] >>

        Q.ABBREV_TAC `S2 = FST (HD (SNOC (Sp2', l2', S2') pi2))` >>
        `S2 = FST (HD (SNOC (Sp2'', l2'', S2'') (SNOC (Sp2', l2', S2') pi2)))`
          by fs [HD_APPEND_reduce, SNOC_APPEND] >>
        `R S1 (FST (HD (SNOC (Sp2', l2', S2') pi2)))`
           by fs [] >>

        `step_execution step (pi2 ++ [(Sp2', l2', S2')])`
          by METIS_TAC [step_execution_rest] >>

        `step Sp2'' l2'' S2''`
          by METIS_TAC [step_execution_rest] >>
        `S2' = Sp2''`
          by METIS_TAC [step_execution_append_eq_state_base] >>
        `step S2' l2'' S2''`
          by fs [] >>

        `? pi1. FST (HD pi1) = S1 /\ step_execution step pi1 /\
                trace obs_of_l obs_visible (SNOC (Sp2', l2', S2') pi2) =
                trace obs_of_l obs_visible pi1 /\
                R S2' ((SND o SND) (LAST pi1))`
          by METIS_TAC [SNOC_APPEND, LAST_SNOC, combinTheory.o_THM, SND] >>
        Q.ABBREV_TAC `S1' = (SND o SND) (LAST pi1)` >>

        Cases_on `l2''` >>
        rename1 `l_lb obs act t` >>
        `? S1'' . step S1' (l_lb obs act t) S1'' /\ R S2'' S1''`
          by METIS_TAC [] >>

        Q.EXISTS_TAC `pi1 ++ [(S1', l_lb obs act t, S1'')]` >>
        rw [] >| [
          fs [step_execution_append_one],

          `pi1 <> []` by METIS_TAC [step_execution_not_empty_list] >>
          fs [HD_APPEND_reduce],

          `trace obs_of_l obs_visible (pi2 ++ [(Sp2', l2', S2')] ++ [(S2', l_lb obs act t, S2'')]) =
           trace obs_of_l obs_visible (pi1 ++ [(S1', l_lb obs act t, S1'')])`
            by fs [trace_append_eq_label] >>
          fs []
        ]
      ]
    ]
  ]
QED

(* Lemma: MIL conditional noninterference reduction *)
Theorem CNI_reduction:
  ! secpol .
    (? L R .
       (!S1 S2. secpol S1 S2 ==> trace_indist_IO S1 S2 ==> L S1 S2) /\
       BISIM out_of_order_step' R /\
       (!S1 S2. secpol S1 S2 ==> L S1 S2 ==> R S1 S2)) ==>
    CNI_IO_OoO secpol
Proof
  rw [CNI_IO_OoO, CNI, trace_indist_IO] >>
  `BISIM out_of_order_step' (R RUNION inv R)`
    by fs [BISIM_RUNION, BISIM_INV] >>
  Q.ABBREV_TAC `R' = R RUNION inv R` >>
  `R' S1 S2` by METIS_TAC [RUNION] >>
  `symmetric R'` by METIS_TAC [RUNION, inv_DEF, symmetric_def] >>
  METIS_TAC [BISIM_implies_trace_indist_OoO, trace_indist_OoO]
QED



val _ = export_theory ();
