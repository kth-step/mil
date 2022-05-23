open HolKernel boolLib Parse bossLib wordsLib optionTheory wordsTheory finite_mapTheory pred_setTheory listTheory rich_listTheory sortingTheory ottTheory milUtilityTheory milTheory milSemanticsUtilityTheory milTracesTheory milMetaTheory milInitializationTheory milExecutableUtilityTheory milExecutableTransitionTheory milExecutableIOTheory;

(* ==================================== *)
(* IO trace of bounded number of steps  *)
(* ==================================== *)

val _ = new_theory "milExecutableIOTrace";

(* -------------------- *)
(* Function definitions *)
(* -------------------- *)

(* FIXME: move to better location *)
Definition obs_of_ll:
 obs_of_ll (ll_lb ob ac t) = ob
End

Definition IO_bounded_trace_acc:
 IO_bounded_trace_acc
  (f_tran : v -> t -> i list)
  (f_sem: e -> (t |-> v) -> v option)
  (State_st_list l s cs fs) (pos:num) (n:num)
  (tr:obs list) : (State_list # obs list) option =
 case n of
 | 0 => SOME (State_st_list l s cs fs,tr)
 | SUC n' =>
   (case DROP pos l of
    | [] => SOME (State_st_list l s cs fs,tr)
    | i_assign t c mop::il =>
      (case FLOOKUP s t of
      | NONE =>
        (case f_sem c s of
        | NONE => NONE
        | SOME v =>
          if v <> val_false then
            (case sem_instr_exe f_sem (i_assign t c mop) (State_st_list l s cs fs) of
             | NONE => NONE
             | SOME (v',obs) =>
               let (ll,stl) = OoO_Exe_list_instr_not_stored_guard_true_sem_instr
                 (State_st_list l s cs fs) (i_assign t c mop) v' obs in
                case mop of
                | o_store res_MEM ta tv =>
                  (case OoO_Cmt_list_stored f_sem stl t ta tv of
                   | NONE => NONE
                   | SOME (ll',stl') =>
                     let ob = obs_of_ll ll in
                     let ob' = obs_of_ll ll' in
                     if obs_visible ob then
                       IO_bounded_trace_acc f_tran f_sem stl' (SUC pos) n' (tr++[ob;ob'])
                     else
                       IO_bounded_trace_acc f_tran f_sem stl' (SUC pos) n' (tr++[ob']))
                | o_store res_PC ta tv =>
                  (case OoO_Ftc_list_stored f_tran f_sem stl t v' of
                   | NONE => NONE
                   | SOME (ll',stl') =>
                     let ob = obs_of_ll ll in
                     let ob' = obs_of_ll ll' in
                     if obs_visible ob then
                       IO_bounded_trace_acc f_tran f_sem stl' (SUC pos) n' (tr++[ob;ob'])
                     else
                       IO_bounded_trace_acc f_tran f_sem stl' (SUC pos) n' (tr++[ob']))
                | _ => (* instruction is completed, move on *)
                  let ob = obs_of_ll ll in
                  if obs_visible ob then
                    IO_bounded_trace_acc f_tran f_sem stl (SUC pos) n' (tr++[ob])
                  else
                    IO_bounded_trace_acc f_tran f_sem stl (SUC pos) n' tr)
          else (* instruction is completed, move on *)
            IO_bounded_trace_acc f_tran f_sem (State_st_list l s cs fs) (SUC pos) n' tr)
      | SOME v =>
        (case mop of
         | o_store res_MEM ta tv =>
           if MEM t cs then (* instruction is completed, move on *)
             IO_bounded_trace_acc f_tran f_sem (State_st_list l s cs fs) (SUC pos) n' tr
           else
             (case OoO_Cmt_list_stored_incomplete f_sem (State_st_list l s cs fs) t ta tv of
             | NONE => NONE
             | SOME (ll,stl) => (* instruction is completed, move on *)
               let ob = obs_of_ll ll in
               IO_bounded_trace_acc f_tran f_sem stl (SUC pos) n' (tr++[ob]))
         | o_store res_PC ta tv =>
           if MEM t fs then (* instruction is completed, move on *)
             IO_bounded_trace_acc f_tran f_sem (State_st_list l s cs fs) (SUC pos) n' tr
           else
             (case OoO_Ftc_list_stored_incomplete f_tran f_sem (State_st_list l s cs fs) t v of
              | NONE => NONE
              | SOME (ll,stl) => (* instruction is completed, move on *)
                let ob = obs_of_ll ll in
                IO_bounded_trace_acc f_tran f_sem stl (SUC pos) n' (tr++[ob]))
         | _ => (* instruction is completed, move on *)
           IO_bounded_trace_acc f_tran f_sem (State_st_list l s cs fs) (SUC pos) n' tr)))
End

Definition IO_bounded_trace_aux:
 IO_bounded_trace_aux
  (f_tran : v -> t -> i list)
  (f_sem: e -> (t |-> v) -> v option)
  (stl:State_list) (pos:num) (n:num) : (State_list # obs list) option =
  IO_bounded_trace_acc f_tran f_sem stl (PRE pos) n []
End

Definition IO_bounded_trace:
 IO_bounded_trace
  (f_tran : v -> t -> i list)
  (f_sem: e -> (t |-> v) -> v option)
  (stl:State_list) (pos:num) (n:num) : (obs list) option =
 case IO_bounded_trace_aux f_tran f_sem stl pos n of
 | SOME (stl,tr) => SOME tr
 | _ => NONE
End

(* ------------------------------ *)
(* IO_bounded_trace_acc soundness *)
(* ------------------------------ *)

Theorem IO_bounded_execution_acc_trace_acc_eq:
 !f_tran f_sem n stl stl0 pos pi pi' tr tr'.
  IO_bounded_execution_acc f_tran f_sem stl pos n pi = SOME pi' ==>
  IO_bounded_trace_acc f_tran f_sem stl pos n tr = SOME (stl0, tr') ==>
  trace obs_of_ll obs_visible pi = tr ==>
  ?pi'' tr''. pi' = pi ++ pi'' /\ tr' = tr ++ tr'' /\
   trace obs_of_ll obs_visible pi' = tr'
Proof
 strip_tac >> strip_tac >>
 Induct_on `n` >>
 Cases_on `stl` >> rename1 `State_st_list l s cs fs` >-
 fs [IO_bounded_trace_acc,IO_bounded_execution_acc] >>
 once_rewrite_tac [IO_bounded_trace_acc,IO_bounded_execution_acc] >>
 fs [] >> rw [] >>
 Cases_on `DROP pos l` >> fs [] >> rw [] >>
 Cases_on `h` >>
 rename1 `i_assign t' c mop::l'` >> rename1 `i_assign t c mop` >>
 fs [] >>
 Cases_on `FLOOKUP s t` >> fs [] >-
  (Cases_on `f_sem c s` >> fs [] >>
   rename1 `f_sem c s = SOME v` >>
   Cases_on `v = val_false` >> fs [] >-
   METIS_TAC [] >>
   Cases_on `sem_instr_exe f_sem (i_assign t c mop) (State_st_list l s cs fs)` >> fs [] >>
   Cases_on `x` >> rename1 `(v',obs)` >> fs [] >>
   Cases_on `OoO_Exe_list_instr_not_stored_guard_true_sem_instr (State_st_list l s cs fs) (i_assign t c mop) v' obs` >>
   fs [] >> rename1 `(ll,stl)` >>
   Cases_on `mop` >> fs [] >| [
    Q.ABBREV_TAC `pi0 = pi ++ [(State_st_list l s cs fs,ll,stl)]` >>
    Cases_on `obs_visible (obs_of_ll ll)` >> fs [] >-
     (Q.ABBREV_TAC `tr0 = trace obs_of_ll obs_visible pi ++ [obs_of_ll ll]` >>
      sg `tr0 = trace obs_of_ll obs_visible pi0` >-
       (fs [Abbr `tr0`,Abbr `pi0`,trace] >>
        Cases_on `ll` >> fs [obs_of_ll] >>
        rw [FILTER_APPEND_DISTRIB]) >>
      `?pi'' tr''. pi' = pi0 ++ pi'' /\
        tr' = trace obs_of_ll obs_visible pi0 ++ tr'' /\
        trace obs_of_ll obs_visible pi' = tr'`
       by METIS_TAC [] >>
      rw [] >> fs [Abbr `pi0`,trace,FILTER_APPEND_DISTRIB]) >>
    sg `trace obs_of_ll obs_visible pi = trace obs_of_ll obs_visible pi0` >-
     (fs [Abbr `pi0`,trace] >>
      Cases_on `ll` >> fs [obs_of_ll] >>
      rw [FILTER_APPEND_DISTRIB]) >>
    `?pi'' tr''. pi' = pi0 ++ pi'' /\
      tr' = trace obs_of_ll obs_visible pi0 ++ tr'' /\
      trace obs_of_ll obs_visible pi' = tr'`
     by METIS_TAC [] >>
    rw [] >> fs [Abbr `pi0`,trace,FILTER_APPEND_DISTRIB],

    Q.ABBREV_TAC `pi0 = pi ++ [(State_st_list l s cs fs,ll,stl)]` >>
    Cases_on `obs_visible (obs_of_ll ll)` >> fs [] >-
     (Q.ABBREV_TAC `tr0 = trace obs_of_ll obs_visible pi ++ [obs_of_ll ll]` >>
      sg `tr0 = trace obs_of_ll obs_visible pi0` >-
       (fs [Abbr `tr0`,Abbr `pi0`,trace] >>
        Cases_on `ll` >> fs [obs_of_ll] >>
        rw [FILTER_APPEND_DISTRIB]) >>
      `?pi'' tr''. pi' = pi0 ++ pi'' /\
        tr' = trace obs_of_ll obs_visible pi0 ++ tr'' /\
        trace obs_of_ll obs_visible pi' = tr'`
       by METIS_TAC [] >>
      rw [] >> fs [Abbr `pi0`,step_list_to_step,trace,FILTER_APPEND_DISTRIB]) >>
    sg `trace obs_of_ll obs_visible pi = trace obs_of_ll obs_visible pi0` >-
     (fs [Abbr `pi0`,trace] >>
      Cases_on `ll` >> fs [obs_of_ll,FILTER_APPEND_DISTRIB]) >>
    `?pi'' tr''. pi' = pi0 ++ pi'' /\
      tr' = trace obs_of_ll obs_visible pi0 ++ tr'' /\
      trace obs_of_ll obs_visible pi' = tr'`
     by METIS_TAC [] >>
    rw [] >> fs [Abbr `pi0`,trace,FILTER_APPEND_DISTRIB],

    Cases_on `r` >> fs [] >| [
     Cases_on `OoO_Ftc_list_stored f_tran f_sem stl t v'` >> fs [] >>
     Cases_on `x` >> fs [] >> rename1 `(ll',stl')` >>
     sg `obs_visible (obs_of_ll ll')` >-
      (Cases_on `stl` >>
       `ll' = ll_lb (obs_il v') (act_ftc_list (f_tran v' (max_bound_name_list l''))) t`
        by METIS_TAC [OoO_Ftc_list_stored_result_form] >>
       rw [obs_visible,obs_of_ll]) >>
     Q.ABBREV_TAC `pi0 = pi ++ [(State_st_list l s cs fs,ll,stl); (stl,ll',stl')]` >>
     Cases_on `obs_visible (obs_of_ll ll)` >> fs [] >-
      (Q.ABBREV_TAC `tr0 = trace obs_of_ll obs_visible pi ++ [obs_of_ll ll;obs_of_ll ll']` >>
       sg `tr0 = trace obs_of_ll obs_visible pi0` >-
        (fs [Abbr `tr0`,Abbr `pi0`,trace] >>
         Cases_on `ll` >> Cases_on `ll'` >> fs [obs_of_ll,FILTER_APPEND_DISTRIB]) >>
       `?pi'' tr''. pi' = pi0 ++ pi'' /\
         tr' = trace obs_of_ll obs_visible pi0 ++ tr'' /\
         trace obs_of_ll obs_visible pi' = tr'`
        by METIS_TAC [] >>
       rw [] >> fs [Abbr `pi0`,trace] >> 
       once_rewrite_tac [FILTER_APPEND_DISTRIB] >> fs []) >>
     Q.ABBREV_TAC `tr0 = trace obs_of_ll obs_visible pi ++ [obs_of_ll ll']` >>
     sg `tr0 = trace obs_of_ll obs_visible pi0` >-
      (fs [Abbr `tr0`,Abbr `pi0`,trace] >>
       Cases_on `ll` >> Cases_on `ll'` >> fs [obs_of_ll,FILTER_APPEND_DISTRIB]) >>
     `?pi'' tr''. pi' = pi0 ++ pi'' /\
       tr' = trace obs_of_ll obs_visible pi0 ++ tr'' /\
       trace obs_of_ll obs_visible pi' = tr'`
      by METIS_TAC [] >>
     rw [] >> fs [Abbr `pi0`,trace,FILTER_APPEND_DISTRIB],

     Q.ABBREV_TAC `pi0 = pi ++ [(State_st_list l s cs fs,ll,stl)]` >>
     Cases_on `obs_visible (obs_of_ll ll)` >> fs [] >-
      (Q.ABBREV_TAC `tr0 = trace obs_of_ll obs_visible pi ++ [obs_of_ll ll]` >>
       sg `tr0 = trace obs_of_ll obs_visible pi0` >-
        (fs [Abbr `tr0`,Abbr `pi0`,trace] >>
         Cases_on `ll` >> fs [obs_of_ll,FILTER_APPEND_DISTRIB]) >>
       `?pi'' tr''. pi' = pi0 ++ pi'' /\
        tr' = trace obs_of_ll obs_visible pi0 ++ tr'' /\
        trace obs_of_ll obs_visible pi' = tr'`
        by METIS_TAC [] >>
       rw [] >> fs [Abbr `pi0`,trace,FILTER_APPEND_DISTRIB]) >>
     sg `trace obs_of_ll obs_visible pi = trace obs_of_ll obs_visible pi0` >-
      (fs [Abbr `pi0`,trace] >>
       Cases_on `ll` >> fs [obs_of_ll,FILTER_APPEND_DISTRIB]) >>
     `?pi'' tr''. pi' = pi0 ++ pi'' /\ tr' = trace obs_of_ll obs_visible pi0 ++ tr'' /\
       trace obs_of_ll obs_visible pi' = tr'`
       by METIS_TAC [] >>
     rw [] >> fs [Abbr `pi0`,trace,FILTER_APPEND_DISTRIB],
     
     rename1 `o_store res_MEM ta tv` >>
     Cases_on `OoO_Cmt_list_stored f_sem stl t ta tv` >> fs [] >>
     Cases_on `x` >> fs [] >> rename1 `(ll',stl')` >>
     sg `obs_visible (obs_of_ll ll')` >-
      (Cases_on `stl` >>
       `?a v. ll' = ll_lb (obs_ds a) (act_cmt_list a v) t`
        by METIS_TAC [OoO_Cmt_list_stored_result_form] >>
       rw [obs_visible,obs_of_ll]) >>
     Q.ABBREV_TAC `pi0 = pi ++ [(State_st_list l s cs fs,ll,stl); (stl,ll',stl')]` >>
     Cases_on `obs_visible (obs_of_ll ll)` >> fs [] >-
      (Q.ABBREV_TAC `tr0 = trace obs_of_ll obs_visible pi ++ [obs_of_ll ll;obs_of_ll ll']` >>
       sg `tr0 = trace obs_of_ll obs_visible pi0` >-
        (fs [Abbr `tr0`,Abbr `pi0`,trace] >>
         Cases_on `ll` >> Cases_on `ll'` >>
         fs [obs_of_ll,FILTER_APPEND_DISTRIB]) >>
       `?pi'' tr''. pi' = pi0 ++ pi'' /\
         tr' = trace obs_of_ll obs_visible pi0 ++ tr'' /\
         trace obs_of_ll obs_visible pi' = tr'`
        by METIS_TAC [] >>
       rw [] >> fs [Abbr `pi0`,trace] >>
       once_rewrite_tac [FILTER_APPEND_DISTRIB] >> fs []) >>
     Q.ABBREV_TAC `tr0 = trace obs_of_ll obs_visible pi ++ [obs_of_ll ll']` >>
     sg `tr0 = trace obs_of_ll obs_visible pi0` >-
      (fs [Abbr `tr0`,Abbr `pi0`,trace] >>
       Cases_on `ll` >> Cases_on `ll'` >> fs [obs_of_ll,FILTER_APPEND_DISTRIB]) >>
     `?pi'' tr''. pi' = pi0 ++ pi'' /\
      tr' = trace obs_of_ll obs_visible pi0 ++ tr'' /\
      trace obs_of_ll obs_visible pi' = tr'`
      by METIS_TAC [] >>
     rw [] >> fs [Abbr `pi0`,trace,FILTER_APPEND_DISTRIB]
    ]
   ]) >>
 Cases_on `mop` >> fs [] >| [
  METIS_TAC [],

  METIS_TAC [],

  rename1 `FLOOKUP s t = SOME v` >>
  Cases_on `r` >> fs [] >| [
   Cases_on `MEM t fs` >> fs [] >- METIS_TAC [] >>
   Cases_on `OoO_Ftc_list_stored_incomplete f_tran f_sem (State_st_list l s cs fs) t v` >> fs [] >>
   Cases_on `x` >> fs [] >> rename1 `(ll,stl)` >>
   sg `obs_visible (obs_of_ll ll)` >-
    (`ll = ll_lb (obs_il v) (act_ftc_list (f_tran v (max_bound_name_list l))) t`
      by METIS_TAC [OoO_Ftc_list_stored_incomplete_result_form] >>
     rw [obs_visible,obs_of_ll]) >>
   Q.ABBREV_TAC `pi0 = pi ++ [(State_st_list l s cs fs,ll,stl)]` >>
   Q.ABBREV_TAC `tr0 = trace obs_of_ll obs_visible pi ++ [obs_of_ll ll]` >>
   sg `tr0 = trace obs_of_ll obs_visible pi0` >-
    (fs [Abbr `tr0`,Abbr `pi0`,trace] >>
     Cases_on `ll` >> fs [obs_of_ll,FILTER_APPEND_DISTRIB]) >>
   `?pi'' tr''. pi' = pi0 ++ pi'' /\ tr' = trace obs_of_ll obs_visible pi0 ++ tr'' /\
     trace obs_of_ll obs_visible pi' = tr'`
    by METIS_TAC [] >>
   rw [] >> fs [Abbr `pi0`,trace,FILTER_APPEND_DISTRIB],

   METIS_TAC [],

   rename1 `o_store res_MEM ta tv` >>
   Cases_on `MEM t cs` >> fs [] >- METIS_TAC [] >>
   Cases_on `OoO_Cmt_list_stored_incomplete f_sem (State_st_list l s cs fs) t ta tv` >> fs [] >>
   Cases_on `x` >> fs [] >> rename1 `(ll,stl)` >>
   sg `obs_visible (obs_of_ll ll)` >-
    (`?a v. ll = ll_lb (obs_ds a) (act_cmt_list a v) t`
      by METIS_TAC [OoO_Cmt_list_stored_incomplete_result_form] >>
     rw [obs_visible,obs_of_ll]) >>
   Q.ABBREV_TAC `pi0 = pi ++ [(State_st_list l s cs fs,ll,stl)]` >>
   Q.ABBREV_TAC `tr0 = trace obs_of_ll obs_visible pi ++ [obs_of_ll ll]` >>
   sg `tr0 = trace obs_of_ll obs_visible pi0` >-
    (fs [Abbr `tr0`,Abbr `pi0`,trace] >>
     Cases_on `ll` >> fs [obs_of_ll,FILTER_APPEND_DISTRIB]) >>
   `?pi'' tr''. pi' = pi0 ++ pi'' /\
     tr' = trace obs_of_ll obs_visible pi0 ++ tr'' /\
     trace obs_of_ll obs_visible pi' = tr'`
    by METIS_TAC [] >>
   rw [] >> fs [Abbr `pi0`,trace,FILTER_APPEND_DISTRIB]
  ]
 ]
QED

Theorem IO_bounded_execution_acc_LAST:
 !f_tran f_sem n stl stl' pos pi pi' tr tr'.
  IO_bounded_execution_acc f_tran f_sem stl pos n pi = SOME pi' ==>
  IO_bounded_trace_acc f_tran f_sem stl pos n tr = SOME (stl',tr') ==>
  SND (SND (LAST pi)) = stl ==>
  SND (SND (LAST pi')) = stl'
Proof
 strip_tac >> strip_tac >>
 Induct_on `n` >>
 Cases_on `stl` >> rename1 `State_st_list l s cs fs` >-
 fs [IO_bounded_trace_acc,IO_bounded_execution_acc] >>
 once_rewrite_tac [IO_bounded_trace_acc,IO_bounded_execution_acc] >>
 fs [] >> rw [] >>
 Cases_on `DROP pos l` >> fs [] >> rw [] >>
 Cases_on `h` >>
 rename1 `i_assign t' c mop::l'` >> rename1 `i_assign t c mop` >>
 fs [] >>
 Cases_on `FLOOKUP s t` >> fs [] >-
  (Cases_on `f_sem c s` >> fs [] >>
   rename1 `f_sem c s = SOME v` >>
   Cases_on `v = val_false` >> fs [] >-
   METIS_TAC [] >>
   Cases_on `sem_instr_exe f_sem (i_assign t c mop) (State_st_list l s cs fs)` >> fs [] >>
   Cases_on `x` >> rename1 `(v',obs)` >> fs [] >>
   Cases_on `OoO_Exe_list_instr_not_stored_guard_true_sem_instr (State_st_list l s cs fs) (i_assign t c mop) v' obs` >>
   fs [] >> rename1 `(ll,stl)` >>
   Cases_on `mop` >> fs [] >| [
    Q.ABBREV_TAC `pi0 = pi ++ [(State_st_list l s cs fs,ll,stl)]` >>
    Cases_on `obs_visible (obs_of_ll ll)` >> fs [] >-
     (`SND (SND (LAST pi0)) = stl` by rw [Abbr `pi0`] >>
      METIS_TAC []) >>    
    `SND (SND (LAST pi0)) = stl` by rw [Abbr `pi0`] >>
    METIS_TAC [],

    Q.ABBREV_TAC `pi0 = pi ++ [(State_st_list l s cs fs,ll,stl)]` >>
    Cases_on `obs_visible (obs_of_ll ll)` >> fs [] >-
     (`SND (SND (LAST pi0)) = stl` by rw [Abbr `pi0`] >>
      METIS_TAC []) >>    
    `SND (SND (LAST pi0)) = stl` by rw [Abbr `pi0`] >>
    METIS_TAC [],

    Cases_on `r` >> fs [] >| [
     Cases_on `OoO_Ftc_list_stored f_tran f_sem stl t v'` >> fs [] >>
     Cases_on `x` >> fs [] >> rename1 `(stl,ll1,stl1)` >>
     Q.ABBREV_TAC `pi0 = pi ++ [(State_st_list l s cs fs,ll,stl); (stl,ll1,stl1)]` >>
     Cases_on `obs_visible (obs_of_ll ll)` >> fs [] >-
      (`SND (SND (LAST pi0)) = stl1` by rw [Abbr `pi0`] >>
       METIS_TAC []) >>
     `SND (SND (LAST pi0)) = stl1` by rw [Abbr `pi0`] >>
     METIS_TAC [],

     Q.ABBREV_TAC `pi0 = pi ++ [(State_st_list l s cs fs,ll,stl)]` >>
     Cases_on `obs_visible (obs_of_ll ll)` >> fs [] >-
      (`SND (SND (LAST pi0)) = stl` by rw [Abbr `pi0`] >>
       METIS_TAC []) >>
     `SND (SND (LAST pi0)) = stl` by rw [Abbr `pi0`] >>
     METIS_TAC [],

     rename1 `o_store res_MEM ta tv` >>
     Cases_on `OoO_Cmt_list_stored f_sem stl t ta tv` >> fs [] >>
     Cases_on `x` >> fs [] >> rename1 `(ll1,stl1)` >>
     Q.ABBREV_TAC `pi0 = pi ++ [(State_st_list l s cs fs,ll,stl); (stl,ll1,stl1)]` >>
     Cases_on `obs_visible (obs_of_ll ll)` >> fs [] >-
      (`SND (SND (LAST pi0)) = stl1` by rw [Abbr `pi0`] >>
       METIS_TAC []) >>
     `SND (SND (LAST pi0)) = stl1` by rw [Abbr `pi0`] >>
     METIS_TAC []
    ]
   ]) >>
 Cases_on `mop` >> fs [] >| [
  METIS_TAC [],

  METIS_TAC [],

  rename1 `FLOOKUP s t = SOME v` >>
  Cases_on `r` >> fs [] >| [
   Cases_on `MEM t fs` >> fs [] >- METIS_TAC [] >>
   Cases_on `OoO_Ftc_list_stored_incomplete f_tran f_sem (State_st_list l s cs fs) t v` >> fs [] >>
   Cases_on `x` >> fs [] >> rename1 `(ll,stl)` >>
   Q.ABBREV_TAC `pi0 = pi ++ [(State_st_list l s cs fs,ll,stl)]` >>   
   `SND (SND (LAST pi0)) = stl` by rw [Abbr `pi0`] >>
   METIS_TAC [],

   METIS_TAC [],

   rename1 `o_store res_MEM ta tv` >>
   Cases_on `MEM t cs` >> fs [] >- METIS_TAC [] >>
   Cases_on `OoO_Cmt_list_stored_incomplete f_sem (State_st_list l s cs fs) t ta tv` >> fs [] >>
   Cases_on `x` >> fs [] >> rename1 `(ll,stl)` >>   
   Q.ABBREV_TAC `pi0 = pi ++ [(State_st_list l s cs fs,ll,stl)]` >>   
   `SND (SND (LAST pi0)) = stl` by rw [Abbr `pi0`] >>
   METIS_TAC []
  ]
 ]
QED

(* TODO: generalize to arbitrary sem_expr, translate_val_list *)
Theorem IO_bounded_trace_acc_empty_LAST:
 !n l s cs fs pos i il pi stl' tr.
  DROP pos l = i::il ==>
  ~(Completed_list sem_expr (State_st_list l s cs fs) i) ==>
  IO_bounded_execution_acc translate_val_list sem_expr (State_st_list l s cs fs) pos (SUC n) [] = SOME pi ==>
  IO_bounded_trace_acc translate_val_list sem_expr (State_st_list l s cs fs) pos (SUC n) [] = SOME (stl',tr) ==>
  SND (SND (LAST pi)) = stl'
Proof
 once_rewrite_tac [IO_bounded_execution_acc,IO_bounded_trace_acc] >>
 fs [] >> rw [] >>
 Cases_on `i` >> rename1 `i_assign t c mop` >> fs [] >>
 Cases_on `FLOOKUP s t` >> fs [] >> Cases_on `mop` >> fs [Completed_list] >| [
  Cases_on `sem_expr c s` >> fs [] >>
  rename1 `v <> val_false` >>
  Cases_on `v = val_false` >> fs [] >>
  Cases_on `sem_instr_exe sem_expr (i_assign t c (o_internal e)) (State_st_list l s cs fs)` >> fs [] >>
  Cases_on `x` >> fs [] >> rename1 `(v',obs)` >>
  Cases_on `OoO_Exe_list_instr_not_stored_guard_true_sem_instr
   (State_st_list l s cs fs) (i_assign t c (o_internal e)) v' obs` >>
  fs [] >> rename1 `(ll,stl)` >>  
  Cases_on `obs_visible (obs_of_ll ll)` >> fs [] >-
   (`SND (SND (LAST [(State_st_list l s cs fs,ll,stl)])) = stl` by fs [] >>
    METIS_TAC [IO_bounded_execution_acc_LAST]) >>
  `SND (SND (LAST [(State_st_list l s cs fs,ll,stl)])) = stl` by fs [] >>
  METIS_TAC [IO_bounded_execution_acc_LAST],

  Cases_on `sem_expr c s` >> fs [] >>
  rename1 `v <> val_false` >>
  Cases_on `v = val_false` >> fs [] >>
  Cases_on `sem_instr_exe sem_expr (i_assign t c (o_load r n')) (State_st_list l s cs fs)` >> fs [] >>
  Cases_on `x` >> fs [] >> rename1 `(v',obs)` >>
  Cases_on `OoO_Exe_list_instr_not_stored_guard_true_sem_instr (State_st_list l s cs fs) (i_assign t c (o_load r n')) v' obs` >>
  fs [] >> rename1 `(ll,stl)` >>
  Cases_on `obs_visible (obs_of_ll ll)` >> fs [] >-
   (`SND (SND (LAST [(State_st_list l s cs fs,ll,stl)])) = stl` by fs [] >>
    METIS_TAC [IO_bounded_execution_acc_LAST]) >>
  `SND (SND (LAST [(State_st_list l s cs fs,ll,stl)])) = stl` by fs [] >>
  METIS_TAC [IO_bounded_execution_acc_LAST],

  Cases_on `sem_expr c s` >> fs [] >>
  rename1 `v <> val_false` >>
  Cases_on `v = val_false` >> Cases_on `r` >> fs [Completed_list] >| [
   rename1 `o_store res_PC ta tv` >>
   Cases_on `sem_instr_exe sem_expr (i_assign t c (o_store res_PC ta tv)) (State_st_list l s cs fs)` >> fs [] >>
   Cases_on `x` >> fs [] >> rename1 `(v',obs)` >>
   Cases_on `OoO_Exe_list_instr_not_stored_guard_true_sem_instr (State_st_list l s cs fs) (i_assign t c (o_store res_PC ta tv)) v' obs` >> fs [] >>
   rename1 `(ll,stl)` >>
   Cases_on `OoO_Ftc_list_stored translate_val_list sem_expr stl t v'` >> fs [] >>
   Cases_on `x` >> fs [] >>
   rename1 `(ll1,stl1)` >>   
   Cases_on `obs_visible (obs_of_ll ll)` >> fs [] >-
    (`SND (SND (LAST[(State_st_list l s cs fs,ll,stl);(stl,ll1,stl1)])) = stl1` by fs [] >>
     METIS_TAC [IO_bounded_execution_acc_LAST]) >>
   `SND (SND (LAST [(State_st_list l s cs fs,ll,stl);(stl,ll1,stl1)])) = stl1` by fs [] >>
   METIS_TAC [IO_bounded_execution_acc_LAST],

   rename1 `o_store res_REG ta tv` >>
   Cases_on `sem_instr_exe sem_expr (i_assign t c (o_store res_REG ta tv)) (State_st_list l s cs fs)` >> fs [] >>
   Cases_on `x` >> rename1 `(v',obs)` >> fs [] >>
   Cases_on `OoO_Exe_list_instr_not_stored_guard_true_sem_instr (State_st_list l s cs fs)
    (i_assign t c (o_store res_REG ta tv)) v' obs` >>
   fs [] >> rename1 `(ll,stl)` >>   
   Cases_on `obs_visible (obs_of_ll ll)` >> fs [] >-
    (`SND (SND (LAST [(State_st_list l s cs fs,ll,stl)])) = stl` by fs [] >>
     METIS_TAC [IO_bounded_execution_acc_LAST]) >>
   `SND (SND (LAST [(State_st_list l s cs fs,ll,stl)])) = stl` by fs [] >>
   METIS_TAC [IO_bounded_execution_acc_LAST],

   rename1 `o_store res_MEM ta tv` >>
   Cases_on `sem_instr_exe sem_expr (i_assign t c (o_store res_MEM ta tv)) (State_st_list l s cs fs)` >> fs [] >>
   Cases_on `x` >> fs [] >> rename1 `(v',obs)` >>
   Cases_on `OoO_Exe_list_instr_not_stored_guard_true_sem_instr (State_st_list l s cs fs) (i_assign t c (o_store res_MEM ta tv)) v' obs` >> fs [] >>
   rename1 `(ll,stl)` >>
   Cases_on `OoO_Cmt_list_stored sem_expr stl t ta tv` >> fs [] >>
   Cases_on `x` >> fs [] >> rename1 `(ll1,stl1)` >>   
   Cases_on `obs_visible (obs_of_ll ll)` >> fs [] >-
    (`SND (SND (LAST [(State_st_list l s cs fs,ll,stl);(stl,ll1,stl1)])) = stl1` by fs [] >>
     METIS_TAC [IO_bounded_execution_acc_LAST]) >>
   `SND (SND (LAST [(State_st_list l s cs fs,ll,stl);(stl,ll1,stl1)])) = stl1` by fs [] >>
   METIS_TAC [IO_bounded_execution_acc_LAST]
  ],

  rename1 `o_store r ta tv` >>
  rename1 `FLOOKUP s t = SOME v` >>
  Cases_on `r` >> fs [Completed_list] >-
   (Cases_on `MEM t fs` >> fs [] >>
    Cases_on `OoO_Ftc_list_stored_incomplete translate_val_list sem_expr (State_st_list l s cs fs) t v` >> fs [] >>
    Cases_on `x` >> fs [] >>
    rename1 `(ll,stl)` >>
    `SND (SND (LAST [(State_st_list l s cs fs,ll,stl)])) = stl` by fs [] >>
    METIS_TAC [IO_bounded_execution_acc_LAST]) >>
  Cases_on `MEM t cs` >> fs [] >>
  Cases_on `OoO_Cmt_list_stored_incomplete sem_expr (State_st_list l s cs fs) t ta tv` >> fs [] >>
  Cases_on `x` >> fs [] >>
  rename1 `(ll,stl)` >>
  `SND (SND (LAST [(State_st_list l s cs fs,ll,stl)])) = stl` by fs [] >>
  METIS_TAC [IO_bounded_execution_acc_LAST]
 ]
QED

Theorem IO_bounded_execution_trace_acc_SOME:
 !f_tran f_sem n stl pos pi pi' tr.
  IO_bounded_execution_acc f_tran f_sem stl pos n pi = SOME pi' ==>
  ?stl' tr'. IO_bounded_trace_acc f_tran f_sem stl pos n tr = SOME (stl',tr')
Proof
 Induct_on `n` >>
 Cases_on `stl` >> rename1 `State_st_list l s cs fs` >-
 fs [IO_bounded_trace_acc,IO_bounded_execution_acc] >>
 once_rewrite_tac [IO_bounded_trace_acc,IO_bounded_execution_acc] >>
 fs [] >> rw [] >>
 Cases_on `DROP pos l` >> fs [] >> rw [] >>
 Cases_on `h` >>
 rename1 `i_assign t' c mop::l'` >> rename1 `i_assign t c mop` >>
 fs [] >>
 Cases_on `FLOOKUP s t` >> fs [] >-
  (Cases_on `f_sem c s` >> fs [] >>
   rename1 `f_sem c s = SOME v` >>
   Cases_on `v = val_false` >> fs [] >-
   METIS_TAC [] >>
   Cases_on `sem_instr_exe f_sem (i_assign t c mop) (State_st_list l s cs fs)` >> fs [] >>
   Cases_on `x` >> rename1 `(v',obs)` >> fs [] >>
   Cases_on `OoO_Exe_list_instr_not_stored_guard_true_sem_instr (State_st_list l s cs fs) (i_assign t c mop) v' obs` >>
   fs [] >> rename1 `(ll,stl)` >>
   Cases_on `mop` >> fs [] >| [
    Cases_on `obs_visible (obs_of_ll ll)` >> fs [] >> METIS_TAC [],
    Cases_on `obs_visible (obs_of_ll ll)` >> fs [] >> METIS_TAC [],
    Cases_on `r` >> fs [] >| [
     Cases_on `OoO_Ftc_list_stored f_tran f_sem stl t v'` >> fs [] >>
     Cases_on `x` >> fs [] >> rename1 `(ll',stl')` >>
     Cases_on `obs_visible (obs_of_ll ll)` >> fs [] >> METIS_TAC [],
     Cases_on `obs_visible (obs_of_ll ll)` >> fs [] >> METIS_TAC [],
     rename1 `o_store res_MEM ta tv` >>
     Cases_on `OoO_Cmt_list_stored f_sem stl t ta tv` >> fs [] >>
     Cases_on `x` >> fs [] >> rename1 `(ll',stl')` >>
     Cases_on `obs_visible (obs_of_ll ll)` >> fs [] >> METIS_TAC []
    ]
   ]) >>
 Cases_on `mop` >> fs [] >| [
  METIS_TAC [],
  METIS_TAC [],
  rename1 `FLOOKUP s t = SOME v` >>
  Cases_on `r` >> fs [] >| [
   Cases_on `MEM t fs` >> fs [] >- METIS_TAC [] >>
   Cases_on `OoO_Ftc_list_stored_incomplete f_tran f_sem (State_st_list l s cs fs) t v` >> fs [] >>
   Cases_on `x` >> fs [] >> rename1 `(ll,stl)` >>
   METIS_TAC [],
   METIS_TAC [],
   Cases_on `MEM t cs` >> fs [] >- METIS_TAC [] >>
   rename1 `o_store res_MEM ta tv` >>
   Cases_on `OoO_Cmt_list_stored_incomplete f_sem (State_st_list l s cs fs) t ta tv` >> fs [] >>
   Cases_on `x` >> fs [] >> rename1 `(ll,stl)` >>
   METIS_TAC []
  ]
 ]
QED

Theorem IO_bounded_trace_execution_acc_SOME:
 !f_tran f_sem n stl stl0 pos tr tr' pi.
  IO_bounded_trace_acc f_tran f_sem stl pos n tr = SOME (stl0,tr') ==>
  ?pi'. IO_bounded_execution_acc f_tran f_sem stl pos n pi = SOME pi'
Proof
 Induct_on `n` >>
 Cases_on `stl` >> rename1 `State_st_list l s cs fs` >-
 fs [IO_bounded_trace_acc,IO_bounded_execution_acc] >>
 once_rewrite_tac [IO_bounded_trace_acc,IO_bounded_execution_acc] >>
 fs [] >> rw [] >>
 Cases_on `DROP pos l` >> fs [] >> rw [] >>
 Cases_on `h` >>
 rename1 `i_assign t' c mop::l'` >> rename1 `i_assign t c mop` >>
 fs [] >>
 Cases_on `FLOOKUP s t` >> fs [] >-
  (Cases_on `f_sem c s` >> fs [] >>
   rename1 `f_sem c s = SOME v` >>
   Cases_on `v = val_false` >> fs [] >-
   METIS_TAC [] >>
   Cases_on `sem_instr_exe f_sem (i_assign t c mop) (State_st_list l s cs fs)` >> fs [] >>
   Cases_on `x` >> rename1 `(v',obs)` >> fs [] >>
   Cases_on `OoO_Exe_list_instr_not_stored_guard_true_sem_instr (State_st_list l s cs fs) (i_assign t c mop) v' obs` >>
   fs [] >>
   rename1 `OoO_Exe_list_instr_not_stored_guard_true_sem_instr
    (State_st_list l s cs fs) (i_assign t c mop) v' obs = (ll,stl)` >>
   Cases_on `mop` >> fs [] >| [
    Cases_on `obs_visible (obs_of_ll ll)` >> fs [] >> METIS_TAC [],
    Cases_on `obs_visible (obs_of_ll ll)` >> fs [] >> METIS_TAC [],
    Cases_on `r` >> fs [] >| [
     Cases_on `OoO_Ftc_list_stored f_tran f_sem stl t v'` >> fs [] >>
     Cases_on `x` >> fs [] >> rename1 `SOME (ll',stl')` >>
     Cases_on `obs_visible (obs_of_ll ll)` >> fs [] >> METIS_TAC [],
     Cases_on `obs_visible (obs_of_ll ll)` >> fs [] >> METIS_TAC [],
     rename1 `o_store res_MEM ta tv` >>
     Cases_on `OoO_Cmt_list_stored f_sem stl t ta tv` >> fs [] >>
     Cases_on `x` >> fs [] >> rename1 `SOME (ll',stl')` >>
     Cases_on `obs_visible (obs_of_ll ll)` >> fs [] >> METIS_TAC []
    ]
   ]) >>
 Cases_on `mop` >> fs [] >| [
  METIS_TAC [],
  METIS_TAC [],
  rename1 `FLOOKUP s t = SOME v` >>
  Cases_on `r` >> fs [] >| [
   Cases_on `MEM t fs` >> fs [] >- METIS_TAC [] >>
   Cases_on `OoO_Ftc_list_stored_incomplete f_tran f_sem (State_st_list l s cs fs) t v` >> fs [] >>
   Cases_on `x` >> fs [] >> rename1 `SOME (ll,stl)` >>
   METIS_TAC [],
   METIS_TAC [],
   Cases_on `MEM t cs` >> fs [] >- METIS_TAC [] >>
   rename1 `o_store res_MEM ta tv` >>
   Cases_on `OoO_Cmt_list_stored_incomplete f_sem (State_st_list l s cs fs) t ta tv` >> fs [] >>
   Cases_on `x` >> fs [] >> rename1 `SOME (ll,stl)` >>
   METIS_TAC []
  ]
 ]
QED

(* ------------------------------ *)
(* IO_bounded_trace_aux soundness *)
(* ------------------------------ *)

Theorem IO_bounded_trace_aux_for_execution:
 !f_tran f_sem stl pos n pi.
  IO_bounded_execution f_tran f_sem stl pos n = SOME pi ==>
  ?stl'. IO_bounded_trace_aux f_tran f_sem stl pos n =
   SOME (stl',trace obs_of_ll obs_visible pi)
Proof
 rw [IO_bounded_execution,IO_bounded_trace_aux] >>
 `?stl' tr. IO_bounded_trace_acc f_tran f_sem stl (PRE pos) n [] = SOME (stl',tr)`
  by METIS_TAC [IO_bounded_execution_trace_acc_SOME] >>
 Q.EXISTS_TAC `stl'` >>
 MP_TAC (Q.SPECL 
  [`f_tran`, `f_sem`, `n`, `stl`, `stl'`,
   `PRE pos`, `[]`, `pi`, `[]`, `tr`]
  IO_bounded_execution_acc_trace_acc_eq) >>
 rw [] >>
 fs [trace]
QED

Theorem IO_bounded_execution_for_trace_aux:
 !f_tran f_sem stl stl' pos n tr.
  IO_bounded_trace_aux f_tran f_sem stl pos n = SOME (stl',tr) ==>
  ?pi. IO_bounded_execution f_tran f_sem stl pos n = SOME pi /\
   tr = trace obs_of_ll obs_visible pi
Proof
 rw [IO_bounded_execution,IO_bounded_trace_aux] >>
 `?pi. IO_bounded_execution_acc f_tran f_sem stl (PRE pos) n [] = SOME pi`
  by METIS_TAC [IO_bounded_trace_execution_acc_SOME] >>
 Q.EXISTS_TAC `pi` >>
 MP_TAC (Q.SPECL 
  [`f_tran`, `f_sem`, `n`, `stl`, `stl'`,
   `PRE pos`, `[]`, `pi`, `[]`, `tr`]
  IO_bounded_execution_acc_trace_acc_eq) >>
 rw [] >>
 fs [trace]
QED

Theorem trace_obs_of_ll_obs_of_l_MAP_step_list_to_step:
 !pi. trace obs_of_ll obs_visible pi = trace obs_of_l obs_visible (MAP step_list_to_step pi)
Proof
 Induct_on `pi` >> fs [trace,obs_of_l,obs_of_ll] >>
 Cases_on `h` >> Cases_on `r` >> rename1 `(stl,ll,stl')` >>
 rw [obs_of_l,obs_of_ll,step_list_to_step] >> Cases_on `ll` >>
 fs [ll_to_l,obs_of_l,obs_of_ll]
QED

Theorem IO_bounded_trace_aux_out_of_order_step_list_sound:
 !l s cs fs pos n i il stl tr.
  State_st_list_well_formed_ok (State_st_list l s cs fs) ==>
  DROP (PRE pos) l = i::il ==>
  ~(Completed_list sem_expr (State_st_list l s cs fs) i) ==>
  IO_bounded_trace_aux translate_val_list sem_expr (State_st_list l s cs fs) pos (SUC n) =
   SOME (stl,tr) ==>
  ?pi. FST (HD pi) = State_st_list l s cs fs /\
   step_execution out_of_order_step_list pi /\
   tr = trace obs_of_ll obs_visible pi /\
   SND (SND (LAST pi)) = stl
Proof
 rw [] >>
 `?pi. IO_bounded_execution translate_val_list sem_expr
   (State_st_list l s cs fs) pos (SUC n) = SOME pi /\
   tr = trace obs_of_ll obs_visible pi`
  by METIS_TAC [IO_bounded_execution_for_trace_aux] >>
 `FST (HD pi) = State_st_list l s cs fs /\
  step_execution out_of_order_step_list pi`
  by METIS_TAC [IO_bounded_execution_out_of_order_step_list_sound] >>
 sg `SND (SND (LAST pi)) = stl` >-
  (fs [IO_bounded_execution,IO_bounded_trace_aux] >>
   METIS_TAC [IO_bounded_trace_acc_empty_LAST]) >>
 Q.EXISTS_TAC `pi` >> rw []
QED

Theorem IO_bounded_trace_aux_in_order_step_list_sound:
 translate_val_list_SORTED ==>
 !l s cs fs pos n i il stl tr.
  State_st_list_well_formed_ok (State_st_list l s cs fs) ==>
  SORTED bound_name_instr_le l ==>
  Completed_list_up_to sem_expr (State_st_list l s cs fs) (PRE pos) ==>
  DROP (PRE pos) l = i::il ==>
  ~(Completed_list sem_expr (State_st_list l s cs fs) i) ==>
  IO_bounded_trace_aux translate_val_list sem_expr (State_st_list l s cs fs) pos (SUC n) =
   SOME (stl,tr) ==>
  ?pi. FST (HD pi) = State_st_list l s cs fs /\
   step_execution in_order_step_list pi /\
   tr = trace obs_of_ll obs_visible pi /\
   Completed_list_up_to sem_expr (SND (SND (LAST pi))) (PRE pos + SUC n) /\
   SND (SND (LAST pi)) = stl
Proof
 rw [] >>
 `?pi. IO_bounded_execution translate_val_list sem_expr
   (State_st_list l s cs fs) pos (SUC n) = SOME pi /\
   tr = trace obs_of_ll obs_visible pi`
  by METIS_TAC [IO_bounded_execution_for_trace_aux] >>
 `FST (HD pi) = State_st_list l s cs fs /\
  step_execution in_order_step_list pi /\
  Completed_list_up_to sem_expr (SND (SND (LAST pi))) (PRE pos + SUC n)`
  by METIS_TAC [IO_bounded_execution_in_order_step_list_sound] >>
 sg `SND (SND (LAST pi)) = stl` >-
  (fs [IO_bounded_execution,IO_bounded_trace_aux] >>
   METIS_TAC [IO_bounded_trace_acc_empty_LAST]) >>
 Q.EXISTS_TAC `pi` >> rw []
QED

(* TODO: out_of_order and in_order versions with MAP, easily derivable *)

(* -------------------------- *)
(* IO_bounded_trace soundness *)
(* -------------------------- *)

Theorem IO_bounded_trace_for_execution:
 !f_tran f_sem stl pos n pi.
  IO_bounded_execution f_tran f_sem stl pos n = SOME pi ==>
  IO_bounded_trace f_tran f_sem stl pos n =
   SOME (trace obs_of_ll obs_visible pi)
Proof
 rw [IO_bounded_trace] >>
 `?stl'. IO_bounded_trace_aux f_tran f_sem stl pos n =
   SOME (stl',trace obs_of_ll obs_visible pi)`
  by METIS_TAC [IO_bounded_trace_aux_for_execution] >>
 rw []
QED

Theorem IO_bounded_execution_for_trace:
 !f_tran f_sem stl pos n tr.
  IO_bounded_trace f_tran f_sem stl pos n = SOME tr ==>
  ?pi. IO_bounded_execution f_tran f_sem stl pos n = SOME pi /\
   tr = trace obs_of_ll obs_visible pi
Proof
 rw [IO_bounded_trace] >>
 Cases_on `IO_bounded_trace_aux f_tran f_sem stl pos n` >> fs [] >>
 Cases_on `x` >> fs [] >> rw [] >> rename1 `(stl',tr)` >>
 `?pi. IO_bounded_execution f_tran f_sem stl pos n = SOME pi /\
   tr = trace obs_of_ll obs_visible pi`
   by METIS_TAC [IO_bounded_execution_for_trace_aux] >>
 rw []
QED

(* FIXME: replace with NTH variant just below? *)
Theorem IO_bounded_trace_out_of_order_step_list_sound:
 !l s cs fs pos n i il tr.
  State_st_list_well_formed_ok (State_st_list l s cs fs) ==>
  DROP (PRE pos) l = i::il ==>
  ~(Completed_list sem_expr (State_st_list l s cs fs) i) ==>
  IO_bounded_trace translate_val_list sem_expr (State_st_list l s cs fs) pos (SUC n) = SOME tr ==>
  ?pi. FST (HD pi) = State_st_list l s cs fs /\
   step_execution out_of_order_step_list pi /\
   tr = trace obs_of_ll obs_visible pi
Proof
 rw [IO_bounded_trace] >>
 Cases_on `IO_bounded_trace_aux translate_val_list sem_expr
  (State_st_list l s cs fs) pos (SUC n)` >> fs [] >>
 Cases_on `x` >> fs [] >> rw [] >>
 METIS_TAC [IO_bounded_trace_aux_out_of_order_step_list_sound]
QED

Theorem IO_bounded_trace_out_of_order_step_list_sound_NTH:
  !stl pos n i tr.
  State_st_list_well_formed_ok stl ==>
  NTH (PRE pos) (state_program_list stl) = SOME i ==>
  ~(Completed_list sem_expr stl i) ==>
  IO_bounded_trace translate_val_list sem_expr stl pos (SUC n) = SOME tr ==>
  ?pi. FST (HD pi) = stl /\
   step_execution out_of_order_step_list pi /\
   tr = trace obs_of_ll obs_visible pi
Proof
 Cases_on `stl` >>
 rw [state_program_list] >>
 METIS_TAC [
  NTH_SOME_DROP,
  IO_bounded_trace_out_of_order_step_list_sound
 ]
QED

(* FIXME: replace with NTH variant just below? *)
Theorem IO_bounded_trace_out_of_order_step_sound:
 !l s cs fs pos n i il tr.
  State_st_list_well_formed_ok (State_st_list l s cs fs) ==>
  DROP (PRE pos) l = i::il ==>
  ~(Completed_list sem_expr (State_st_list l s cs fs) i) ==>
  IO_bounded_trace translate_val_list sem_expr (State_st_list l s cs fs) pos (SUC n) = SOME tr ==>
  ?pi. FST (HD pi) = State_st_list l s cs fs /\
   step_execution out_of_order_step (MAP step_list_to_step pi) /\
   tr = trace obs_of_ll obs_visible pi
Proof
 METIS_TAC [
  step_execution_out_of_order_step_list_step,
  IO_bounded_trace_out_of_order_step_list_sound
 ]
QED

Theorem IO_bounded_trace_out_of_order_step_sound_NTH:
 !stl pos n i tr.
  State_st_list_well_formed_ok stl ==>
  NTH (PRE pos) (state_program_list stl) = SOME i ==>
  ~(Completed_list sem_expr stl i) ==>
  IO_bounded_trace translate_val_list sem_expr stl pos (SUC n) = SOME tr ==>
  ?pi. FST (HD pi) = stl /\
   step_execution out_of_order_step (MAP step_list_to_step pi) /\
   tr = trace obs_of_ll obs_visible pi
Proof
 Cases_on `stl` >>
 rw [state_program_list] >>
 METIS_TAC [
  NTH_SOME_DROP,
  IO_bounded_trace_out_of_order_step_sound
 ]
QED

(* FIXME: replace with NTH variant just below? *)
Theorem IO_bounded_trace_in_order_step_list_sound:
 translate_val_list_SORTED ==>
 !l s cs fs pos n i il tr.
  State_st_list_well_formed_ok (State_st_list l s cs fs) ==>
  SORTED bound_name_instr_le l ==>
  Completed_list_up_to sem_expr (State_st_list l s cs fs) (PRE pos) ==>
  DROP (PRE pos) l = i::il ==>
  ~(Completed_list sem_expr (State_st_list l s cs fs) i) ==>
  IO_bounded_trace translate_val_list sem_expr (State_st_list l s cs fs) pos (SUC n) = SOME tr ==>
  ?pi. FST (HD pi) = State_st_list l s cs fs /\
   step_execution in_order_step_list pi /\
   tr = trace obs_of_ll obs_visible pi /\
   Completed_list_up_to sem_expr (SND (SND (LAST pi))) (PRE pos + SUC n)
Proof
 rw [IO_bounded_trace] >>
 Cases_on `IO_bounded_trace_aux translate_val_list sem_expr
  (State_st_list l s cs fs) pos (SUC n)` >> fs [] >>
 Cases_on `x` >> fs [] >> rw [] >>
 METIS_TAC [IO_bounded_trace_aux_in_order_step_list_sound]
QED

Theorem IO_bounded_trace_in_order_step_list_sound_NTH:
 translate_val_list_SORTED ==>
 !stl pos n i tr.
  State_st_list_well_formed_ok stl ==>
  SORTED bound_name_instr_le (state_program_list stl) ==>
  Completed_list_up_to sem_expr stl (PRE pos) ==>
  NTH (PRE pos) (state_program_list stl) = SOME i ==>
  ~(Completed_list sem_expr stl i) ==>
  IO_bounded_trace translate_val_list sem_expr stl pos (SUC n) = SOME tr ==>
  ?pi. FST (HD pi) = stl /\
   step_execution in_order_step_list pi /\
   tr = trace obs_of_ll obs_visible pi /\
   Completed_list_up_to sem_expr (SND (SND (LAST pi))) (PRE pos + SUC n)
Proof
 strip_tac >>
 Cases_on `stl` >>
 rw [state_program_list] >>
 METIS_TAC [
  NTH_SOME_DROP,
  IO_bounded_trace_in_order_step_list_sound
 ]
QED

(* FIXME: switch to NTH as version below? *)
Theorem IO_bounded_trace_in_order_step_sound:
 translate_val_list_SORTED ==>
 !l s cs fs pos n i il tr.
  State_st_list_well_formed_ok (State_st_list l s cs fs) ==>
  SORTED bound_name_instr_le l ==>
  Completed_list_up_to sem_expr (State_st_list l s cs fs) (PRE pos) ==>
  DROP (PRE pos) l = i::il ==>
  ~(Completed_list sem_expr (State_st_list l s cs fs) i) ==>
  IO_bounded_trace translate_val_list sem_expr (State_st_list l s cs fs) pos (SUC n) = SOME tr ==>
  ?pi. FST (HD pi) = State_st_list l s cs fs /\
   step_execution in_order_step (MAP step_list_to_step pi) /\
   tr = trace obs_of_ll obs_visible pi /\
   Completed_list_up_to sem_expr (SND (SND (LAST pi))) (PRE pos + SUC n)
Proof
 METIS_TAC [
  step_execution_in_order_step_list_step,
  IO_bounded_trace_in_order_step_list_sound
 ]
QED

Theorem IO_bounded_trace_in_order_step_sound_NTH:
 translate_val_list_SORTED ==>
 !stl pos n i tr.
  State_st_list_well_formed_ok stl ==>
  SORTED bound_name_instr_le (state_program_list stl) ==>
  Completed_list_up_to sem_expr stl (PRE pos) ==>
  NTH (PRE pos) (state_program_list stl) = SOME i ==>
  ~(Completed_list sem_expr stl i) ==>
  IO_bounded_trace translate_val_list sem_expr stl pos (SUC n) = SOME tr ==>
  ?pi. FST (HD pi) = stl /\
   step_execution in_order_step (MAP step_list_to_step pi) /\
   tr = trace obs_of_ll obs_visible pi /\
   Completed_list_up_to sem_expr (SND (SND (LAST pi))) (PRE pos + SUC n)
Proof
 strip_tac >>
 Cases_on `stl` >>
 rw [state_program_list] >>
 METIS_TAC [
  NTH_SOME_DROP,
  IO_bounded_trace_in_order_step_sound
 ]
QED

val _ = export_theory ();
