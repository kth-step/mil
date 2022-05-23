open HolKernel boolLib Parse bossLib wordsLib optionTheory wordsTheory finite_mapTheory pred_setTheory listTheory rich_listTheory sortingTheory ottTheory milUtilityTheory milTheory milSemanticsUtilityTheory milTracesTheory milMetaTheory milInitializationTheory milExecutableUtilityTheory milExecutableTransitionTheory milExecutableCompletenessTheory;

(* ======================================== *)
(* IO execution of bounded number of steps  *)
(* ======================================== *)

val _ = new_theory "milExecutableIO";

(* --------------------------------- *)
(* Function and property definitions *)
(* --------------------------------- *)

(* TODO: easy optimization to put transitions at head of exec, reverse the final list *)
Definition IO_bounded_execution_acc:
 IO_bounded_execution_acc
  (f_tran: v -> t -> i list)
  (f_sem: e -> (t |-> v) -> v option)
  (State_st_list l s cs fs) (pos:num) (n:num)
  (exec:(State_list # ll # State_list) list) :
 ((State_list # ll # State_list) list) option =
 case n of
 | 0 => SOME exec
 | SUC n' =>
   (case DROP pos l of
    | [] => SOME exec
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
                     IO_bounded_execution_acc f_tran f_sem stl' (SUC pos) n'
                      (exec++[(State_st_list l s cs fs,ll,stl);(stl,ll',stl')]))
                | o_store res_PC ta tv =>
                  (case OoO_Ftc_list_stored f_tran f_sem stl t v' of
                   | NONE => NONE
                   | SOME (ll',stl') =>
                     IO_bounded_execution_acc f_tran f_sem stl' (SUC pos) n'
                      (exec++[(State_st_list l s cs fs,ll,stl);(stl,ll',stl')]))
                | _ => (* instruction is completed, move on *)
                  IO_bounded_execution_acc f_tran f_sem stl (SUC pos) n'
                   (exec++[(State_st_list l s cs fs,ll,stl)]))
          else (* instruction is completed, move on *)
            IO_bounded_execution_acc f_tran f_sem (State_st_list l s cs fs) (SUC pos) n' exec)
      | SOME v =>
        (case mop of
         | o_store res_MEM ta tv =>
           if MEM t cs then (* instruction is completed, move on *)
             IO_bounded_execution_acc f_tran f_sem (State_st_list l s cs fs) (SUC pos) n' exec
           else
             (case OoO_Cmt_list_stored_incomplete f_sem (State_st_list l s cs fs) t ta tv of
             | NONE => NONE
             | SOME (ll,stl) => (* instruction is completed, move on *)
               IO_bounded_execution_acc f_tran f_sem stl (SUC pos) n'
                (exec++[(State_st_list l s cs fs,ll,stl)]))
         | o_store res_PC ta tv =>
           if MEM t fs then (* instruction is completed, move on *)
             IO_bounded_execution_acc f_tran f_sem (State_st_list l s cs fs) (SUC pos) n' exec
           else
             (case OoO_Ftc_list_stored_incomplete f_tran f_sem (State_st_list l s cs fs) t v of
              | NONE => NONE
              | SOME (ll,stl) => (* instruction is completed, move on *)
                IO_bounded_execution_acc f_tran f_sem stl (SUC pos) n'
                 (exec++[(State_st_list l s cs fs,ll,stl)]))
         | _ => (* instruction is completed, move on *)
           IO_bounded_execution_acc f_tran f_sem (State_st_list l s cs fs) (SUC pos) n' exec)))
End

(* FIXME: double check how PRE affects all theorem statements *)
Definition IO_bounded_execution:
 IO_bounded_execution
  (f_tran : v -> t -> i list)
  (f_sem: e -> (t |-> v) -> v option)
  (stl:State_list) (pos:num) (n:num) :
 ((State_list # ll # State_list) list) option =
  IO_bounded_execution_acc f_tran f_sem stl (PRE pos) n []
End

Definition step_execution_list_OoO_HD:
 step_execution_list_OoO_HD stl pi n =
  (FST (HD pi) = stl /\
   step_execution out_of_order_step_list pi /\
   LENGTH pi <= 2*n)
End

Definition step_execution_list_IO_HD:
 step_execution_list_IO_HD stl pi pos n =
  (FST (HD pi) = stl /\
   step_execution in_order_step_list pi /\
   Completed_list_up_to sem_expr (SND (SND (LAST pi))) (pos + n) /\
   LENGTH pi <= 2*n)
End

(* ----------------------- *)
(* Execution OoO soundness *)
(* ----------------------- *)

Theorem NO_DUPLICATES_FIND_instr:
 !l t i. 
  NO_DUPLICATES l ==>
  MEM i l ==>
  bound_name_instr i = t ==>
  FIND_instr t l = SOME i
Proof
 rw [] >>
 Cases_on `FIND_instr (bound_name_instr i) l` >-
 METIS_TAC [FIND_instr_eq_NONE,MEM_MAP,NO_DUPLICATES_bound_name_instr] >>
 METIS_TAC [FIND_instr_eq_SOME,NO_DUPLICATES_bound_name_instr]
QED

(* FIXME: extract lemma on one-step cases *)
Theorem IO_bounded_execution_acc_OoO_execution_sound:
 !n stl pos pi pi'.
  State_st_list_well_formed_ok stl ==>
  step_execution out_of_order_step_list pi ==>
  SND (SND (LAST pi)) = stl ==>
  IO_bounded_execution_acc translate_val_list sem_expr stl pos n pi = SOME pi' ==>
  ?pi''. pi' = pi ++ pi'' /\
   step_execution out_of_order_step_list pi' /\
   LENGTH pi'' <= 2*n
Proof
 Induct_on `n` >>
 Cases_on `stl` >> rename1 `State_st_list l s cs fs` >-
 fs [IO_bounded_execution_acc] >>
 once_rewrite_tac [IO_bounded_execution_acc] >>
 fs [] >> rw [] >>
 Cases_on `DROP pos l` >> fs [] >>
 Cases_on `h` >>
 rename1 `i_assign t' c mop::l'` >> rename1 `i_assign t c mop` >>
 fs [] >>
 Cases_on `FLOOKUP s t` >> fs [] >-
  (Cases_on `sem_expr c s` >> fs [] >>
   rename1 `sem_expr c s = SOME v` >>
   Cases_on `v = val_false` >> fs [] >-
    (`?pi''. pi' = pi ++ pi'' /\
       step_execution out_of_order_step_list pi' /\
       LENGTH pi'' <= 2 * n` by METIS_TAC [] >>
     Q.EXISTS_TAC `pi''` >> rw []) >>
   Cases_on `sem_instr_exe sem_expr (i_assign t c mop) (State_st_list l s cs fs)` >> fs [] >>
   Cases_on `x` >> rename1 `(v',obs)` >> fs [] >>
   Cases_on `OoO_Exe_list_instr_not_stored_guard_true_sem_instr
    (State_st_list l s cs fs) (i_assign t c mop) v' obs` >>
   fs [] >> rename1 `(ll,stl)` >>
   `MEM (i_assign t c mop) l` by METIS_TAC [DROP_HEAD_MEM] >>
   `State_st_list_well_formed_ok stl`
    by METIS_TAC [State_st_list_well_formed_ok_OoO_Exe_list_instr_not_stored_guard_true_sem_instr] >>
   `State_st_list_ok (State_st_list l s cs fs)` by fs [State_st_list_ok,State_st_list_well_formed_ok] >>
   `FIND_instr t l = SOME (i_assign t c mop)`
    by METIS_TAC [State_st_list_ok,NO_DUPLICATES_FIND_instr,bound_name_instr] >>
   `out_of_order_step_list (State_st_list l s cs fs) ll stl`
    by METIS_TAC [OoO_Exe_list_instr_not_stored_guard_true_sem_instr_SOME_out_of_order_step_list] >>
   `State_st_list_ok stl` by METIS_TAC [step_invariant,step_invariant_out_of_order_step_list_ok] >>
   Cases_on `mop` >> fs [] >| [
     Q.ABBREV_TAC `pi0 = pi ++ [(State_st_list l s cs fs,ll,stl)]` >>
     `State_st_list_well_formed_ok (SND (SND (LAST pi0)))` by fs [Abbr `pi0`] >>

     sg `step_execution out_of_order_step_list pi0` >-
      (fs [Abbr `pi0`,step_list_to_step] >>
       `pi <> []` by METIS_TAC [step_execution_not_empty_list] >>
       `pi = [] \/ ?e pi1. pi = SNOC e pi1` by fs [SNOC_CASES] >> fs [SNOC_APPEND] >>
       Cases_on `e'` >> fs [] >> Cases_on `r` >> rename1 `(stl1,ll1,stl2)` >>
       fs [step_list_to_step] >> rw [] >>
       `pi1 ++ [(stl1,ll1,State_st_list l s cs fs)] ++ [(State_st_list l s cs fs,ll,stl)] =
        pi1 ++ [(stl1,ll1,State_st_list l s cs fs);(State_st_list l s cs fs,ll,stl)]`
        by fs [] >>
       rw [] >> METIS_TAC [step_execution_rules]) >>

     `SND (SND (LAST pi0)) = stl` by fs [Abbr `pi0`] >>
     `?pi''. pi' = pi0 ++ pi'' /\
       step_execution out_of_order_step_list pi' /\
       LENGTH pi'' <= 2 * n` by METIS_TAC [] >>
     fs [Abbr `pi0`],

     Q.ABBREV_TAC `pi0 = pi ++ [(State_st_list l s cs fs,ll,stl)]` >>
     `State_st_list_well_formed_ok (SND (SND (LAST pi0)))` by fs [Abbr `pi0`] >>

     sg `step_execution out_of_order_step_list pi0` >-
      (fs [Abbr `pi0`,step_list_to_step] >>
       `pi <> []` by METIS_TAC [step_execution_not_empty_list] >>
       `pi = [] \/ ?e pi1. pi = SNOC e pi1` by fs [SNOC_CASES] >> fs [SNOC_APPEND] >>
       Cases_on `e` >> fs [] >> Cases_on `r'` >> rename1 `(stl1,ll1,stl2)` >>
       fs [step_list_to_step] >> rw [] >>
       `pi1 ++ [(stl1,ll1,State_st_list l s cs fs)] ++ [(State_st_list l s cs fs,ll,stl)] =
        pi1 ++ [(stl1,ll1,State_st_list l s cs fs);(State_st_list l s cs fs,ll,stl)]`
        by fs [] >>
       rw [] >> METIS_TAC [step_execution_rules]) >>
     `SND (SND (LAST pi0)) = stl` by fs [Abbr `pi0`] >>
     `?pi''. pi' = pi0 ++ pi'' /\
       step_execution out_of_order_step_list pi' /\
       LENGTH pi'' <= 2 * n` by METIS_TAC [] >>
     fs [Abbr `pi0`],

     Cases_on `r` >> fs [] >| [
      Cases_on `OoO_Ftc_list_stored translate_val_list sem_expr stl t v'` >> fs [] >>
      Cases_on `x` >> fs [] >> rename1 `(ll',stl')` >>
      rename1 `o_store res_PC ta tv` >>
      `stl = State_st_list l (s |+ (t,v')) cs fs`
       by METIS_TAC [OoO_Exe_list_instr_not_stored_guard_true_sem_instr_result_form] >>
      rw [] >>
      Q.ABBREV_TAC `pi0 = pi ++ [(State_st_list l s cs fs,ll,State_st_list l (s |+ (t,v')) cs fs);
       (State_st_list l (s |+ (t,v')) cs fs,ll',stl')]` >>
      `FLOOKUP (s |+ (t,v')) t = SOME v'` by fs [FLOOKUP_UPDATE] >>
      `State_st_list_well_formed_ok stl'`
       by METIS_TAC [State_st_list_well_formed_ok_OoO_Ftc_list_stored] >>
      
      `out_of_order_step_list (State_st_list l (s |+ (t,v')) cs fs) ll' stl'`
       by METIS_TAC [OoO_Ftc_list_stored_SOME_out_of_order_step_list] >>
      
      `State_st_list_well_formed_ok (SND (SND (LAST pi0)))` by fs [Abbr `pi0`] >>
      sg `step_execution out_of_order_step_list pi0` >-
       (fs [Abbr `pi0`,step_list_to_step] >>
        `step_execution out_of_order_step_list
          (pi ++ [(State_st_list l s cs fs,ll,State_st_list l (s |+ (t,v')) cs fs)])`
          suffices_by METIS_TAC [step_execution_rules] >>
        `pi <> []` by METIS_TAC [step_execution_not_empty_list] >>
        `pi = [] \/ ?e pi1. pi = SNOC e pi1` by fs [SNOC_CASES] >> fs [SNOC_APPEND] >>
        Cases_on `e` >> fs [] >> Cases_on `r` >> rename1 `(stl1,ll1,stl2)` >>
        fs [step_list_to_step] >> rw [] >>
        `pi1 ++ [(stl1,ll1,State_st_list l s cs fs)] ++
          [(State_st_list l s cs fs,ll,State_st_list l (s |+ (t,v')) cs fs)] =
         pi1 ++ [(stl1,ll1,State_st_list l s cs fs);
           (State_st_list l s cs fs,ll,State_st_list l (s |+ (t,v')) cs fs)]`
         by fs [] >>
        rw [] >> METIS_TAC [step_execution_rules]) >>

      `SND (SND (LAST pi0)) = stl'` by fs [Abbr `pi0`] >>
      `?pi''. pi' = pi0 ++ pi'' /\
        step_execution out_of_order_step_list pi' /\
        LENGTH pi'' <= 2 * n` by METIS_TAC [] >>
      fs [Abbr `pi0`],
      
      Q.ABBREV_TAC `pi0 = pi ++ [(State_st_list l s cs fs,ll,stl)]` >>
      `State_st_list_well_formed_ok (SND (SND (LAST pi0)))` by fs [Abbr `pi0`] >>

      sg `step_execution out_of_order_step_list pi0` >-
       (fs [Abbr `pi0`,step_list_to_step] >>
        `pi <> []` by METIS_TAC [step_execution_not_empty_list] >>
        `pi = [] \/ ?e pi1. pi = SNOC e pi1` by fs [SNOC_CASES] >> fs [SNOC_APPEND] >>
        Cases_on `e` >> fs [] >> Cases_on `r` >> rename1 `(stl1,ll1,stl2)` >>
        fs [step_list_to_step] >> rw [] >>
        `pi1 ++ [(stl1,ll1,State_st_list l s cs fs)] ++
          [(State_st_list l s cs fs,ll,stl)] =
         pi1 ++ [(stl1,ll1,State_st_list l s cs fs);
          (State_st_list l s cs fs,ll,stl)]`
         by fs [] >>
        rw [] >> METIS_TAC [step_execution_rules]) >>
      `SND (SND (LAST pi0)) = stl` by fs [Abbr `pi0`] >>
      `?pi''. pi' = pi0 ++ pi'' /\
        step_execution out_of_order_step_list pi' /\
        LENGTH pi'' <= 2 * n` by METIS_TAC [] >>
      fs [Abbr `pi0`],

      rename1 `o_store res_MEM ta tv` >>
      Cases_on `OoO_Cmt_list_stored sem_expr stl t ta tv` >> fs [] >>
      Cases_on `x` >> fs [] >> rename1 `(ll',stl')` >>
      `stl = State_st_list l (s |+ (t,v')) cs fs`
       by METIS_TAC [OoO_Exe_list_instr_not_stored_guard_true_sem_instr_result_form] >>
      rw [] >>
      Q.ABBREV_TAC `pi0 = pi ++ [(State_st_list l s cs fs,ll,State_st_list l (s |+ (t,v')) cs fs);
       (State_st_list l (s |+ (t,v')) cs fs,ll',stl')]` >>
      `FLOOKUP (s |+ (t,v')) t = SOME v'` by fs [FLOOKUP_UPDATE] >>
      `FLOOKUP (s |+ (t,v')) t <> NONE` by fs [] >>
      `State_st_list_well_formed_ok stl'`
       by METIS_TAC [State_st_list_well_formed_ok_OoO_Cmt_list_stored] >>

      `out_of_order_step_list (State_st_list l (s |+ (t,v')) cs fs) ll' stl'`
       by METIS_TAC [OoO_Cmt_list_stored_SOME_out_of_order_step_list] >>

      `State_st_list_well_formed_ok (SND (SND (LAST pi0)))` by fs [Abbr `pi0`] >>
      
      sg `step_execution out_of_order_step_list pi0` >-
       (fs [Abbr `pi0`,step_list_to_step] >>
        `step_execution out_of_order_step_list 
         (pi ++ [(State_st_list l s cs fs,ll,State_st_list l (s |+ (t,v')) cs fs)])`
         suffices_by METIS_TAC [step_execution_rules] >>
        `pi <> []` by METIS_TAC [step_execution_not_empty_list] >>
        `pi = [] \/ ?e pi1. pi = SNOC e pi1` by fs [SNOC_CASES] >> fs [SNOC_APPEND] >>
        Cases_on `e` >> fs [] >> Cases_on `r` >> rename1 `(stl1,ll1,stl2)` >>
        fs [step_list_to_step] >> rw [] >>
        `pi1 ++ [(stl1,ll1,State_st_list l s cs fs)] ++
          [(State_st_list l s cs fs,ll,State_st_list l (s |+ (t,v')) cs fs)] =
         pi1 ++ [(stl1,ll1,State_st_list l s cs fs);
           (State_st_list l s cs fs,ll,State_st_list l (s |+ (t,v')) cs fs)]`
         by fs [] >>
        rw [] >> METIS_TAC [step_execution_rules]) >>
      `SND (SND (LAST pi0)) = stl'` by fs [Abbr `pi0`] >>
      `?pi''. pi' = pi0 ++ pi'' /\
        step_execution out_of_order_step_list pi' /\
        LENGTH pi'' <= 2 * n` by METIS_TAC [] >>
      fs [Abbr `pi0`]
     ]
   ]) >>
 `MEM (i_assign t c mop) l` by METIS_TAC [DROP_HEAD_MEM] >>
 `FIND_instr t l = SOME (i_assign t c mop)`
  by METIS_TAC [State_st_list_well_formed_ok,State_st_list_ok,NO_DUPLICATES_FIND_instr,bound_name_instr] >> 
 Cases_on `mop` >> fs [] >| [
  `?pi''. pi' = pi ++ pi'' /\
   step_execution out_of_order_step_list pi' /\
   LENGTH pi'' <= 2 * n` by METIS_TAC [] >>
  Q.EXISTS_TAC `pi''` >> rw [],
  
  `?pi''. pi' = pi ++ pi'' /\
   step_execution out_of_order_step_list pi' /\
   LENGTH pi'' <= 2 * n` by METIS_TAC [] >>
  Q.EXISTS_TAC `pi''` >> rw [],

  Cases_on `r` >> fs [] >| [
   Cases_on `MEM t fs` >> fs [] >-
    (`?pi''. pi' = pi ++ pi'' /\
       step_execution out_of_order_step_list pi' /\
       LENGTH pi'' <= 2 * n` by METIS_TAC [] >>
     Q.EXISTS_TAC `pi''` >> rw []) >>
   Cases_on `OoO_Ftc_list_stored_incomplete translate_val_list sem_expr (State_st_list l s cs fs) t x` >> fs [] >>
   Cases_on `x'` >> fs [] >> rename1 `(ll,stl)` >> rename1 `o_store res_PC ta tv` >>
   rename1 `FLOOKUP s t = SOME v` >>
   `State_st_list_ok (State_st_list l s cs fs)`
    by fs [State_st_list_ok,State_st_list_well_formed_ok] >>
   
   `out_of_order_step_list (State_st_list l s cs fs) ll stl`
    by METIS_TAC [OoO_Ftc_list_stored_incomplete_SOME_out_of_order_step_list] >>
   
   `State_st_list_ok stl` by METIS_TAC [step_invariant,step_invariant_out_of_order_step_list_ok] >>
   `State_st_list_well_formed_ok stl`
    by METIS_TAC [step_invariant,step_invariant_out_of_order_step_list_well_formed_ok] >>
   
   Q.ABBREV_TAC `pi0 = pi ++ [(State_st_list l s cs fs,ll,stl)]` >>
   `State_st_list_well_formed_ok (SND (SND (LAST pi0)))` by fs [Abbr `pi0`] >>

   sg `step_execution out_of_order_step_list pi0` >-
    (fs [Abbr `pi0`,step_list_to_step] >>
     `pi <> []` by METIS_TAC [step_execution_not_empty_list] >>
     `pi = [] \/ ?e pi1. pi = SNOC e pi1` by fs [SNOC_CASES] >> fs [SNOC_APPEND] >>
     Cases_on `e` >> fs [] >> Cases_on `r` >> rename1 `(stl1,ll1,stl2)` >>
     fs [step_list_to_step] >> rw [] >>
     `pi1 ++ [(stl1,ll1,State_st_list l s cs fs)] ++
       [(State_st_list l s cs fs,ll,stl)] =
      pi1 ++ [(stl1,ll1,State_st_list l s cs fs);
        (State_st_list l s cs fs,ll,stl)]`
      by fs [] >>
     rw [] >> METIS_TAC [step_execution_rules]) >>

   `SND (SND (LAST pi0)) = stl` by fs [Abbr `pi0`] >>
   `?pi''. pi' = pi0 ++ pi'' /\
     step_execution out_of_order_step_list pi' /\
     LENGTH pi'' <= 2 * n` by METIS_TAC [] >>
   fs [Abbr `pi0`],

   `?pi''. pi' = pi ++ pi'' /\
     step_execution out_of_order_step_list pi' /\
     LENGTH pi'' <= 2 * n` by METIS_TAC [] >>
   Q.EXISTS_TAC `pi''` >> rw [],

   Cases_on `MEM t cs` >> fs [] >-
    (`?pi''. pi' = pi ++ pi'' /\
      step_execution out_of_order_step_list pi' /\
      LENGTH pi'' <= 2 * n` by METIS_TAC [] >>
     Q.EXISTS_TAC `pi''` >> rw []) >>

   rename1 `o_store res_MEM ta tv` >>
   Cases_on `OoO_Cmt_list_stored_incomplete sem_expr (State_st_list l s cs fs) t ta tv` >> fs [] >>
   Cases_on `x'` >> fs [] >> rename1 `(ll,stl)` >>
   rename1 `FLOOKUP s t = SOME v` >>
   `FLOOKUP s t <> NONE` by rw [] >>

   `State_st_list_ok (State_st_list l s cs fs)`
    by fs [State_st_list_ok,State_st_list_well_formed_ok] >>
   
   `out_of_order_step_list (State_st_list l s cs fs) ll stl`
    by METIS_TAC [OoO_Cmt_list_stored_incomplete_SOME_out_of_order_step_list] >>

   `State_st_list_ok stl` by METIS_TAC [step_invariant,step_invariant_out_of_order_step_list_ok] >>
   `State_st_list_well_formed_ok stl`
    by METIS_TAC [step_invariant,step_invariant_out_of_order_step_list_well_formed_ok] >>

   Q.ABBREV_TAC `pi0 = pi ++ [(State_st_list l s cs fs,ll,stl)]` >>
   `State_st_list_well_formed_ok (SND (SND (LAST pi0)))` by fs [Abbr `pi0`] >>

   sg `step_execution out_of_order_step_list pi0` >-
    (fs [Abbr `pi0`,step_list_to_step] >>
     `pi <> []` by METIS_TAC [step_execution_not_empty_list] >>
     `pi = [] \/ ?e pi1. pi = SNOC e pi1` by fs [SNOC_CASES] >> fs [SNOC_APPEND] >>
     Cases_on `e` >> fs [] >> Cases_on `r` >> rename1 `(stl1,ll1,stl2)` >>
     fs [step_list_to_step] >> rw [] >>
     `pi1 ++ [(stl1,ll1,State_st_list l s cs fs)] ++
       [(State_st_list l s cs fs,ll,stl)] =
      pi1 ++ [(stl1,ll1,State_st_list l s cs fs);
        (State_st_list l s cs fs,ll,stl)]`
      by fs [] >>
     rw [] >> METIS_TAC [step_execution_rules]) >>

   `SND (SND (LAST pi0)) = stl` by fs [Abbr `pi0`] >>
   `?pi''. pi' = pi0 ++ pi'' /\
     step_execution out_of_order_step_list pi' /\
     LENGTH pi'' <= 2 * n` by METIS_TAC [] >>
   fs [Abbr `pi0`]
  ]
 ]
QED

Theorem IO_bounded_execution_acc_OoO_empty_sound:
 !l s cs fs pos n i il pi.
  State_st_list_well_formed_ok (State_st_list l s cs fs) ==>
  DROP pos l = i::il ==>
  ~(Completed_list sem_expr (State_st_list l s cs fs) i) ==>
  IO_bounded_execution_acc translate_val_list sem_expr (State_st_list l s cs fs) pos (SUC n) [] = SOME pi ==>
  step_execution_list_OoO_HD (State_st_list l s cs fs) pi (SUC n)
Proof
 once_rewrite_tac [IO_bounded_execution_acc] >>
 fs [] >> rw [] >>
 Cases_on `i` >> rename1 `i_assign t c mop` >> fs [] >>
 `MEM (i_assign t c mop) l` by METIS_TAC [DROP_HEAD_MEM] >>
 `FIND_instr t l = SOME (i_assign t c mop)`
  by METIS_TAC [State_st_list_well_formed_ok,State_st_list_ok,NO_DUPLICATES_FIND_instr,bound_name_instr] >>
 Cases_on `FLOOKUP s t` >> fs [] >> Cases_on `mop` >> fs [Completed_list] >| [
  Cases_on `sem_expr c s` >> fs [] >>
  rename1 `v <> val_false` >>
  Cases_on `v = val_false` >> fs [] >>
  Cases_on `sem_instr_exe sem_expr (i_assign t c (o_internal e)) (State_st_list l s cs fs)` >> fs [] >>
  Cases_on `x` >> fs [] >> rename1 `(v',obs)` >>
  Cases_on `OoO_Exe_list_instr_not_stored_guard_true_sem_instr
   (State_st_list l s cs fs) (i_assign t c (o_internal e)) v' obs` >>
  fs [] >> rename1 `(ll,stl)` >>
  `State_st_list_ok (State_st_list l s cs fs)` by fs [State_st_list_ok,State_st_list_well_formed_ok] >>
  `out_of_order_step_list (State_st_list l s cs fs) ll stl`
   by METIS_TAC [OoO_Exe_list_instr_not_stored_guard_true_sem_instr_SOME_out_of_order_step_list] >>
  `State_st_list_ok stl` by METIS_TAC [step_invariant,step_invariant_out_of_order_step_list_ok] >>
  `State_st_list_well_formed_ok stl`
   by METIS_TAC [step_invariant,step_invariant_out_of_order_step_list_well_formed_ok] >>
  sg `step_execution out_of_order_step_list [(State_st_list l s cs fs,ll,stl)]` >-
   (fs [step_list_to_step] >> METIS_TAC [step_execution_rules]) >>
  `SND (SND (LAST [(State_st_list l s cs fs,ll,stl)])) = stl` by fs [] >>
  `?pi'. pi = [(State_st_list l s cs fs,ll,stl)] ++ pi' /\
   step_execution out_of_order_step_list pi /\
   LENGTH pi' <= 2 * n`
   by METIS_TAC [IO_bounded_execution_acc_OoO_execution_sound] >>
  `FST (HD ([(State_st_list l s cs fs,ll,stl)] ++ pi')) = State_st_list l s cs fs` by fs [] >>
  `LENGTH pi <= 2 * (SUC n)` by rw [] >>
  METIS_TAC [step_execution_list_OoO_HD],

  Cases_on `sem_expr c s` >> fs [] >>
  rename1 `v <> val_false` >>
  Cases_on `v = val_false` >> fs [] >>
  Cases_on `sem_instr_exe sem_expr (i_assign t c (o_load r n')) (State_st_list l s cs fs)` >> fs [] >>
  Cases_on `x` >> fs [] >> rename1 `(v',obs)` >>
  Cases_on `OoO_Exe_list_instr_not_stored_guard_true_sem_instr (State_st_list l s cs fs) (i_assign t c (o_load r n')) v' obs` >>
  fs [] >> rename1 `(ll,stl)` >>
  `State_st_list_ok (State_st_list l s cs fs)` by fs [State_st_list_ok,State_st_list_well_formed_ok] >>
  `out_of_order_step_list (State_st_list l s cs fs) ll stl`
   by METIS_TAC [OoO_Exe_list_instr_not_stored_guard_true_sem_instr_SOME_out_of_order_step_list] >>
  `State_st_list_ok stl` by METIS_TAC [step_invariant,step_invariant_out_of_order_step_list_ok] >>
  `State_st_list_well_formed_ok stl`
   by METIS_TAC [step_invariant,step_invariant_out_of_order_step_list_well_formed_ok] >>
  sg `step_execution out_of_order_step_list [(State_st_list l s cs fs,ll,stl)]` >-
   (fs [step_list_to_step] >> METIS_TAC [step_execution_rules]) >>
  `SND (SND (LAST [(State_st_list l s cs fs,ll,stl)])) = stl` by fs [] >>
  `?pi'. pi = [(State_st_list l s cs fs,ll,stl)] ++ pi' /\
    step_execution out_of_order_step_list pi /\
    LENGTH pi' <= 2 * n`
   by METIS_TAC [IO_bounded_execution_acc_OoO_execution_sound] >>
  `FST (HD ([(State_st_list l s cs fs,ll,stl)] ++ pi')) = State_st_list l s cs fs` by fs [] >>
  `LENGTH pi <= 2 * (SUC n)` by rw [] >>
  METIS_TAC [step_execution_list_OoO_HD],

  Cases_on `sem_expr c s` >> fs [] >>
  rename1 `v <> val_false` >>
  Cases_on `v = val_false` >> Cases_on `r` >> fs [Completed_list] >| [
   rename1 `o_store res_PC ta tv` >>
   Cases_on `sem_instr_exe sem_expr (i_assign t c (o_store res_PC ta tv)) (State_st_list l s cs fs)` >> fs [] >>
   Cases_on `x` >> fs [] >> rename1 `(v',obs)` >>
   Cases_on `OoO_Exe_list_instr_not_stored_guard_true_sem_instr (State_st_list l s cs fs) (i_assign t c (o_store res_PC ta tv)) v' obs` >> fs [] >>
   rename1 `(ll,stl)` >>
   Cases_on `OoO_Ftc_list_stored translate_val_list sem_expr stl t v'` >> fs [] >>
   Cases_on `x` >> fs [] >> rename1 `(ll',stl')` >>
   `State_st_list_ok (State_st_list l s cs fs)` by fs [State_st_list_ok,State_st_list_well_formed_ok] >>
   `out_of_order_step_list (State_st_list l s cs fs) ll stl`
    by METIS_TAC [OoO_Exe_list_instr_not_stored_guard_true_sem_instr_SOME_out_of_order_step_list] >>
   `State_st_list_ok stl` by METIS_TAC [step_invariant,step_invariant_out_of_order_step_list_ok] >>
   `State_st_list_well_formed_ok stl`
    by METIS_TAC [step_invariant,step_invariant_out_of_order_step_list_well_formed_ok] >>
   `stl = State_st_list l (s |+ (t,v')) cs fs`
    by METIS_TAC [OoO_Exe_list_instr_not_stored_guard_true_sem_instr_result_form] >>
   rw [] >>
   `FLOOKUP (s |+ (t,v')) t = SOME v'` by fs [FLOOKUP_UPDATE] >>
   `FLOOKUP (s |+ (t,v')) t <> NONE` by fs [] >>
   `out_of_order_step_list (State_st_list l (s |+ (t,v')) cs fs) ll' stl'`
    by METIS_TAC [OoO_Ftc_list_stored_SOME_out_of_order_step_list] >>
   `State_st_list_ok stl'` by METIS_TAC [step_invariant,step_invariant_out_of_order_step_list_ok] >>
   `State_st_list_well_formed_ok stl'`
    by METIS_TAC [step_invariant,step_invariant_out_of_order_step_list_well_formed_ok] >>
   Q.ABBREV_TAC `pi0 = [(State_st_list l s cs fs,ll,State_st_list l (s |+ (t,v')) cs fs);
    (State_st_list l (s |+ (t,v')) cs fs,ll',stl')]` >>
   sg `step_execution out_of_order_step_list pi0` >-
    (rw [Abbr `pi0`,step_list_to_step] >>
     `step_execution out_of_order_step_list ([] ++
       [(State_st_list l s cs fs,ll,State_st_list l (s |+ (t,v')) cs fs);
        (State_st_list l (s |+ (t,v')) cs fs,ll',stl')])`
      suffices_by fs [] >>
     `step_execution out_of_order_step_list ([] ++
       [(State_st_list l s cs fs,ll,State_st_list l (s |+ (t,v')) cs fs)])`
      suffices_by METIS_TAC [step_execution_rules] >>
     fs [] >> METIS_TAC [step_execution_rules]) >>
   `SND (SND (LAST pi0)) = stl'` by fs [Abbr `pi0`] >>
   `?pi'. pi = pi0 ++ pi' /\
     step_execution out_of_order_step_list pi /\
     LENGTH pi' <= 2 * n`
    by METIS_TAC [IO_bounded_execution_acc_OoO_execution_sound] >>
   `FST (HD (pi0 ++ pi')) = State_st_list l s cs fs` by fs [Abbr `pi0`] >>
   `LENGTH pi <= 2 * (SUC n)` by rw [Abbr `pi0`] >>
   METIS_TAC [step_execution_list_OoO_HD],

   rename1 `o_store res_REG ta tv` >>
   Cases_on `sem_instr_exe sem_expr (i_assign t c (o_store res_REG ta tv)) (State_st_list l s cs fs)` >> fs [] >>
   Cases_on `x` >> rename1 `(v',obs)` >> fs [] >>
   Cases_on `OoO_Exe_list_instr_not_stored_guard_true_sem_instr (State_st_list l s cs fs)
    (i_assign t c (o_store res_REG ta tv)) v' obs` >>
   fs [] >> rename1 `(ll,stl)` >>
   `State_st_list_ok (State_st_list l s cs fs)` by fs [State_st_list_ok,State_st_list_well_formed_ok] >>
   `out_of_order_step_list (State_st_list l s cs fs) ll stl`
    by METIS_TAC [OoO_Exe_list_instr_not_stored_guard_true_sem_instr_SOME_out_of_order_step_list] >>
   `State_st_list_ok stl` by METIS_TAC [step_invariant,step_invariant_out_of_order_step_list_ok] >>
   `State_st_list_well_formed_ok stl`
    by METIS_TAC [step_invariant,step_invariant_out_of_order_step_list_well_formed_ok] >>
   sg `step_execution out_of_order_step_list [(State_st_list l s cs fs,ll,stl)]` >-
    (fs [step_list_to_step] >> METIS_TAC [step_execution_rules]) >>
   `SND (SND (LAST [(State_st_list l s cs fs,ll,stl)])) = stl` by fs [] >>
   `?pi'. pi = [(State_st_list l s cs fs,ll,stl)] ++ pi' /\
     step_execution out_of_order_step_list pi /\
     LENGTH pi' <= 2 * n`
    by METIS_TAC [IO_bounded_execution_acc_OoO_execution_sound] >>
   `FST (HD ([(State_st_list l s cs fs,ll,stl)] ++ pi')) = State_st_list l s cs fs` by fs [] >>
   `LENGTH pi <= 2 * (SUC n)` by rw [] >>
   METIS_TAC [step_execution_list_OoO_HD],

   rename1 `o_store res_MEM ta tv` >>
   Cases_on `sem_instr_exe sem_expr (i_assign t c (o_store res_MEM ta tv)) (State_st_list l s cs fs)` >> fs [] >>
   Cases_on `x` >> fs [] >> rename1 `(v',obs)` >>
   Cases_on `OoO_Exe_list_instr_not_stored_guard_true_sem_instr (State_st_list l s cs fs) (i_assign t c (o_store res_MEM ta tv)) v' obs` >> fs [] >>
   rename1 `(ll,stl)` >>
   Cases_on `OoO_Cmt_list_stored sem_expr stl t ta tv` >> fs [] >>
   Cases_on `x` >> fs [] >> rename1 `(ll',stl')` >>
   `State_st_list_ok (State_st_list l s cs fs)` by fs [State_st_list_ok,State_st_list_well_formed_ok] >>
   `out_of_order_step_list (State_st_list l s cs fs) ll stl`
    by METIS_TAC [OoO_Exe_list_instr_not_stored_guard_true_sem_instr_SOME_out_of_order_step_list] >>
   `State_st_list_ok stl` by METIS_TAC [step_invariant,step_invariant_out_of_order_step_list_ok] >>
   `State_st_list_well_formed_ok stl`
    by METIS_TAC [step_invariant,step_invariant_out_of_order_step_list_well_formed_ok] >>
   `stl = State_st_list l (s |+ (t,v')) cs fs`
    by METIS_TAC [OoO_Exe_list_instr_not_stored_guard_true_sem_instr_result_form] >>
   rw [] >>
   `FLOOKUP (s |+ (t,v')) t = SOME v'` by fs [FLOOKUP_UPDATE] >>
   `FLOOKUP (s |+ (t,v')) t <> NONE` by fs [] >>
   `out_of_order_step_list (State_st_list l (s |+ (t,v')) cs fs) ll' stl'`
    by METIS_TAC [OoO_Cmt_list_stored_SOME_out_of_order_step_list] >>
   `State_st_list_ok stl'` by METIS_TAC [step_invariant,step_invariant_out_of_order_step_list_ok] >>
   `State_st_list_well_formed_ok stl'`
    by METIS_TAC [step_invariant,step_invariant_out_of_order_step_list_well_formed_ok] >>
   Q.ABBREV_TAC `pi0 = [(State_st_list l s cs fs,ll,State_st_list l (s |+ (t,v')) cs fs);
    (State_st_list l (s |+ (t,v')) cs fs,ll',stl')]` >>
   sg `step_execution out_of_order_step_list pi0` >-
    (rw [Abbr `pi0`,step_list_to_step] >>
     `step_execution out_of_order_step_list ([] ++
       [(State_st_list l s cs fs,ll,State_st_list l (s |+ (t,v')) cs fs);
        (State_st_list l (s |+ (t,v')) cs fs,ll',stl')])`
      suffices_by fs [] >>
     `step_execution out_of_order_step_list ([] ++
       [(State_st_list l s cs fs,ll,State_st_list l (s |+ (t,v')) cs fs)])`
      suffices_by METIS_TAC [step_execution_rules] >>
     fs [] >> METIS_TAC [step_execution_rules]) >>
   `SND (SND (LAST pi0)) = stl'` by fs [Abbr `pi0`] >>
   `?pi'. pi = pi0 ++ pi' /\
     step_execution out_of_order_step_list pi /\
     LENGTH pi' <= 2 * n`
    by METIS_TAC [IO_bounded_execution_acc_OoO_execution_sound] >>
   `FST (HD (pi0 ++ pi')) = State_st_list l s cs fs` by fs [Abbr `pi0`] >>
   `LENGTH pi <= 2 * (SUC n)` by rw [Abbr `pi0`] >>
   METIS_TAC [step_execution_list_OoO_HD]
  ],

  rename1 `o_store r ta tv` >>
  rename1 `FLOOKUP s t = SOME v` >>
  Cases_on `r` >> fs [Completed_list] >-
   (Cases_on `MEM t fs` >> fs [] >>
    Cases_on `OoO_Ftc_list_stored_incomplete translate_val_list sem_expr (State_st_list l s cs fs) t v` >> fs [] >>
    Cases_on `x` >> fs [] >>
    rename1 `(ll,stl)` >>
    `State_st_list_ok (State_st_list l s cs fs)` by fs [State_st_list_ok,State_st_list_well_formed_ok] >>
    `out_of_order_step_list (State_st_list l s cs fs) ll stl`
     by METIS_TAC [OoO_Ftc_list_stored_incomplete_SOME_out_of_order_step_list] >>
    `State_st_list_ok stl` by METIS_TAC [step_invariant,step_invariant_out_of_order_step_list_ok] >>
    `State_st_list_well_formed_ok stl`
     by METIS_TAC [step_invariant,step_invariant_out_of_order_step_list_well_formed_ok] >>
    sg `step_execution out_of_order_step_list [(State_st_list l s cs fs,ll,stl)]` >-
     (fs [step_list_to_step] >> METIS_TAC [step_execution_rules]) >>
    `SND (SND (LAST [(State_st_list l s cs fs,ll,stl)])) = stl` by fs [] >>
    `?pi'. pi = [(State_st_list l s cs fs,ll,stl)] ++ pi' /\
      step_execution out_of_order_step_list pi /\
      LENGTH pi' <= 2 * n`
     by METIS_TAC [IO_bounded_execution_acc_OoO_execution_sound] >>
    `FST (HD ([(State_st_list l s cs fs,ll,stl)] ++ pi')) = State_st_list l s cs fs` by fs [] >>
    `LENGTH pi <= 2 * (SUC n)` by rw [] >>
    METIS_TAC [step_execution_list_OoO_HD]) >>

  Cases_on `MEM t cs` >> fs [] >>
  Cases_on `OoO_Cmt_list_stored_incomplete sem_expr (State_st_list l s cs fs) t ta tv` >> fs [] >>
  Cases_on `x` >> fs [] >>
  rename1 `(ll,stl)` >>
  `FLOOKUP s t <> NONE` by fs [] >>
  `State_st_list_ok (State_st_list l s cs fs)` by fs [State_st_list_ok,State_st_list_well_formed_ok] >>
  `out_of_order_step_list (State_st_list l s cs fs) ll stl`
   by METIS_TAC [OoO_Cmt_list_stored_incomplete_SOME_out_of_order_step_list] >>
  `State_st_list_ok stl` by METIS_TAC [step_invariant,step_invariant_out_of_order_step_list_ok] >>
  `State_st_list_well_formed_ok stl`
   by METIS_TAC [step_invariant,step_invariant_out_of_order_step_list_well_formed_ok] >>
  sg `step_execution out_of_order_step_list [(State_st_list l s cs fs,ll,stl)]` >-
   (fs [step_list_to_step] >> METIS_TAC [step_execution_rules]) >>
  `SND (SND (LAST [(State_st_list l s cs fs,ll,stl)])) = stl` by fs [] >>  
  `?pi'. pi = [(State_st_list l s cs fs,ll,stl)] ++ pi' /\
    step_execution out_of_order_step_list pi /\
    LENGTH pi' <= 2 * n`
   by METIS_TAC [IO_bounded_execution_acc_OoO_execution_sound] >>
  `FST (HD ([(State_st_list l s cs fs,ll,stl)] ++ pi')) = State_st_list l s cs fs` by fs [] >>
  `LENGTH pi <= 2 * (SUC n)` by rw [] >>
  METIS_TAC [step_execution_list_OoO_HD]
 ]
QED

(* FIXME: replace by NTH version just below? *)
Theorem IO_bounded_execution_out_of_order_step_list_sound:
 !l s cs fs pos n i il pi.
  State_st_list_well_formed_ok (State_st_list l s cs fs) ==>
  DROP (PRE pos) l = i::il ==>
  ~(Completed_list sem_expr (State_st_list l s cs fs) i) ==>
  IO_bounded_execution translate_val_list sem_expr (State_st_list l s cs fs) pos (SUC n) = SOME pi ==>
  FST (HD pi) = State_st_list l s cs fs /\
  step_execution out_of_order_step_list pi /\
  LENGTH pi <= 2 * n + 2
Proof
 rw [IO_bounded_execution] >>
 `2 * SUC n = 2 * n + 2` by DECIDE_TAC >>
 METIS_TAC [IO_bounded_execution_acc_OoO_empty_sound,step_execution_list_OoO_HD]
QED

Theorem IO_bounded_execution_out_of_order_step_list_sound_NTH:
 !l s cs fs pos n i pi.
  State_st_list_well_formed_ok (State_st_list l s cs fs) ==>
  NTH (PRE pos) l = SOME i ==>
  ~(Completed_list sem_expr (State_st_list l s cs fs) i) ==>
  IO_bounded_execution translate_val_list sem_expr (State_st_list l s cs fs) pos (SUC n) = SOME pi ==>
  FST (HD pi) = State_st_list l s cs fs /\
  step_execution out_of_order_step_list pi /\
  LENGTH pi <= 2 * n + 2
Proof
 METIS_TAC [
  NTH_SOME_DROP,
  IO_bounded_execution_out_of_order_step_list_sound
 ]
QED

(* FIXME: replace by NTH version just below? *)
Theorem IO_bounded_execution_out_of_order_step_sound:
 !l s cs fs pos n i il pi.
  State_st_list_well_formed_ok (State_st_list l s cs fs) ==>
  DROP (PRE pos) l = i::il ==>
  ~(Completed_list sem_expr (State_st_list l s cs fs) i) ==>
  IO_bounded_execution translate_val_list sem_expr (State_st_list l s cs fs) pos (SUC n) = SOME pi ==>
  FST (HD pi) = State_st_list l s cs fs /\
  step_execution out_of_order_step (MAP step_list_to_step pi) /\
  LENGTH pi <= 2 * n + 2
Proof
 METIS_TAC [
  step_execution_out_of_order_step_list_step,
  IO_bounded_execution_out_of_order_step_list_sound
 ]
QED

Theorem IO_bounded_execution_out_of_order_step_sound_NTH:
 !stl pos n i pi.
  State_st_list_well_formed_ok stl ==>
  NTH (PRE pos) (state_program_list stl) = SOME i ==>
  ~(Completed_list sem_expr stl i) ==>
  IO_bounded_execution translate_val_list sem_expr stl pos (SUC n) = SOME pi ==>
  FST (HD pi) = stl /\
  step_execution out_of_order_step (MAP step_list_to_step pi) /\
  LENGTH pi <= 2 * n + 2
Proof
 Cases_on `stl` >>
 rw [state_program_list] >>
 METIS_TAC [  
  NTH_SOME_DROP,
  IO_bounded_execution_out_of_order_step_sound
 ]
QED

(* ---------------------- *)
(* Execution IO soundness *)
(* ---------------------- *)

Theorem IO_bounded_execution_acc_IO_execution_sound:
 translate_val_list_SORTED ==>
 !n l s cs fs pos pi pi'.
  State_st_list_well_formed_ok (State_st_list l s cs fs) ==>
  SORTED bound_name_instr_le l ==>
  Completed_list_up_to sem_expr (State_st_list l s cs fs) pos ==>
  step_execution in_order_step_list pi ==>
  SND (SND (LAST pi)) = State_st_list l s cs fs ==>
  IO_bounded_execution_acc translate_val_list sem_expr (State_st_list l s cs fs) pos n pi = SOME pi' ==>
  ?pi''. pi' = pi ++ pi'' /\
   step_execution in_order_step_list pi' /\
   Completed_list_up_to sem_expr (SND (SND (LAST pi'))) (pos + n) /\
   LENGTH pi'' <= 2 * n
Proof 
 once_rewrite_tac [translate_val_list_SORTED] >>
 strip_tac >>
 Induct_on `n` >- fs [IO_bounded_execution_acc] >>
 once_rewrite_tac [IO_bounded_execution_acc] >>
 fs [] >> rw [] >>
 Cases_on `DROP pos l` >> fs [] >-
  (rw [] >> fs [Completed_list_up_to] >> rw [] >>
   `TAKE (pos + SUC n) l = TAKE pos l` suffices_by METIS_TAC [] \\
   rw [LENGTH_TAKE_PLUS]) >>
 Cases_on `h` >>
 rename1 `i_assign t' c mop::l'` >> rename1 `i_assign t c mop` >>
 fs [] >>
 Cases_on `FLOOKUP s t` >> fs [] >-
  (Cases_on `sem_expr c s` >> fs [] >>
   rename1 `sem_expr c s = SOME v` >>
   Cases_on `v = val_false` >> fs [] >-
    (`Completed_list sem_expr (State_st_list l s cs fs) (i_assign t c mop)`
      by (Cases_on `mop` >> rw [Completed_list] >> Cases_on `r` >> rw [Completed_list]) >>
     sg `Completed_list_up_to sem_expr (State_st_list l s cs fs) (SUC pos)` >-
      (rw [Completed_list_up_to] >>
       `TAKE (SUC pos) l = SNOC (i_assign t c mop) (TAKE pos l)`
        by rw [DROP_TAKE_SNOC] >>
       fs [Completed_list_up_to]) >>
     Q.PAT_X_ASSUM `!l s cs. P`
      (STRIP_ASSUME_TAC o (Q.SPECL [`l`,`s`,`cs`,`fs`,`SUC pos`, `pi`,`pi'`])) >>
     `?pi''. pi' = pi ++ pi'' /\
      step_execution in_order_step_list pi' /\
      Completed_list_up_to sem_expr (SND (SND (LAST pi'))) (n + (SUC pos)) /\
      LENGTH pi'' ≤ 2 * n` by METIS_TAC [] >>
     Q.EXISTS_TAC `pi''` >> rw [] >>
     `pos + SUC n = n + SUC pos` by rw [] >>
     rw []) >>
   Cases_on `sem_instr_exe sem_expr (i_assign t c mop) (State_st_list l s cs fs)` >> fs [] >>
   Cases_on `x` >> rename1 `(v',obs)` >> fs [] >>
   Cases_on `OoO_Exe_list_instr_not_stored_guard_true_sem_instr
    (State_st_list l s cs fs) (i_assign t c mop) v' obs` >>
   fs [] >> rename1 `(ll,stl)` >>
   `MEM (i_assign t c mop) l` by METIS_TAC [DROP_HEAD_MEM] >>
   `FIND_instr t l = SOME (i_assign t c mop)`
    by METIS_TAC [State_st_list_well_formed_ok,State_st_list_ok,NO_DUPLICATES_FIND_instr,bound_name_instr] >>
   `State_st_list_ok (State_st_list l s cs fs)` by fs [State_st_list_ok,State_st_list_well_formed_ok] >>   
   `out_of_order_step_list (State_st_list l s cs fs) ll stl`
    by METIS_TAC [OoO_Exe_list_instr_not_stored_guard_true_sem_instr_SOME_out_of_order_step_list] >>
   `State_st_list_ok stl` by METIS_TAC [step_invariant,step_invariant_out_of_order_step_list_ok] >>
   `State_st_list_well_formed_ok stl`
    by METIS_TAC [step_invariant,step_invariant_out_of_order_step_list_well_formed_ok] >>
   sg `in_order_step_list (State_st_list l s cs fs) ll stl` >-
    (`ll = ll_lb obs act_exe_list t /\ stl = State_st_list l (s |+ (t,v')) cs fs`
      by METIS_TAC [OoO_Exe_list_instr_not_stored_guard_true_sem_instr_result_form] >>
     rw [in_order_step_list,IO_step_list] >>
     fs [out_of_order_step_list] >>
     rw [EVERY_MEM] >>
     fs [MEM_FILTER] >>
     `bound_name_instr i < t` by DECIDE_TAC >>
     `MEM i (TAKE pos l)` suffices_by fs [Completed_list_up_to] >>
     `MEM i (TAKE pos l) \/ MEM i (DROP pos l)`
      by METIS_TAC [TAKE_DROP,MEM_APPEND] >>
     `i <> i_assign t c mop` by (Cases_on `i` >> fs [bound_name_instr]) >>
     `MEM i (i_assign t c mop::l')` by METIS_TAC [] >>
     fs [] >> rw [] >>
     sg `SORTED bound_name_instr_le ((TAKE pos l ++ [i_assign t c mop]) ++ l')` >-
      (`(TAKE pos l ++ [i_assign t c mop]) ++ l' = l` suffices_by rw [] >>
       `l = TAKE pos l ++ (i_assign t c mop::l')` by METIS_TAC [TAKE_DROP] >>
       once_rewrite_tac [GSYM APPEND_ASSOC] >>
       `[i_assign t c mop] ++ l' = i_assign t c mop::l'` by rw [] >>
       METIS_TAC []) >>
     `!x y. MEM x (TAKE pos l ++ [i_assign t c mop]) ==> MEM y l' ==> bound_name_instr_le x y`
      by METIS_TAC [SORTED_APPEND,transitive_bound_name_instr_le] >>
     `MEM (i_assign t c mop) (TAKE pos l ++ [i_assign t c mop])` by rw [] >>
     `bound_name_instr_le (i_assign t c mop) i` by METIS_TAC [] >>
     fs [bound_name_instr_le,name_le,bound_name_instr]) >>
   Cases_on `mop` >> fs [] >| [
    Q.ABBREV_TAC `pi0 = pi ++ [(State_st_list l s cs fs,ll,stl)]` >>
    `State_st_list_well_formed_ok (SND (SND (LAST pi0)))` by fs [Abbr `pi0`] >>
    sg `step_execution in_order_step_list pi0` >-
      (fs [Abbr `pi0`,step_list_to_step] >>
       `pi <> []` by METIS_TAC [step_execution_not_empty_list] >>
       `pi = [] \/ ?e pi1. pi = SNOC e pi1` by fs [SNOC_CASES] >> fs [SNOC_APPEND] >>
       Cases_on `e'` >> fs [] >> Cases_on `r` >> rename1 `(stl1,ll1,stl2)` >>
       fs [step_list_to_step] >> rw [] >>
       `pi1 ++ [(stl1,ll1,State_st_list l s cs fs)] ++ [(State_st_list l s cs fs,ll,stl)] =
        pi1 ++ [(stl1,ll1,State_st_list l s cs fs);(State_st_list l s cs fs,ll,stl)]`
        by fs [] >>
       rw [] >> METIS_TAC [step_execution_rules]) >>
    `SND (SND (LAST pi0)) = stl` by fs [Abbr `pi0`] >>
    Cases_on `stl` >>
    rename1 `(ll,State_st_list l'' s'' cs'' fs'')` >>
    `SORTED bound_name_instr_le l''` by fs [OoO_Exe_list_instr_not_stored_guard_true_sem_instr] >>
    sg `Completed_list sem_expr (State_st_list l'' s'' cs'' fs'') (i_assign t c (o_internal e))` >-
     (fs [Completed_list,OoO_Exe_list_instr_not_stored_guard_true_sem_instr] >>
      rw [FLOOKUP_DEF])	>>
    sg `Completed_list_up_to sem_expr (State_st_list l'' s'' cs'' fs'') (SUC pos)` >-
     (rw [Completed_list_up_to] >>
      `ll = ll_lb obs act_exe_list t /\ 
       State_st_list l'' s'' cs'' fs'' = State_st_list l (s |+ (t,v')) cs fs`
       by METIS_TAC [OoO_Exe_list_instr_not_stored_guard_true_sem_instr_result_form] >>
      rw [] >>
      `TAKE (SUC pos) l = SNOC (i_assign t c (o_internal e)) (TAKE pos l)` by rw [DROP_TAKE_SNOC] >>
      fs [] >>
      `Completed_list sem_expr (State_st_list l s cs fs) i`
       by fs [Completed_list_up_to] >>
      `MEM i l` by METIS_TAC [MEM_TAKE] >>
      (* TODO: adapt well_formed_state_OoO_completed_t_preserved for lists *)
      `Completed (state_list_to_state (State_st_list l s cs fs)) i`
       by METIS_TAC [Completed_list_correct] >>
      `Completed (state_list_to_state (State_st_list l (s |+ (t,v')) cs fs)) i`
       suffices_by METIS_TAC [Completed_list_correct] >>
      `Completed_t (state_list_to_state (State_st_list l s cs fs)) (bound_name_instr i)`
       by (fs [state_list_to_state] >> rw [Completed_t] >> METIS_TAC []) >>
      `Completed_t (state_list_to_state (State_st_list l (s |+ (t,v')) cs fs)) (bound_name_instr i)`
       by METIS_TAC [state_list_to_state,
        out_of_order_step_list_sound,
        well_formed_state_OoO_completed_t_preserved,
        State_st_list_well_formed_ok] >>
      fs [state_list_to_state,Completed_t,State_st_list_well_formed_ok] >>
      METIS_TAC [wfs_unique_instr_names]) >>
    Q.PAT_X_ASSUM `!l s cs. P`
      (STRIP_ASSUME_TAC o (Q.SPECL [`l''`,`s''`,`cs''`,`fs''`,`SUC pos`, `pi0`,`pi'`])) >>
    `?pi''. pi' = pi0 ++ pi'' /\
      step_execution in_order_step_list pi' /\
      Completed_list_up_to sem_expr (SND (SND (LAST pi'))) (n + SUC pos) /\
      LENGTH pi'' <= 2 * n` by METIS_TAC [] >>
    Q.EXISTS_TAC `(State_st_list l s cs fs,ll,State_st_list l'' s'' cs'' fs'')::pi''` >>
    `pos + SUC n = n + SUC pos` by DECIDE_TAC >>
    rw [Abbr `pi0`],

    Q.ABBREV_TAC `pi0 = pi ++ [(State_st_list l s cs fs,ll,stl)]` >>
    `State_st_list_well_formed_ok (SND (SND (LAST pi0)))` by fs [Abbr `pi0`] >>
    sg `step_execution in_order_step_list pi0` >-
      (fs [Abbr `pi0`,step_list_to_step] >>
       `pi <> []` by METIS_TAC [step_execution_not_empty_list] >>
       `pi = [] \/ ?e pi1. pi = SNOC e pi1` by fs [SNOC_CASES] >> fs [SNOC_APPEND] >>
       Cases_on `e` >> fs [] >> Cases_on `r'` >> rename1 `(stl1,ll1,stl2)` >>
       fs [step_list_to_step] >> rw [] >>
       `pi1 ++ [(stl1,ll1,State_st_list l s cs fs)] ++ [(State_st_list l s cs fs,ll,stl)] =
        pi1 ++ [(stl1,ll1,State_st_list l s cs fs);(State_st_list l s cs fs,ll,stl)]`
        by fs [] >>
       rw [] >> METIS_TAC [step_execution_rules]) >>
    `SND (SND (LAST pi0)) = stl` by fs [Abbr `pi0`] >>
    Cases_on `stl` >>
    rename1 `(ll,State_st_list l'' s'' cs'' fs'')` >>
    `SORTED bound_name_instr_le l''` by fs [OoO_Exe_list_instr_not_stored_guard_true_sem_instr] >>
    sg `Completed_list sem_expr (State_st_list l'' s'' cs'' fs'') (i_assign t c (o_load r n'))` >-
     (fs [Completed_list,OoO_Exe_list_instr_not_stored_guard_true_sem_instr] >>
      rw [FLOOKUP_DEF])	>>
    sg `Completed_list_up_to sem_expr (State_st_list l'' s'' cs'' fs'') (SUC pos)` >-
     (rw [Completed_list_up_to] >>
      `ll = ll_lb obs act_exe_list t /\ 
       State_st_list l'' s'' cs'' fs'' = State_st_list l (s |+ (t,v')) cs fs`
       by METIS_TAC [OoO_Exe_list_instr_not_stored_guard_true_sem_instr_result_form] >>
      rw [] >>
      `TAKE (SUC pos) l = SNOC (i_assign t c (o_load r n')) (TAKE pos l)` by rw [DROP_TAKE_SNOC] >>
      fs [] >>
      `Completed_list sem_expr (State_st_list l s cs fs) i`
       by fs [Completed_list_up_to] >>
      `MEM i l` by METIS_TAC [MEM_TAKE] >>
      (* TODO: adapt well_formed_state_OoO_completed_t_preserved for lists *)
      `Completed (state_list_to_state (State_st_list l s cs fs)) i`
       by METIS_TAC [Completed_list_correct] >>
      `Completed (state_list_to_state (State_st_list l (s |+ (t,v')) cs fs)) i`
       suffices_by METIS_TAC [Completed_list_correct] >>
      `Completed_t (state_list_to_state (State_st_list l s cs fs)) (bound_name_instr i)`
       by (fs [state_list_to_state] >> rw [Completed_t] >> METIS_TAC []) >>
      `Completed_t (state_list_to_state (State_st_list l (s |+ (t,v')) cs fs)) (bound_name_instr i)`
       by METIS_TAC [state_list_to_state,
        out_of_order_step_list_sound,
        well_formed_state_OoO_completed_t_preserved,
        State_st_list_well_formed_ok] >>
      fs [state_list_to_state,Completed_t,State_st_list_well_formed_ok] >>
      METIS_TAC [wfs_unique_instr_names]) >>
    Q.PAT_X_ASSUM `!l s cs. P`
      (STRIP_ASSUME_TAC o (Q.SPECL [`l''`,`s''`,`cs''`,`fs''`,`SUC pos`, `pi0`,`pi'`])) >>
    `?pi''. pi' = pi0 ++ pi'' /\
      step_execution in_order_step_list pi' /\
      Completed_list_up_to sem_expr (SND (SND (LAST pi'))) (n + SUC pos) /\
      LENGTH pi'' <= 2 * n` by METIS_TAC [] >>
    Q.EXISTS_TAC `(State_st_list l s cs fs,ll,State_st_list l'' s'' cs'' fs'')::pi''` >>
    `pos + SUC n = n + SUC pos` by DECIDE_TAC >>
    rw [Abbr `pi0`],

    Cases_on `r` >> fs [] >| [
     Cases_on `OoO_Ftc_list_stored translate_val_list sem_expr stl t v'` >> fs [] >>
     Cases_on `x` >> fs [] >> rename1 `(ll',stl')` >>
     rename1 `o_store res_PC ta tv` >>
     `stl = State_st_list l (s |+ (t,v')) cs fs`
      by METIS_TAC [OoO_Exe_list_instr_not_stored_guard_true_sem_instr_result_form] >>
     rw [] >>
     Q.ABBREV_TAC `pi0 = pi ++ [(State_st_list l s cs fs,ll,State_st_list l (s |+ (t,v')) cs fs);
      (State_st_list l (s |+ (t,v')) cs fs,ll',stl')]` >>
     `FLOOKUP (s |+ (t,v')) t = SOME v'` by fs [FLOOKUP_UPDATE] >>
     `out_of_order_step_list (State_st_list l (s |+ (t,v')) cs fs) ll' stl'`
      by METIS_TAC [OoO_Ftc_list_stored_SOME_out_of_order_step_list] >>
     `State_st_list_ok stl'` by METIS_TAC [step_invariant,step_invariant_out_of_order_step_list_ok] >>
     `State_st_list_well_formed_ok stl'`
      by METIS_TAC [step_invariant,step_invariant_out_of_order_step_list_well_formed_ok] >>
     `State_st_list_well_formed_ok (SND (SND (LAST pi0)))` by fs [Abbr `pi0`] >>
     sg `Completed_list_up_to sem_expr (State_st_list l (s |+ (t,v')) cs fs) pos` >-
      (rw [Completed_list_up_to] >>
       `MEM i l` by METIS_TAC [MEM_TAKE] >>
       `Completed_list sem_expr (State_st_list l s cs fs) i`
        by fs [Completed_list_up_to] >>
       `Completed (state_list_to_state (State_st_list l s cs fs)) i`
        by METIS_TAC [Completed_list_correct] >>
       `Completed (state_list_to_state (State_st_list l (s |+ (t,v')) cs fs)) i`
        suffices_by METIS_TAC [Completed_list_correct] >>
       `Completed_t (state_list_to_state (State_st_list l s cs fs)) (bound_name_instr i)`
        by (fs [state_list_to_state] >> rw [Completed_t] >> METIS_TAC []) >>
       `Completed_t (state_list_to_state (State_st_list l (s |+ (t,v')) cs fs)) (bound_name_instr i)`
         by METIS_TAC [state_list_to_state,
          out_of_order_step_list_sound,
          well_formed_state_OoO_completed_t_preserved,
          State_st_list_well_formed_ok] >>
       fs [state_list_to_state,Completed_t,State_st_list_well_formed_ok] >>
       METIS_TAC [wfs_unique_instr_names]) >>
     sg `in_order_step_list (State_st_list l (s |+ (t,v')) cs fs) ll' stl'` >-
      (`ll' = ll_lb (obs_il v') (act_ftc_list (translate_val_list v' (max_bound_name_list l))) t /\
        stl' = State_st_list (l ++ translate_val_list v' (max_bound_name_list l)) (s |+ (t,v')) cs (t::fs)`
        by METIS_TAC [OoO_Ftc_list_stored_result_form] >>
       rw [in_order_step_list,IO_step_list] >>
       fs [out_of_order_step_list] >>
       rw [EVERY_MEM] >>
       fs [MEM_FILTER] >>
       `bound_name_instr i < t` by DECIDE_TAC >>
       `MEM i (TAKE pos l)` suffices_by fs [Completed_list_up_to] >>
       `MEM i (TAKE pos l) \/ MEM i (DROP pos l)`
        by METIS_TAC [TAKE_DROP,MEM_APPEND] >>
       `i <> i_assign t c (o_store res_PC ta tv)` by (Cases_on `i` >> fs [bound_name_instr]) >>
       `MEM i (i_assign t c (o_store res_PC ta tv)::l')` by METIS_TAC [] >>
       fs [] >> rw [] >>
       sg `SORTED bound_name_instr_le ((TAKE pos l ++ [i_assign t c (o_store res_PC ta tv)]) ++ l')` >-
        (`(TAKE pos l ++ [i_assign t c (o_store res_PC ta tv)]) ++ l' = l` suffices_by rw [] >>
         `l = TAKE pos l ++ (i_assign t c (o_store res_PC ta tv)::l')` by METIS_TAC [TAKE_DROP] >>
         once_rewrite_tac [GSYM APPEND_ASSOC] >>
         `[i_assign t c (o_store res_PC ta tv)] ++ l' = i_assign t c (o_store res_PC ta tv)::l'` by rw [] >>
         METIS_TAC []) >>
       `!x y. MEM x (TAKE pos l ++ [i_assign t c (o_store res_PC ta tv)]) ==> MEM y l' ==> bound_name_instr_le x y`
        by METIS_TAC [SORTED_APPEND,transitive_bound_name_instr_le] >>
       `MEM (i_assign t c (o_store res_PC ta tv)) (TAKE pos l ++ [i_assign t c (o_store res_PC ta tv)])` by rw [] >>
       `bound_name_instr_le (i_assign t c (o_store res_PC ta tv)) i` by METIS_TAC [] >>
       fs [bound_name_instr_le,name_le,bound_name_instr]) >>
     sg `SORTED bound_name_instr_le (l ++ translate_val_list v' (max_bound_name_list l))` >-
      (`!x y. MEM x l ==> MEM y (translate_val_list v' (max_bound_name_list l)) ==> bound_name_instr_le x y`
        suffices_by METIS_TAC [SORTED_APPEND,transitive_bound_name_instr_le] >>
       rw [bound_name_instr_le,name_le] >>
       `bound_name_instr x < bound_name_instr y` suffices_by rw [] >>
       `y IN (translate_val v' (MAX_SET (bound_names_program (set l))))`
        by METIS_TAC [translate_val_list_correct,max_bound_name_list_correct] >>
       `FINITE (set l)` by rw [] >>
       METIS_TAC [translate_val_max_name_lt]) >>
     `Completed_list sem_expr (State_st_list (l ++ translate_val_list v' (max_bound_name_list l))
       (s |+ (t,v')) cs (t::fs)) (i_assign t c (o_store res_PC ta tv))` by rw [Completed_list] >>
     sg `Completed_list_up_to sem_expr stl' (SUC pos)` >-
      (`stl' = State_st_list (l ++ translate_val_list v' (max_bound_name_list l)) (s |+ (t,v')) cs (t::fs)`
        by METIS_TAC [OoO_Ftc_list_stored_result_form] >>
       rw [Completed_list_up_to] >>
       `DROP pos (l ++ translate_val_list v' (max_bound_name_list l)) =
        i_assign t c (o_store res_PC ta tv)::l' ++ translate_val_list v' (max_bound_name_list l)`
        by rw [DROP_CONS_APPEND] >>
       `TAKE (SUC pos) (l ++ translate_val_list v' (max_bound_name_list l)) =
        SNOC (i_assign t c (o_store res_PC ta tv)) (TAKE pos (l ++ translate_val_list v' (max_bound_name_list l)))`
        by rw [DROP_TAKE_SNOC] >>
       fs [] >>
       `MEM i (TAKE pos l)` by METIS_TAC [DROP_CONS_TAKE_APPEND] >>
       `MEM i l` by METIS_TAC [MEM_TAKE] >>
       `Completed_list sem_expr (State_st_list l (s |+ (t,v')) cs fs) i`
        by fs [Completed_list_up_to] >>
       `Completed (state_list_to_state (State_st_list l (s |+ (t,v')) cs fs)) i`
        by fs [Completed_list_correct] >>       
       `Completed_t (state_list_to_state (State_st_list l (s |+ (t,v')) cs fs)) (bound_name_instr i)`
        by (fs [state_list_to_state] >> rw [Completed_t] >> METIS_TAC []) >>
       `Completed_t (state_list_to_state (State_st_list (l ++ translate_val_list v' (max_bound_name_list l))
         (s |+ (t,v')) cs (t::fs))) (bound_name_instr i)`
        by METIS_TAC [state_list_to_state,
         out_of_order_step_list_sound,
         well_formed_state_OoO_completed_t_preserved,
         State_st_list_well_formed_ok] >>
       `Completed (state_list_to_state (State_st_list (l ++ translate_val_list v' (max_bound_name_list l))
         (s |+ (t,v')) cs (t::fs))) i` suffices_by METIS_TAC [Completed_list_correct] >>
       sg `!i'. MEM i' (translate_val_list v' (max_bound_name_list l)) ==>
        bound_name_instr i < bound_name_instr i'` >-
        (`FINITE (set l)` by rw [] >>
         rw [] >>
         `i' IN (translate_val v' (MAX_SET (bound_names_program (set l))))`
          by METIS_TAC [translate_val_list_correct,max_bound_name_list_correct] >>
         METIS_TAC [translate_val_max_name_lt]) >>
       fs [state_list_to_state,Completed_t,State_st_list_well_formed_ok] >-
       METIS_TAC [wfs_unique_instr_names] >>
       `bound_name_instr i < bound_name_instr i` suffices_by DECIDE_TAC >>
       METIS_TAC []) >>
     `stl' = State_st_list (l ++ translate_val_list v' (max_bound_name_list l)) (s |+ (t,v')) cs (t::fs)`
      by METIS_TAC [OoO_Ftc_list_stored_result_form] >>
     rw [] >>
     sg `step_execution in_order_step_list pi0` >-
      (fs [Abbr `pi0`,step_list_to_step] >>
       `step_execution in_order_step_list (pi ++ [(State_st_list l s cs fs,ll,State_st_list l (s |+ (t,v')) cs fs)])`
        suffices_by METIS_TAC [step_execution_rules] >>
       `pi <> []` by METIS_TAC [step_execution_not_empty_list] >>
       `pi = [] \/ ?e pi1. pi = SNOC e pi1` by fs [SNOC_CASES] >> fs [SNOC_APPEND] >>
       Cases_on `e` >> fs [] >> Cases_on `r` >> rename1 `(stl1,ll1,stl2)` >>
       fs [step_list_to_step] >> rw [] >>
       `pi1 ++ [(stl1,ll1,State_st_list l s cs fs)] ++ [(State_st_list l s cs fs,ll,State_st_list l (s |+ (t,v')) cs fs)] =
         pi1 ++ [(stl1,ll1,State_st_list l s cs fs);(State_st_list l s cs fs,ll,State_st_list l (s |+ (t,v')) cs fs)]`
        by fs [] >>
       rw [] >> METIS_TAC [step_execution_rules]) >>
     Q.PAT_X_ASSUM `!l s cs. P`
      (STRIP_ASSUME_TAC o (Q.SPECL [`l ++ translate_val_list v' (max_bound_name_list l)`,
        `s |+ (t,v')`,`cs`,`t::fs`,`SUC pos`, `pi0`,`pi'`])) >>
     `?pi''. pi' = pi0 ++ pi'' /\
      step_execution in_order_step_list pi' /\
      Completed_list_up_to sem_expr (SND (SND (LAST pi'))) (n + SUC pos) /\
      LENGTH pi'' <= 2 * n` by fs [Abbr `pi0`] >>
     Q.EXISTS_TAC `(State_st_list l s cs fs,ll,State_st_list l (s |+ (t,v')) cs fs)::
      (State_st_list l (s |+ (t,v')) cs fs,ll', State_st_list
      (l ++ translate_val_list v' (max_bound_name_list l)) (s |+ (t,v')) cs (t::fs))::pi''` >>
     `pos + SUC n = n + SUC pos` by DECIDE_TAC >>
     rw [Abbr `pi0`],

     Q.ABBREV_TAC `pi0 = pi ++ [(State_st_list l s cs fs,ll,stl)]` >>
     `State_st_list_well_formed_ok (SND (SND (LAST pi0)))` by fs [Abbr `pi0`] >>
     sg `step_execution in_order_step_list pi0` >-
      (fs [Abbr `pi0`,step_list_to_step] >>
       `pi <> []` by METIS_TAC [step_execution_not_empty_list] >>
       `pi = [] \/ ?e pi1. pi = SNOC e pi1` by fs [SNOC_CASES] >> fs [SNOC_APPEND] >>
       Cases_on `e` >> fs [] >> Cases_on `r` >> rename1 `(stl1,ll1,stl2)` >>
       fs [step_list_to_step] >> rw [] >>
       `pi1 ++ [(stl1,ll1,State_st_list l s cs fs)] ++ [(State_st_list l s cs fs,ll,stl)] =
         pi1 ++ [(stl1,ll1,State_st_list l s cs fs);(State_st_list l s cs fs,ll,stl)]`
        by fs [] >>
       rw [] >> METIS_TAC [step_execution_rules]) >>
     `SND (SND (LAST pi0)) = stl` by fs [Abbr `pi0`] >>
     Cases_on `stl` >>
     rename1 `(ll,State_st_list l'' s'' cs'' fs'')` >>
     `SORTED bound_name_instr_le l''` by fs [OoO_Exe_list_instr_not_stored_guard_true_sem_instr] >>
     sg `Completed_list sem_expr (State_st_list l'' s'' cs'' fs'') (i_assign t c (o_store res_REG n' n0))` >-
      (fs [Completed_list,OoO_Exe_list_instr_not_stored_guard_true_sem_instr] >>
      rw [FLOOKUP_DEF])	>>
     sg `Completed_list_up_to sem_expr (State_st_list l'' s'' cs'' fs'') (SUC pos)` >-
      (rw [Completed_list_up_to] >>
       `ll = ll_lb obs act_exe_list t /\ 
        State_st_list l'' s'' cs'' fs'' = State_st_list l (s |+ (t,v')) cs fs`
        by METIS_TAC [OoO_Exe_list_instr_not_stored_guard_true_sem_instr_result_form] >>
       rw [] >>
       `TAKE (SUC pos) l = SNOC (i_assign t c (o_store res_REG n' n0)) (TAKE pos l)` by rw [DROP_TAKE_SNOC] >>
       fs [] >>
       `Completed_list sem_expr (State_st_list l s cs fs) i`
        by fs [Completed_list_up_to] >>
       `MEM i l` by METIS_TAC [MEM_TAKE] >>
       `Completed (state_list_to_state (State_st_list l s cs fs)) i`
        by METIS_TAC [Completed_list_correct] >>
       `Completed (state_list_to_state (State_st_list l (s |+ (t,v')) cs fs)) i`
        suffices_by METIS_TAC [Completed_list_correct] >>
       `Completed_t (state_list_to_state (State_st_list l s cs fs)) (bound_name_instr i)`
        by (fs [state_list_to_state] >> rw [Completed_t] >> METIS_TAC []) >>
       `Completed_t (state_list_to_state (State_st_list l (s |+ (t,v')) cs fs)) (bound_name_instr i)`
        by METIS_TAC [state_list_to_state,
         out_of_order_step_list_sound,
         well_formed_state_OoO_completed_t_preserved,
         State_st_list_well_formed_ok] >>
       fs [state_list_to_state,Completed_t,State_st_list_well_formed_ok] >>
       METIS_TAC [wfs_unique_instr_names]) >>       
     Q.PAT_X_ASSUM `!l s cs. P`
      (STRIP_ASSUME_TAC o (Q.SPECL [`l''`,`s''`,`cs''`,`fs''`,`SUC pos`, `pi0`,`pi'`])) >>
     `?pi''. pi' = pi0 ++ pi'' /\
      step_execution in_order_step_list pi' /\
      Completed_list_up_to sem_expr (SND (SND (LAST pi'))) (n + SUC pos) /\
      LENGTH pi'' <= 2 * n` by METIS_TAC [] >>
     Q.EXISTS_TAC `(State_st_list l s cs fs,ll,State_st_list l'' s'' cs'' fs'')::pi''` >>
     `pos + SUC n = n + SUC pos` by DECIDE_TAC >>
     rw [Abbr `pi0`],

     rename1 `o_store res_MEM ta tv` >>
     Cases_on `OoO_Cmt_list_stored sem_expr stl t ta tv` >> fs [] >>
     Cases_on `x` >> fs [] >> rename1 `(ll',stl')` >>
     `stl = State_st_list l (s |+ (t,v')) cs fs`
      by METIS_TAC [OoO_Exe_list_instr_not_stored_guard_true_sem_instr_result_form] >>
     rw [] >>
     Q.ABBREV_TAC `pi0 = pi ++ [(State_st_list l s cs fs,ll,State_st_list l (s |+ (t,v')) cs fs);
      (State_st_list l (s |+ (t,v')) cs fs,ll',stl')]` >>
     `FLOOKUP (s |+ (t,v')) t = SOME v'` by fs [FLOOKUP_UPDATE] >>
     `FLOOKUP (s |+ (t,v')) t <> NONE` by fs [] >>

     `out_of_order_step_list (State_st_list l (s |+ (t,v')) cs fs) ll' stl'`
      by METIS_TAC [OoO_Cmt_list_stored_SOME_out_of_order_step_list] >>
     `State_st_list_ok stl'` by METIS_TAC [step_invariant,step_invariant_out_of_order_step_list_ok] >>
     `State_st_list_well_formed_ok stl'`
      by METIS_TAC [step_invariant,step_invariant_out_of_order_step_list_well_formed_ok] >>     
     `State_st_list_well_formed_ok (SND (SND (LAST pi0)))` by fs [Abbr `pi0`] >>

     sg `Completed_list_up_to sem_expr (State_st_list l (s |+ (t,v')) cs fs) pos` >-
      (rw [Completed_list_up_to] >>
       `MEM i l` by METIS_TAC [MEM_TAKE] >>
       `Completed_list sem_expr (State_st_list l s cs fs) i`
        by fs [Completed_list_up_to] >>
       `Completed (state_list_to_state (State_st_list l s cs fs)) i`
        by METIS_TAC [Completed_list_correct] >>
       `Completed (state_list_to_state (State_st_list l (s |+ (t,v')) cs fs)) i`
        suffices_by METIS_TAC [Completed_list_correct] >>
       `Completed_t (state_list_to_state (State_st_list l s cs fs)) (bound_name_instr i)`
        by (fs [state_list_to_state] >> rw [Completed_t] >> METIS_TAC []) >>
       `Completed_t (state_list_to_state (State_st_list l (s |+ (t,v')) cs fs)) (bound_name_instr i)`
         by METIS_TAC [state_list_to_state,
          out_of_order_step_list_sound,
          well_formed_state_OoO_completed_t_preserved,
          State_st_list_well_formed_ok] >>
       fs [state_list_to_state,Completed_t,State_st_list_well_formed_ok] >>
       METIS_TAC [wfs_unique_instr_names]) >>

     sg `in_order_step_list (State_st_list l (s |+ (t,v')) cs fs) ll' stl'` >-
      (`?a v. ll' = ll_lb (obs_ds a) (act_cmt_list a v) t /\
        stl' = State_st_list l (s |+ (t,v')) (t::cs) fs`
        by METIS_TAC [OoO_Cmt_list_stored_result_form] >>       
       rw [in_order_step_list,IO_step_list] >>
       fs [out_of_order_step_list] >>
       rw [EVERY_MEM] >>
       fs [MEM_FILTER] >>
       `bound_name_instr i < t` by DECIDE_TAC >>
       `MEM i l` by fs [state_list_to_state,instr_in_State] >>
       `MEM i (TAKE pos l)` suffices_by fs [Completed_list_up_to] >>
       `MEM i (TAKE pos l) \/ MEM i (DROP pos l)`
        by METIS_TAC [TAKE_DROP,MEM_APPEND] >>
       `i <> i_assign t c (o_store res_MEM ta tv)` by (Cases_on `i` >> fs [bound_name_instr]) >>
       `MEM i (i_assign t c (o_store res_MEM ta tv)::l')` by METIS_TAC [] >>
       fs [] >> rw [] >>
       sg `SORTED bound_name_instr_le ((TAKE pos l ++ [i_assign t c (o_store res_MEM ta tv)]) ++ l')` >-
        (`(TAKE pos l ++ [i_assign t c (o_store res_MEM ta tv)]) ++ l' = l` suffices_by rw [] >>
         `l = TAKE pos l ++ (i_assign t c (o_store res_MEM ta tv))::l'` by METIS_TAC [TAKE_DROP] >>
         once_rewrite_tac [GSYM APPEND_ASSOC] >>
         `[i_assign t c (o_store res_MEM ta tv)] ++ l' = i_assign t c (o_store res_MEM ta tv)::l'` by rw [] >>
         METIS_TAC []) >>
       `!x y. MEM x (TAKE pos l ++ [i_assign t c (o_store res_MEM ta tv)]) ==> MEM y l' ==> bound_name_instr_le x y`
        by METIS_TAC [SORTED_APPEND,transitive_bound_name_instr_le] >>
       `MEM (i_assign t c (o_store res_MEM ta tv)) (TAKE pos l ++ [i_assign t c (o_store res_MEM ta tv)])` by rw [] >>
       `bound_name_instr_le (i_assign t c (o_store res_MEM ta tv)) i` by METIS_TAC [] >>
       fs [bound_name_instr_le,name_le,bound_name_instr]) >>

     `Completed_list sem_expr (State_st_list l (s |+ (t,v')) (t::cs) fs)
       (i_assign t c (o_store res_MEM ta tv))` by rw [Completed_list] >>
     sg `Completed_list_up_to sem_expr stl' (SUC pos)` >-
      (`stl' = State_st_list l (s |+ (t,v')) (t::cs) fs`
        by METIS_TAC [OoO_Cmt_list_stored_result_form] >>
       rw [Completed_list_up_to] >>
       `TAKE (SUC pos) l = SNOC (i_assign t c (o_store res_MEM ta tv)) (TAKE pos l)`
        by rw [DROP_TAKE_SNOC] >>       
       fs [Completed_list_up_to] >>
       `Completed_list sem_expr (State_st_list l (s |+ (t,v')) cs fs) i` by METIS_TAC [] >>
       `Completed (state_list_to_state (State_st_list l (s |+ (t,v')) cs fs)) i`
        by METIS_TAC [Completed_list_correct] >>
       `Completed (state_list_to_state (State_st_list l (s |+ (t,v')) (t::cs) fs)) i`
        suffices_by METIS_TAC [Completed_list_correct] >>
       `MEM i l` by METIS_TAC [MEM_TAKE] >>
       `Completed_t (state_list_to_state (State_st_list l (s |+ (t,v')) cs fs)) (bound_name_instr i)`
        by (fs [state_list_to_state] >> rw [Completed_t] >> METIS_TAC []) >>
       `Completed_t (state_list_to_state (State_st_list l (s |+ (t,v')) (t::cs) fs)) (bound_name_instr i)`
         by METIS_TAC [state_list_to_state,
          out_of_order_step_list_sound,
          well_formed_state_OoO_completed_t_preserved,
          State_st_list_well_formed_ok] >>
       fs [state_list_to_state,Completed_t,State_st_list_well_formed_ok,Abbr `pi0`] >>
       METIS_TAC [wfs_unique_instr_names]) >>

     `stl' = State_st_list l (s |+ (t,v')) (t::cs) fs`
      by METIS_TAC [OoO_Cmt_list_stored_result_form] >>
     rw [] >>
     sg `step_execution in_order_step_list pi0` >-
      (fs [Abbr `pi0`,step_list_to_step] >>
       `step_execution in_order_step_list (pi ++
         [(State_st_list l s cs fs,ll,State_st_list l (s |+ (t,v')) cs fs)])`
        suffices_by METIS_TAC [step_execution_rules] >>
       `pi <> []` by METIS_TAC [step_execution_not_empty_list] >>
       `pi = [] \/ ?e pi1. pi = SNOC e pi1` by fs [SNOC_CASES] >> fs [SNOC_APPEND] >>
       Cases_on `e` >> fs [] >> Cases_on `r` >> rename1 `(stl1,ll1,stl2)` >>
       fs [step_list_to_step] >> rw [] >>
       `pi1 ++ [(stl1,ll1,State_st_list l s cs fs)] ++ [(State_st_list l s cs fs,ll,State_st_list l (s |+ (t,v')) cs fs)] =
         pi1 ++ [(stl1,ll1,State_st_list l s cs fs);(State_st_list l s cs fs,ll,State_st_list l (s |+ (t,v')) cs fs)]`
        by fs [] >>
       rw [] >> METIS_TAC [step_execution_rules]) >>
     Q.PAT_X_ASSUM `!l s cs. P`
      (STRIP_ASSUME_TAC o (Q.SPECL [`l`,`s |+ (t,v')`,`t::cs`,`fs`,`SUC pos`, `pi0`,`pi'`])) >>
     `?pi''. pi' = pi0 ++ pi'' /\
      step_execution in_order_step_list pi' /\
      Completed_list_up_to sem_expr (SND (SND (LAST pi'))) (n + SUC pos) /\
      LENGTH pi'' <= 2 * n` by fs [Abbr `pi0`] >>
     Q.EXISTS_TAC `(State_st_list l s cs fs,ll,State_st_list l (s |+ (t,v')) cs fs)::
      (State_st_list l (s |+ (t,v')) cs fs,ll',State_st_list l (s |+ (t,v')) (t::cs) fs)::pi''` >>
     `pos + SUC n = n + SUC pos` by DECIDE_TAC >>
     rw [Abbr `pi0`]
    ]
   ]) >>

 `MEM (i_assign t c mop) l` by METIS_TAC [DROP_HEAD_MEM] >>
 `FIND_instr t l = SOME (i_assign t c mop)`
  by METIS_TAC [State_st_list_well_formed_ok,State_st_list_ok,NO_DUPLICATES_FIND_instr,bound_name_instr] >>
 Cases_on `mop` >> fs [] >| [
  `Completed_list sem_expr (State_st_list l s cs fs) (i_assign t c (o_internal e))`
   by rw [Completed_list] >>
  sg `Completed_list_up_to sem_expr (State_st_list l s cs fs) (SUC pos)` >-
   (rw [Completed_list_up_to] >>
    `TAKE (SUC pos) l = SNOC (i_assign t c (o_internal e)) (TAKE pos l)`
     by rw [DROP_TAKE_SNOC] >>
    fs [Completed_list_up_to]) >>
  Q.PAT_X_ASSUM `!l s cs. P`
   (STRIP_ASSUME_TAC o (Q.SPECL [`l`,`s`,`cs`,`fs`,`SUC pos`, `pi`,`pi'`])) >>
  `?pi''. pi' = pi ++ pi'' /\
   step_execution in_order_step_list pi' /\
   Completed_list_up_to sem_expr (SND (SND (LAST pi'))) (n + (SUC pos)) /\
   LENGTH pi'' ≤ 2 * n` by METIS_TAC [] >>
  Q.EXISTS_TAC `pi''` >> rw [] >>
  `pos + SUC n = n + SUC pos` by rw [] >>
  rw [],

  `Completed_list sem_expr (State_st_list l s cs fs) (i_assign t c (o_load r n'))`
   by rw [Completed_list] >>
  sg `Completed_list_up_to sem_expr (State_st_list l s cs fs) (SUC pos)` >-
   (rw [Completed_list_up_to] >>
    `TAKE (SUC pos) l = SNOC (i_assign t c (o_load r n')) (TAKE pos l)`
     by rw [DROP_TAKE_SNOC] >>
    fs [Completed_list_up_to]) >>
  Q.PAT_X_ASSUM `!l s cs. P`
   (STRIP_ASSUME_TAC o (Q.SPECL [`l`,`s`,`cs`,`fs`,`SUC pos`, `pi`,`pi'`])) >>
  `?pi''. pi' = pi ++ pi'' /\
   step_execution in_order_step_list pi' /\
   Completed_list_up_to sem_expr (SND (SND (LAST pi'))) (n + (SUC pos)) /\
   LENGTH pi'' ≤ 2 * n` by METIS_TAC [] >>
  Q.EXISTS_TAC `pi''` >> rw [] >>
  `pos + SUC n = n + SUC pos` by rw [] >>
  rw [],

  Cases_on `r` >> fs [] >| [
   Cases_on `MEM t fs` >> fs [] >-
    (`Completed_list sem_expr (State_st_list l s cs fs) (i_assign t c (o_store res_PC n' n0))`
      by rw [Completed_list] >>
     sg `Completed_list_up_to sem_expr (State_st_list l s cs fs) (SUC pos)` >-
      (rw [Completed_list_up_to] >>
       `TAKE (SUC pos) l = SNOC (i_assign t c (o_store res_PC n' n0)) (TAKE pos l)`
        by rw [DROP_TAKE_SNOC] >>
       fs [Completed_list_up_to]) >>
     Q.PAT_X_ASSUM `!l s cs. P`
      (STRIP_ASSUME_TAC o (Q.SPECL [`l`,`s`,`cs`,`fs`,`SUC pos`, `pi`,`pi'`])) >>
     `?pi''. pi' = pi ++ pi'' /\
       step_execution in_order_step_list pi' /\
       Completed_list_up_to sem_expr (SND (SND (LAST pi'))) (n + (SUC pos)) /\
       LENGTH pi'' ≤ 2 * n` by METIS_TAC [] >>
     Q.EXISTS_TAC `pi''` >> rw [] >>
     `pos + SUC n = n + SUC pos` by rw [] >>
     rw []) >>
   Cases_on `OoO_Ftc_list_stored_incomplete translate_val_list sem_expr (State_st_list l s cs fs) t x` >> fs [] >>
   Cases_on `x'` >> fs [] >> rename1 `(ll,stl)` >> rename1 `o_store res_PC ta tv` >>
   rename1 `FLOOKUP s t = SOME v` >>
   `State_st_list_ok (State_st_list l s cs fs)` by fs [State_st_list_ok,State_st_list_well_formed_ok] >>
   `out_of_order_step_list (State_st_list l s cs fs) ll stl`
    by METIS_TAC [OoO_Ftc_list_stored_incomplete_SOME_out_of_order_step_list] >>
   `State_st_list_ok stl` by METIS_TAC [step_invariant,step_invariant_out_of_order_step_list_ok] >>
   `State_st_list_well_formed_ok stl`
    by METIS_TAC [step_invariant,step_invariant_out_of_order_step_list_well_formed_ok] >>
   Q.ABBREV_TAC `pi0 = pi ++ [(State_st_list l s cs fs,ll,stl)]` >>
   `State_st_list_well_formed_ok (SND (SND (LAST pi0)))` by fs [Abbr `pi0`] >>

   sg `in_order_step_list (State_st_list l s cs fs) ll stl` >-
    (`ll = ll_lb (obs_il v) (act_ftc_list (translate_val_list v (max_bound_name_list l))) t /\
      stl = State_st_list (l ++ translate_val_list v (max_bound_name_list l)) s cs (t::fs)`
      by METIS_TAC [OoO_Ftc_list_stored_incomplete_result_form] >>
     rw [in_order_step_list,IO_step_list] >>
     fs [out_of_order_step_list] >>
     rw [EVERY_MEM] >>
     fs [MEM_FILTER] >>
     `bound_name_instr i < t` by DECIDE_TAC >>
     `Completed_list sem_expr (State_st_list l s cs fs) i`
      suffices_by rw [Completed_list_correct] >>
     `MEM i l` by fs [state_list_to_state,instr_in_State] >>
     `MEM i (TAKE pos l)` suffices_by fs [Completed_list_up_to] >>
     `MEM i (TAKE pos l) \/ MEM i (DROP pos l)`
      by METIS_TAC [TAKE_DROP,MEM_APPEND] >>
     `i <> i_assign t c (o_store res_PC ta tv)` by (Cases_on `i` >> fs [bound_name_instr]) >>
     `MEM i (i_assign t c (o_store res_PC ta tv)::l')` by METIS_TAC [] >>
     fs [] >> rw [] >>
     sg `SORTED bound_name_instr_le ((TAKE pos l ++ [i_assign t c (o_store res_PC ta tv)]) ++ l')` >-
      (`(TAKE pos l ++ [i_assign t c (o_store res_PC ta tv)]) ++ l' = l` suffices_by rw [] >>
       `l = TAKE pos l ++ (i_assign t c (o_store res_PC ta tv)::l')` by METIS_TAC [TAKE_DROP] >>
       once_rewrite_tac [GSYM APPEND_ASSOC] >>
       `[i_assign t c (o_store res_PC ta tv)] ++ l' = i_assign t c (o_store res_PC ta tv)::l'` by rw [] >>
       METIS_TAC []) >>
     `!x y. MEM x (TAKE pos l ++ [i_assign t c (o_store res_PC ta tv)]) ==> MEM y l' ==> bound_name_instr_le x y`
      by METIS_TAC [SORTED_APPEND,transitive_bound_name_instr_le] >>
     `MEM (i_assign t c (o_store res_PC ta tv)) (TAKE pos l ++ [i_assign t c (o_store res_PC ta tv)])` by rw [] >>
     `bound_name_instr_le (i_assign t c (o_store res_PC ta tv)) i` by METIS_TAC [] >>
     fs [bound_name_instr_le,name_le,bound_name_instr]) >>

   sg `step_execution in_order_step_list pi0` >-
    (fs [Abbr `pi0`,step_list_to_step] >>
     `pi <> []` by METIS_TAC [step_execution_not_empty_list] >>
     `pi = [] \/ ?e pi1. pi = SNOC e pi1` by fs [SNOC_CASES] >> fs [SNOC_APPEND] >>
     Cases_on `e` >> fs [] >> Cases_on `r` >> rename1 `(stl1,ll1,stl2)` >>
     fs [step_list_to_step] >> rw [] >>
     `pi1 ++ [(stl1,ll1,State_st_list l s cs fs)] ++ [(State_st_list l s cs fs,ll,stl)] =
       pi1 ++ [(stl1,ll1,State_st_list l s cs fs);(State_st_list l s cs fs,ll,stl)]`
      by fs [] >>
     rw [] >> METIS_TAC [step_execution_rules]) >>

   `SND (SND (LAST pi0)) = stl` by fs [Abbr `pi0`] >>

   sg `SORTED bound_name_instr_le (l ++ translate_val_list v (max_bound_name_list l))` >-
    (`!x y. MEM x l ==> MEM y (translate_val_list v (max_bound_name_list l)) ==> bound_name_instr_le x y`
       suffices_by METIS_TAC [SORTED_APPEND,transitive_bound_name_instr_le] >>
     rw [bound_name_instr_le,name_le] >>
     `bound_name_instr x < bound_name_instr y` suffices_by rw [] >>
     `y IN (translate_val v (MAX_SET (bound_names_program (set l))))`
       by METIS_TAC [translate_val_list_correct,max_bound_name_list_correct] >>
     `FINITE (set l)` by rw [] >>
     METIS_TAC [translate_val_max_name_lt]) >>

   sg `Completed_list sem_expr stl (i_assign t c (o_store res_PC ta tv))` >-
    (`stl = State_st_list (l ++ translate_val_list v (max_bound_name_list l)) s cs (t::fs)`
      by METIS_TAC [OoO_Ftc_list_stored_incomplete_result_form] >>
     rw [Completed_list]) >>

   sg `Completed_list_up_to sem_expr stl (SUC pos)` >-
    (`stl = State_st_list (l ++ translate_val_list v (max_bound_name_list l)) s cs (t::fs)`
      by METIS_TAC [OoO_Ftc_list_stored_incomplete_result_form] >>
     rw [Completed_list_up_to] >>
     `DROP pos (l ++ translate_val_list v (max_bound_name_list l)) =
       i_assign t c (o_store res_PC ta tv)::l' ++ translate_val_list v (max_bound_name_list l)`
      by rw [DROP_CONS_APPEND] >>
     `TAKE (SUC pos) (l ++ translate_val_list v (max_bound_name_list l)) =
       SNOC (i_assign t c (o_store res_PC ta tv)) (TAKE pos (l ++ translate_val_list v (max_bound_name_list l)))`
      by rw [DROP_TAKE_SNOC] >>
     fs [] >>
     `MEM i (TAKE pos l)` by METIS_TAC [DROP_CONS_TAKE_APPEND] >>
     `MEM i l` by METIS_TAC [MEM_TAKE] >>

     `Completed_list sem_expr (State_st_list l s cs fs) i`
      by fs [Completed_list_up_to] >>
     `Completed (state_list_to_state (State_st_list l s cs fs)) i`
      by fs [Completed_list_correct] >>
     `Completed_t (state_list_to_state (State_st_list l s cs fs)) (bound_name_instr i)`
      by (fs [state_list_to_state] >> rw [Completed_t] >> METIS_TAC []) >>

     `Completed_t (state_list_to_state (State_st_list (l ++ translate_val_list v (max_bound_name_list l))
       s cs (t::fs))) (bound_name_instr i)`
       by METIS_TAC [state_list_to_state,
        out_of_order_step_list_sound,
        well_formed_state_OoO_completed_t_preserved,
        State_st_list_well_formed_ok] >>

     `Completed (state_list_to_state (State_st_list (l ++ translate_val_list v (max_bound_name_list l))
       s cs (t::fs))) i` suffices_by METIS_TAC [Completed_list_correct] >>
     sg `!i'. MEM i' (translate_val_list v (max_bound_name_list l)) ==> bound_name_instr i < bound_name_instr i'` >-
      (`FINITE (set l)` by rw [] >>
       rw [] >>
       `i' IN (translate_val v (MAX_SET (bound_names_program (set l))))`
        by METIS_TAC [translate_val_list_correct,max_bound_name_list_correct] >>
       METIS_TAC [translate_val_max_name_lt]) >>
     fs [state_list_to_state,Completed_t,State_st_list_well_formed_ok] >-
     METIS_TAC [wfs_unique_instr_names] >>
     `bound_name_instr i < bound_name_instr i` suffices_by DECIDE_TAC >>
     METIS_TAC []) >>

   `stl = State_st_list (l ++ translate_val_list v (max_bound_name_list l)) s cs (t::fs)`
    by METIS_TAC [OoO_Ftc_list_stored_incomplete_result_form] >>
   rw [] >>
   Q.PAT_X_ASSUM `!l s cs. P`
    (STRIP_ASSUME_TAC o (Q.SPECL [`l ++ translate_val_list v (max_bound_name_list l)`,
     `s`,`cs`,`t::fs`,`SUC pos`, `pi0`,`pi'`])) >>
   `?pi''. pi' = pi0 ++ pi'' /\
     step_execution in_order_step_list pi' /\
     Completed_list_up_to sem_expr (SND (SND (LAST pi'))) (n + SUC pos) /\
     LENGTH pi'' <= 2 * n` by fs [Abbr `pi0`] >>
   Q.EXISTS_TAC `(State_st_list l s cs fs,ll, State_st_list
     (l ++ translate_val_list v (max_bound_name_list l)) s cs (t::fs))::pi''` >>
   `pos + SUC n = n + SUC pos` by DECIDE_TAC >>
   rw [Abbr `pi0`],

   `Completed_list sem_expr (State_st_list l s cs fs) (i_assign t c (o_store res_REG n' n0))`
    by rw [Completed_list] >>
   sg `Completed_list_up_to sem_expr (State_st_list l s cs fs) (SUC pos)` >-
    (rw [Completed_list_up_to] >>
     `TAKE (SUC pos) l = SNOC (i_assign t c (o_store res_REG n' n0)) (TAKE pos l)`
       by rw [DROP_TAKE_SNOC] >>
     fs [Completed_list_up_to]) >>
   Q.PAT_X_ASSUM `!l s cs. P`
    (STRIP_ASSUME_TAC o (Q.SPECL [`l`,`s`,`cs`,`fs`,`SUC pos`, `pi`,`pi'`])) >>
   `?pi''. pi' = pi ++ pi'' /\
     step_execution in_order_step_list pi' /\
     Completed_list_up_to sem_expr (SND (SND (LAST pi'))) (n + (SUC pos)) /\
     LENGTH pi'' ≤ 2 * n` by METIS_TAC [] >>
   Q.EXISTS_TAC `pi''` >> rw [] >>
   `pos + SUC n = n + SUC pos` by rw [] >>
   rw [],

   Cases_on `MEM t cs` >> fs [] >-
    (`Completed_list sem_expr (State_st_list l s cs fs) (i_assign t c (o_store res_MEM n' n0))`
      by rw [Completed_list] >>
     sg `Completed_list_up_to sem_expr (State_st_list l s cs fs) (SUC pos)` >-
      (rw [Completed_list_up_to] >>
       `TAKE (SUC pos) l = SNOC (i_assign t c (o_store res_MEM n' n0)) (TAKE pos l)`
        by rw [DROP_TAKE_SNOC] >>
       fs [Completed_list_up_to]) >>
     Q.PAT_X_ASSUM `!l s cs. P`
      (STRIP_ASSUME_TAC o (Q.SPECL [`l`,`s`,`cs`,`fs`,`SUC pos`, `pi`,`pi'`])) >>
     `?pi''. pi' = pi ++ pi'' /\
       step_execution in_order_step_list pi' /\
       Completed_list_up_to sem_expr (SND (SND (LAST pi'))) (n + (SUC pos)) /\
       LENGTH pi'' ≤ 2 * n` by METIS_TAC [] >>
     Q.EXISTS_TAC `pi''` >> rw [] >>
     `pos + SUC n = n + SUC pos` by rw [] >>
     rw []) >>

   rename1 `o_store res_MEM ta tv` >>
   Cases_on `OoO_Cmt_list_stored_incomplete sem_expr (State_st_list l s cs fs) t ta tv` >> fs [] >>
   Cases_on `x'` >> fs [] >> rename1 `(ll,stl)` >>
   rename1 `FLOOKUP s t = SOME v` >>
   `FLOOKUP s t <> NONE` by rw [FLOOKUP_DEF] >>
   `State_st_list_ok (State_st_list l s cs fs)` by fs [State_st_list_ok,State_st_list_well_formed_ok] >>   
   `out_of_order_step_list (State_st_list l s cs fs) ll stl`
    by METIS_TAC [OoO_Cmt_list_stored_incomplete_SOME_out_of_order_step_list] >>
   `State_st_list_ok stl` by METIS_TAC [step_invariant,step_invariant_out_of_order_step_list_ok] >>
   `State_st_list_well_formed_ok stl`
    by METIS_TAC [step_invariant,step_invariant_out_of_order_step_list_well_formed_ok] >>   
   Q.ABBREV_TAC `pi0 = pi ++ [(State_st_list l s cs fs,ll,stl)]` >>
   `State_st_list_well_formed_ok (SND (SND (LAST pi0)))` by fs [Abbr `pi0`] >>

   sg `in_order_step_list (State_st_list l s cs fs) ll stl` >-
    (`?a v. ll = ll_lb (obs_ds a) (act_cmt_list a v) t /\ stl = State_st_list l s (t::cs) fs`
      by METIS_TAC [OoO_Cmt_list_stored_incomplete_result_form] >>
     rw [in_order_step_list,IO_step_list] >>
     fs [out_of_order_step_list] >>
     rw [EVERY_MEM] >>
     fs [MEM_FILTER] >>
     `bound_name_instr i < t` by DECIDE_TAC >>
     `MEM i l` by fs [state_list_to_state,instr_in_State] >>
     `Completed_list sem_expr (State_st_list l s cs fs) i`
      suffices_by rw [Completed_list_correct] >>
     `MEM i (TAKE pos l)` suffices_by fs [Completed_list_up_to] >>
     `MEM i (TAKE pos l) \/ MEM i (DROP pos l)`
      by METIS_TAC [TAKE_DROP,MEM_APPEND] >>
     `i <> i_assign t c (o_store res_MEM ta tv)` by (Cases_on `i` >> fs [bound_name_instr]) >>
     `MEM i (i_assign t c (o_store res_MEM ta tv)::l')` by METIS_TAC [] >>
     fs [] >> rw [] >>
     sg `SORTED bound_name_instr_le ((TAKE pos l ++ [i_assign t c (o_store res_MEM ta tv)]) ++ l')` >-
      (`(TAKE pos l ++ [i_assign t c (o_store res_MEM ta tv)]) ++ l' = l` suffices_by rw [] >>
       `l = TAKE pos l ++ (i_assign t c (o_store res_MEM ta tv))::l'` by METIS_TAC [TAKE_DROP] >>
       once_rewrite_tac [GSYM APPEND_ASSOC] >>
       `[i_assign t c (o_store res_MEM ta tv)] ++ l' = i_assign t c (o_store res_MEM ta tv)::l'` by rw [] >>
       METIS_TAC []) >>
     `!x y. MEM x (TAKE pos l ++ [i_assign t c (o_store res_MEM ta tv)]) ==> MEM y l' ==> bound_name_instr_le x y`
      by METIS_TAC [SORTED_APPEND,transitive_bound_name_instr_le] >>
     `MEM (i_assign t c (o_store res_MEM ta tv)) (TAKE pos l ++ [i_assign t c (o_store res_MEM ta tv)])` by rw [] >>
     `bound_name_instr_le (i_assign t c (o_store res_MEM ta tv)) i` by METIS_TAC [] >>
     fs [bound_name_instr_le,name_le,bound_name_instr]) >>

   sg `step_execution in_order_step_list pi0` >-
    (fs [Abbr `pi0`,step_list_to_step] >>
     `pi <> []` by METIS_TAC [step_execution_not_empty_list] >>
     `pi = [] \/ ?e pi1. pi = SNOC e pi1` by fs [SNOC_CASES] >> fs [SNOC_APPEND] >>
     Cases_on `e` >> fs [] >> Cases_on `r` >> rename1 `(stl1,ll1,stl2)` >>
     fs [step_list_to_step] >> rw [] >>
     `pi1 ++ [(stl1,ll1,State_st_list l s cs fs)] ++ [(State_st_list l s cs fs,ll,stl)] =
       pi1 ++ [(stl1,ll1,State_st_list l s cs fs); (State_st_list l s cs fs,ll,stl)]`
      by fs [] >>
     rw [] >> METIS_TAC [step_execution_rules]) >>

   `SND (SND (LAST pi0)) = stl` by fs [Abbr `pi0`] >>
   `Completed_list sem_expr (State_st_list l s (t::cs) fs) (i_assign t c (o_store res_MEM ta tv))`
    by rw [Completed_list] >>

   sg `Completed_list_up_to sem_expr stl (SUC pos)` >-
    (`stl = State_st_list l s (t::cs) fs`
      by METIS_TAC [OoO_Cmt_list_stored_incomplete_result_form] >>
     rw [Completed_list_up_to] >>
     `TAKE (SUC pos) l = SNOC (i_assign t c (o_store res_MEM ta tv)) (TAKE pos l)`
      by rw [DROP_TAKE_SNOC] >>
     fs [Completed_list_up_to] >>
     `Completed_list sem_expr (State_st_list l s cs fs) i` by METIS_TAC [] >>
     `Completed (state_list_to_state (State_st_list l s cs fs)) i`
      by METIS_TAC [Completed_list_correct] >>
     `Completed (state_list_to_state (State_st_list l s (t::cs) fs)) i`
      suffices_by METIS_TAC [Completed_list_correct] >>
     `MEM i l` by METIS_TAC [MEM_TAKE] >>
     `Completed_t (state_list_to_state (State_st_list l s cs fs)) (bound_name_instr i)`
      by (fs [state_list_to_state] >> rw [Completed_t] >> METIS_TAC []) >>
     `Completed_t (state_list_to_state (State_st_list l s (t::cs) fs)) (bound_name_instr i)`
      by METIS_TAC [state_list_to_state,
       out_of_order_step_list_sound,
       well_formed_state_OoO_completed_t_preserved,
       State_st_list_well_formed_ok] >>
     fs [state_list_to_state,Completed_t,State_st_list_well_formed_ok,Abbr `pi0`] >>
     METIS_TAC [wfs_unique_instr_names]) >>

   `stl = State_st_list l s (t::cs) fs`
    by METIS_TAC [OoO_Cmt_list_stored_incomplete_result_form] >>
   rw [] >>
   Q.PAT_X_ASSUM `!l s cs. P`
    (STRIP_ASSUME_TAC o (Q.SPECL [`l`,`s`,`t::cs`,`fs`,`SUC pos`, `pi0`,`pi'`])) >>
   `?pi''. pi' = pi0 ++ pi'' /\
     step_execution in_order_step_list pi' /\
     Completed_list_up_to sem_expr (SND (SND (LAST pi'))) (n + SUC pos) /\
     LENGTH pi'' <= 2 * n` by fs [Abbr `pi0`] >>
   Q.EXISTS_TAC `(State_st_list l s cs fs,ll,State_st_list l s (t::cs) fs)::pi''` >>
   `pos + SUC n = n + SUC pos` by DECIDE_TAC >>
   rw [Abbr `pi0`]
  ]
 ]
QED

Theorem IO_bounded_execution_acc_IO_empty_sound:
 translate_val_list_SORTED ==>
 !n l s cs fs i il pos pi.
  State_st_list_well_formed_ok (State_st_list l s cs fs) ==>
  SORTED bound_name_instr_le l ==>
  Completed_list_up_to sem_expr (State_st_list l s cs fs) pos ==>
  DROP pos l = i::il ==>
  ~(Completed_list sem_expr (State_st_list l s cs fs) i) ==>
  IO_bounded_execution_acc translate_val_list sem_expr (State_st_list l s cs fs) pos (SUC n) [] = SOME pi ==>
  step_execution_list_IO_HD (State_st_list l s cs fs) pi pos (SUC n)
Proof
 once_rewrite_tac [translate_val_list_SORTED] >>
 once_rewrite_tac [IO_bounded_execution_acc] >>
 fs [] >> rw [] >>
 Cases_on `i` >> rename1 `i_assign t c mop` >> fs [] >>
 `MEM (i_assign t c mop) l` by METIS_TAC [DROP_HEAD_MEM] >>
 `FIND_instr t l = SOME (i_assign t c mop)`
  by METIS_TAC [State_st_list_well_formed_ok,State_st_list_ok,NO_DUPLICATES_FIND_instr,bound_name_instr] >>
 Cases_on `FLOOKUP s t` >> fs [] >> Cases_on `mop` >> fs [Completed_list] >| [
  Cases_on `sem_expr c s` >> fs [] >>
  rename1 `v <> val_false` >>
  Cases_on `v = val_false` >> fs [] >>
  Cases_on `sem_instr_exe sem_expr (i_assign t c (o_internal e)) (State_st_list l s cs fs)` >> fs [] >>
  Cases_on `x` >> fs [] >> rename1 `(v',obs)` >>
  Cases_on `OoO_Exe_list_instr_not_stored_guard_true_sem_instr
   (State_st_list l s cs fs) (i_assign t c (o_internal e)) v' obs` >>
  fs [] >> rename1 `(ll,stl)` >>

  `State_st_list_ok (State_st_list l s cs fs)` by fs [State_st_list_ok,State_st_list_well_formed_ok] >>   
  `out_of_order_step_list (State_st_list l s cs fs) ll stl`
   by METIS_TAC [OoO_Exe_list_instr_not_stored_guard_true_sem_instr_SOME_out_of_order_step_list] >>
  `State_st_list_ok stl` by METIS_TAC [step_invariant,step_invariant_out_of_order_step_list_ok] >>
  `State_st_list_well_formed_ok stl`
   by METIS_TAC [step_invariant,step_invariant_out_of_order_step_list_well_formed_ok] >>

  sg `in_order_step_list (State_st_list l s cs fs) ll stl` >-
   (`ll = ll_lb obs act_exe_list t /\ stl = State_st_list l (s |+ (t,v')) cs fs`
     by METIS_TAC [OoO_Exe_list_instr_not_stored_guard_true_sem_instr_result_form] >>
    rw [in_order_step_list,IO_step_list] >>
    fs [out_of_order_step_list] >>
    rw [EVERY_MEM] >>
    fs [MEM_FILTER] >>
    `bound_name_instr i < t` by DECIDE_TAC >>
    `MEM i l` by fs [state_list_to_state,instr_in_State] >>

    `Completed_list sem_expr (State_st_list l s cs fs) i`
     suffices_by rw [Completed_list_correct] >>
    `MEM i (TAKE pos l)` suffices_by fs [Completed_list_up_to] >>
    `MEM i (TAKE pos l) \/ MEM i (DROP pos l)`
     by METIS_TAC [TAKE_DROP,MEM_APPEND] >>
    `i <> i_assign t c (o_internal e)` by (Cases_on `i` >> fs [bound_name_instr]) >>
    `MEM i (i_assign t c (o_internal e)::il)` by METIS_TAC [] >>
    fs [] >> rw [] >>

    sg `SORTED bound_name_instr_le ((TAKE pos l ++ [i_assign t c (o_internal e)]) ++ il)` >-
     (`(TAKE pos l ++ [i_assign t c (o_internal e)]) ++ il = l` suffices_by rw [] >>
      `l = TAKE pos l ++ (i_assign t c (o_internal e)::il)` by METIS_TAC [TAKE_DROP] >>
      once_rewrite_tac [GSYM APPEND_ASSOC] >>
      `[i_assign t c (o_internal e)] ++ il = i_assign t c (o_internal e)::il` by rw [] >>
      METIS_TAC []) >>
    `!x y. MEM x (TAKE pos l ++ [i_assign t c (o_internal e)]) ==> MEM y il ==> bound_name_instr_le x y`
     by METIS_TAC [SORTED_APPEND,transitive_bound_name_instr_le] >>
    `MEM (i_assign t c (o_internal e)) (TAKE pos l ++ [i_assign t c (o_internal e)])` by rw [] >>
    `bound_name_instr_le (i_assign t c (o_internal e)) i` by METIS_TAC [] >>
    fs [bound_name_instr_le,name_le,bound_name_instr]) >>

  `step_execution in_order_step_list [(State_st_list l s cs fs,ll,stl)]`
   by (fs [step_list_to_step] >> METIS_TAC [step_execution_rules]) >>
  `SND (SND (LAST [(State_st_list l s cs fs,ll,stl)])) = stl` by fs [] >>
  sg `Completed_list sem_expr stl (i_assign t c (o_internal e))` >-
   (fs [OoO_Exe_list_instr_not_stored_guard_true_sem_instr] >>
    rw [Completed_list,FLOOKUP_DEF]) >>
  sg `Completed_list_up_to sem_expr stl (SUC pos)` >-
   (`stl = State_st_list l (s |+ (t,v')) cs fs`
     by METIS_TAC [OoO_Exe_list_instr_not_stored_guard_true_sem_instr_result_form] >>
    rw [Completed_list_up_to] >>
    `MEM i l` by METIS_TAC [MEM_TAKE] >>
    `TAKE (SUC pos) l = SNOC (i_assign t c (o_internal e)) (TAKE pos l)`
     by rw [DROP_TAKE_SNOC] >>
    fs [] >>
    `Completed_list sem_expr (State_st_list l s cs fs) i`
     by fs [Completed_list_up_to] >>
    `Completed (state_list_to_state (State_st_list l s cs fs)) i`
     by METIS_TAC [Completed_list_correct] >>
    `Completed (state_list_to_state (State_st_list l (s |+ (t,v')) cs fs)) i`
     suffices_by METIS_TAC [Completed_list_correct] >>
    `Completed_t (state_list_to_state (State_st_list l s cs fs)) (bound_name_instr i)`
     by (fs [state_list_to_state] >> rw [Completed_t] >> METIS_TAC []) >>

    `Completed_t (state_list_to_state (State_st_list l (s |+ (t,v')) cs fs)) (bound_name_instr i)`
       by METIS_TAC [state_list_to_state,
        out_of_order_step_list_sound,
        well_formed_state_OoO_completed_t_preserved,
        State_st_list_well_formed_ok] >>

    fs [state_list_to_state,Completed_t,State_st_list_well_formed_ok] >>
    METIS_TAC [wfs_unique_instr_names]) >>

  `stl = State_st_list l (s |+ (t,v')) cs fs`
   by METIS_TAC [OoO_Exe_list_instr_not_stored_guard_true_sem_instr_result_form] >>
  rw [] >>
  `?pi'. pi = [(State_st_list l s cs fs,ll,State_st_list l (s |+ (t,v')) cs fs)] ++ pi' /\
    step_execution in_order_step_list pi /\
    Completed_list_up_to sem_expr (SND (SND (LAST pi))) (SUC pos + n) /\
    LENGTH pi' <= 2 * n`
   by METIS_TAC [IO_bounded_execution_acc_IO_execution_sound,translate_val_list_SORTED] >>
  `FST (HD ([(State_st_list l s cs fs,ll,State_st_list l (s |+ (t,v')) cs fs)] ++ pi')) =
    State_st_list l s cs fs` by fs [] >>
  `LENGTH pi <= 2 * SUC n` by rw [] >>
  `SUC pos + n = pos + SUC n` by rw [] >>
  METIS_TAC [step_execution_list_IO_HD],

  Cases_on `sem_expr c s` >> fs [] >>
  rename1 `v <> val_false` >>
  Cases_on `v = val_false` >> fs [] >>
  Cases_on `sem_instr_exe sem_expr (i_assign t c (o_load r n')) (State_st_list l s cs fs)` >> fs [] >>
  Cases_on `x` >> fs [] >> rename1 `(v',obs)` >>
  Cases_on `OoO_Exe_list_instr_not_stored_guard_true_sem_instr
   (State_st_list l s cs fs) (i_assign t c (o_load r n')) v' obs` >>
  fs [] >> rename1 `(ll,stl)` >>
  
  `State_st_list_ok (State_st_list l s cs fs)` by fs [State_st_list_ok,State_st_list_well_formed_ok] >>   
  `out_of_order_step_list (State_st_list l s cs fs) ll stl`
   by METIS_TAC [OoO_Exe_list_instr_not_stored_guard_true_sem_instr_SOME_out_of_order_step_list] >>
  `State_st_list_ok stl` by METIS_TAC [step_invariant,step_invariant_out_of_order_step_list_ok] >>
  `State_st_list_well_formed_ok stl`
   by METIS_TAC [step_invariant,step_invariant_out_of_order_step_list_well_formed_ok] >>

  sg `in_order_step_list (State_st_list l s cs fs) ll stl` >-
   (`ll = ll_lb obs act_exe_list t /\ stl = State_st_list l (s |+ (t,v')) cs fs`
     by METIS_TAC [OoO_Exe_list_instr_not_stored_guard_true_sem_instr_result_form] >>
    rw [in_order_step_list,IO_step_list] >>
    fs [out_of_order_step_list] >>
    rw [EVERY_MEM] >>
    fs [MEM_FILTER] >>
    `bound_name_instr i < t` by DECIDE_TAC >>
    `MEM i l` by fs [state_list_to_state,instr_in_State] >>

    `Completed_list sem_expr (State_st_list l s cs fs) i`
     suffices_by rw [Completed_list_correct] >>
    `MEM i (TAKE pos l)` suffices_by fs [Completed_list_up_to] >>
    `MEM i (TAKE pos l) \/ MEM i (DROP pos l)`
     by METIS_TAC [TAKE_DROP,MEM_APPEND] >>
    `i <> i_assign t c (o_load r n')` by (Cases_on `i` >> fs [bound_name_instr]) >>
    `MEM i (i_assign t c (o_load r n')::il)` by METIS_TAC [] >>
    fs [] >> rw [] >>
    sg `SORTED bound_name_instr_le ((TAKE pos l ++ [i_assign t c (o_load r n')]) ++ il)` >-
     (`(TAKE pos l ++ [i_assign t c (o_load r n')]) ++ il = l` suffices_by rw [] >>
      `l = TAKE pos l ++ (i_assign t c (o_load r n')::il)` by METIS_TAC [TAKE_DROP] >>
      once_rewrite_tac [GSYM APPEND_ASSOC] >>
      `[i_assign t c (o_load r n')] ++ il = i_assign t c (o_load r n')::il` by rw [] >>
      METIS_TAC []) >>
    `!x y. MEM x (TAKE pos l ++ [i_assign t c (o_load r n')]) ==> MEM y il ==> bound_name_instr_le x y`
     by METIS_TAC [SORTED_APPEND,transitive_bound_name_instr_le] >>
    `MEM (i_assign t c (o_load r n')) (TAKE pos l ++ [i_assign t c (o_load r n')])` by rw [] >>
    `bound_name_instr_le (i_assign t c (o_load r n')) i` by METIS_TAC [] >>
    fs [bound_name_instr_le,name_le,bound_name_instr]) >>

  `step_execution in_order_step_list [(State_st_list l s cs fs,ll,stl)]`
   by (fs [step_list_to_step] >> METIS_TAC [step_execution_rules]) >>
  `SND (SND (LAST [(State_st_list l s cs fs,ll,stl)])) = stl` by fs [] >>
  sg `Completed_list sem_expr stl (i_assign t c (o_load r n'))` >-
   (fs [OoO_Exe_list_instr_not_stored_guard_true_sem_instr] >>
    rw [Completed_list,FLOOKUP_DEF]) >>

  sg `Completed_list_up_to sem_expr stl (SUC pos)` >-
   (`stl = State_st_list l (s |+ (t,v')) cs fs`
     by METIS_TAC [OoO_Exe_list_instr_not_stored_guard_true_sem_instr_result_form] >>
    rw [Completed_list_up_to] >>
    `MEM i l` by METIS_TAC [MEM_TAKE] >>
    `TAKE (SUC pos) l = SNOC (i_assign t c (o_load r n')) (TAKE pos l)`
     by rw [DROP_TAKE_SNOC] >>
    fs [] >>
    `Completed_list sem_expr (State_st_list l s cs fs) i`
     by fs [Completed_list_up_to] >>
    `Completed (state_list_to_state (State_st_list l s cs fs)) i`
     by METIS_TAC [Completed_list_correct] >>
    `Completed (state_list_to_state (State_st_list l (s |+ (t,v')) cs fs)) i`
     suffices_by METIS_TAC [Completed_list_correct] >>
    `Completed_t (state_list_to_state (State_st_list l s cs fs)) (bound_name_instr i)`
     by (fs [state_list_to_state] >> rw [Completed_t] >> METIS_TAC []) >>

    `Completed_t (state_list_to_state (State_st_list l (s |+ (t,v')) cs fs)) (bound_name_instr i)`
       by METIS_TAC [state_list_to_state,
        out_of_order_step_list_sound,
        well_formed_state_OoO_completed_t_preserved,
        State_st_list_well_formed_ok] >>

    fs [state_list_to_state,Completed_t,State_st_list_well_formed_ok] >>
    METIS_TAC [wfs_unique_instr_names]) >>

  `stl = State_st_list l (s |+ (t,v')) cs fs`
   by METIS_TAC [OoO_Exe_list_instr_not_stored_guard_true_sem_instr_result_form] >>
  rw [] >>
  `?pi'. pi = [(State_st_list l s cs fs,ll,State_st_list l (s |+ (t,v')) cs fs)] ++ pi' /\
    step_execution in_order_step_list pi /\
    Completed_list_up_to sem_expr (SND (SND (LAST pi))) (SUC pos + n) /\
    LENGTH pi' <= 2 * n`
   by METIS_TAC [IO_bounded_execution_acc_IO_execution_sound,translate_val_list_SORTED] >>
  `FST (HD ([(State_st_list l s cs fs,ll,State_st_list l (s |+ (t,v')) cs fs)] ++ pi')) =
    State_st_list l s cs fs` by fs [] >>
  `LENGTH pi <= 2 * SUC n` by rw [] >>
  `SUC pos + n = pos + SUC n` by rw [] >>
  METIS_TAC [step_execution_list_IO_HD],

  Cases_on `sem_expr c s` >> fs [] >>
  rename1 `v <> val_false` >>
  Cases_on `v = val_false` >> Cases_on `r` >> fs [Completed_list] >| [
   rename1 `o_store res_PC ta tv` >>
   Cases_on `sem_instr_exe sem_expr (i_assign t c (o_store res_PC ta tv)) (State_st_list l s cs fs)` >> fs [] >>
   Cases_on `x` >> fs [] >> rename1 `(v',obs)` >>
   Cases_on `OoO_Exe_list_instr_not_stored_guard_true_sem_instr (State_st_list l s cs fs) (i_assign t c (o_store res_PC ta tv)) v' obs` >> fs [] >>
   rename1 `(ll,stl)` >>
   Cases_on `OoO_Ftc_list_stored translate_val_list sem_expr stl t v'` >> fs [] >>
   Cases_on `x` >> fs [] >> rename1 `(ll',stl')` >>

   `State_st_list_ok (State_st_list l s cs fs)` by fs [State_st_list_ok,State_st_list_well_formed_ok] >>   
   `out_of_order_step_list (State_st_list l s cs fs) ll stl`
    by METIS_TAC [OoO_Exe_list_instr_not_stored_guard_true_sem_instr_SOME_out_of_order_step_list] >>
   `State_st_list_ok stl` by METIS_TAC [step_invariant,step_invariant_out_of_order_step_list_ok] >>
   `State_st_list_well_formed_ok stl`
    by METIS_TAC [step_invariant,step_invariant_out_of_order_step_list_well_formed_ok] >>

   `stl = State_st_list l (s |+ (t,v')) cs fs`
    by METIS_TAC [OoO_Exe_list_instr_not_stored_guard_true_sem_instr_result_form] >>
   rw [] >>
   `FLOOKUP (s |+ (t,v')) t = SOME v'` by fs [FLOOKUP_UPDATE] >>
   `FLOOKUP (s |+ (t,v')) t <> NONE` by fs [] >>

   `out_of_order_step_list (State_st_list l (s |+ (t,v')) cs fs) ll' stl'`
    by METIS_TAC [OoO_Ftc_list_stored_SOME_out_of_order_step_list] >>
   `State_st_list_ok stl'` by METIS_TAC [step_invariant,step_invariant_out_of_order_step_list_ok] >>
   `State_st_list_well_formed_ok stl'`
    by METIS_TAC [step_invariant,step_invariant_out_of_order_step_list_well_formed_ok] >>

   Q.ABBREV_TAC `pi0 = [(State_st_list l s cs fs,ll,State_st_list l (s |+ (t,v')) cs fs);
    (State_st_list l (s |+ (t,v')) cs fs,ll',stl')]` >>
   `SND (SND (LAST pi0)) = stl'` by fs [Abbr `pi0`] >>

   sg `in_order_step_list (State_st_list l s cs fs) ll
      (State_st_list l (s |+ (t,v')) cs fs)` >-
    (`ll = ll_lb obs act_exe_list t`
      by METIS_TAC [OoO_Exe_list_instr_not_stored_guard_true_sem_instr_result_form] >>
     rw [in_order_step_list,IO_step_list] >>
     fs [out_of_order_step_list] >>
     rw [EVERY_MEM] >>
     fs [MEM_FILTER] >>
     `bound_name_instr i < t` by DECIDE_TAC >>
     `MEM i l` by fs [state_list_to_state,instr_in_State] >>
     
     `Completed_list sem_expr (State_st_list l s cs fs) i`
      suffices_by rw [Completed_list_correct] >>
     `MEM i (TAKE pos l)` suffices_by fs [Completed_list_up_to] >>
     `MEM i (TAKE pos l) \/ MEM i (DROP pos l)`
      by METIS_TAC [TAKE_DROP,MEM_APPEND] >>
     `i <> i_assign t c (o_store res_PC ta tv)` by (Cases_on `i` >> fs [bound_name_instr]) >>
     `MEM i (i_assign t c (o_store res_PC ta tv)::il)` by METIS_TAC [] >>
     fs [] >> rw [] >>
     sg `SORTED bound_name_instr_le ((TAKE pos l ++ [i_assign t c (o_store res_PC ta tv)]) ++ il)` >-
      (`(TAKE pos l ++ [i_assign t c (o_store res_PC ta tv)]) ++ il = l` suffices_by rw [] >>
       `l = TAKE pos l ++ (i_assign t c (o_store res_PC ta tv)::il)` by METIS_TAC [TAKE_DROP] >>
       once_rewrite_tac [GSYM APPEND_ASSOC] >>
       `[i_assign t c (o_store res_PC ta tv)] ++ il = i_assign t c (o_store res_PC ta tv)::il` by rw [] >>
       METIS_TAC []) >>
     `!x y. MEM x (TAKE pos l ++ [i_assign t c (o_store res_PC ta tv)]) ==> MEM y il ==> bound_name_instr_le x y`
      by METIS_TAC [SORTED_APPEND,transitive_bound_name_instr_le] >>
     `MEM (i_assign t c (o_store res_PC ta tv)) (TAKE pos l ++ [i_assign t c (o_store res_PC ta tv)])` by rw [] >>
     `bound_name_instr_le (i_assign t c (o_store res_PC ta tv)) i` by METIS_TAC [] >>
     fs [bound_name_instr_le,name_le,bound_name_instr]) >>

   sg `Completed_list_up_to sem_expr (State_st_list l (s |+ (t,v')) cs fs) pos` >-
    (rw [Completed_list_up_to] >>
     `MEM i l` by METIS_TAC [MEM_TAKE] >>
     `Completed_list sem_expr (State_st_list l s cs fs) i`
      by fs [Completed_list_up_to] >>
     `Completed (state_list_to_state (State_st_list l s cs fs)) i`
      by METIS_TAC [Completed_list_correct] >>
     `Completed (state_list_to_state (State_st_list l (s |+ (t,v')) cs fs)) i`
      suffices_by METIS_TAC [Completed_list_correct] >>
     `Completed_t (state_list_to_state (State_st_list l s cs fs)) (bound_name_instr i)`
      by (fs [state_list_to_state] >> rw [Completed_t] >> METIS_TAC []) >>

     `Completed_t (state_list_to_state (State_st_list l (s |+ (t,v')) cs fs)) (bound_name_instr i)`
       by METIS_TAC [state_list_to_state,
        out_of_order_step_list_sound,
        well_formed_state_OoO_completed_t_preserved,
        State_st_list_well_formed_ok] >>

     fs [state_list_to_state,Completed_t,State_st_list_well_formed_ok] >>
     METIS_TAC [wfs_unique_instr_names]) >>

   sg `in_order_step_list (State_st_list l (s |+ (t,v')) cs fs) ll' stl'` >-
    (`ll' = ll_lb (obs_il v') (act_ftc_list (translate_val_list v' (max_bound_name_list l))) t /\
      stl' = State_st_list (l ++ translate_val_list v' (max_bound_name_list l)) (s |+ (t,v')) cs (t::fs)`
      by METIS_TAC [OoO_Ftc_list_stored_result_form] >>
     rw [in_order_step_list,IO_step_list] >>
     fs [out_of_order_step_list] >>
     rw [EVERY_MEM] >>
     fs [MEM_FILTER] >>
     `bound_name_instr i < t` by DECIDE_TAC >>
     `MEM i l` by fs [state_list_to_state,instr_in_State] >>

     `Completed_list sem_expr (State_st_list l (s |+ (t,v')) cs fs) i`
      suffices_by rw [Completed_list_correct] >>
     `MEM i l` by fs [state_list_to_state,instr_in_State] >>
     `MEM i (TAKE pos l)` suffices_by fs [Completed_list_up_to] >>
     `MEM i (TAKE pos l) \/ MEM i (DROP pos l)`
      by METIS_TAC [TAKE_DROP,MEM_APPEND] >>
     `i <> i_assign t c (o_store res_PC ta tv)` by (Cases_on `i` >> fs [bound_name_instr]) >>
     `MEM i (i_assign t c (o_store res_PC ta tv)::il)` by METIS_TAC [] >>
     fs [] >> rw [] >>
     sg `SORTED bound_name_instr_le ((TAKE pos l ++ [i_assign t c (o_store res_PC ta tv)]) ++ il)` >-
      (`(TAKE pos l ++ [i_assign t c (o_store res_PC ta tv)]) ++ il = l` suffices_by rw [] >>
       `l = TAKE pos l ++ (i_assign t c (o_store res_PC ta tv)::il)` by METIS_TAC [TAKE_DROP] >>
       once_rewrite_tac [GSYM APPEND_ASSOC] >>
       `[i_assign t c (o_store res_PC ta tv)] ++ il = i_assign t c (o_store res_PC ta tv)::il` by rw [] >>
       METIS_TAC []) >>
     `!x y. MEM x (TAKE pos l ++ [i_assign t c (o_store res_PC ta tv)]) ==> MEM y il ==> bound_name_instr_le x y`
      by METIS_TAC [SORTED_APPEND,transitive_bound_name_instr_le] >>
     `MEM (i_assign t c (o_store res_PC ta tv)) (TAKE pos l ++ [i_assign t c (o_store res_PC ta tv)])` by rw [] >>
     `bound_name_instr_le (i_assign t c (o_store res_PC ta tv)) i` by METIS_TAC [] >>
     fs [bound_name_instr_le,name_le,bound_name_instr]) >>

   sg `step_execution in_order_step_list pi0` >-
    (rw [Abbr `pi0`,step_list_to_step] >>
     `step_execution in_order_step_list ([] ++
       [(State_st_list l s cs fs,ll,State_st_list l (s |+ (t,v')) cs fs);
        (State_st_list l (s |+ (t,v')) cs fs,ll',stl')])`
      suffices_by fs [] >>
     `step_execution in_order_step_list ([] ++
       [(State_st_list l s cs fs,ll,State_st_list l (s |+ (t,v')) cs fs)])`
      suffices_by METIS_TAC [step_execution_rules] >>
     fs [] >> METIS_TAC [step_execution_rules]) >>

   sg `Completed_list sem_expr stl' (i_assign t c (o_store res_PC ta tv))` >-
    (`stl' = State_st_list (l ++ translate_val_list v' (max_bound_name_list l)) (s |+ (t,v')) cs (t::fs)`
      by METIS_TAC [OoO_Ftc_list_stored_result_form] >>
     rw [Completed_list]) >>

   sg `Completed_list_up_to sem_expr stl' (SUC pos)` >-
    (`stl' = State_st_list (l ++ translate_val_list v' (max_bound_name_list l)) (s |+ (t,v')) cs (t::fs)`
      by METIS_TAC [OoO_Ftc_list_stored_result_form] >>
     rw [Completed_list_up_to] >>
     `DROP pos (l ++ translate_val_list v' (max_bound_name_list l)) =
       i_assign t c (o_store res_PC ta tv)::il ++ translate_val_list v' (max_bound_name_list l)`
      by rw [DROP_CONS_APPEND] >>
     `TAKE (SUC pos) (l ++ translate_val_list v' (max_bound_name_list l)) =
       SNOC (i_assign t c (o_store res_PC ta tv)) (TAKE pos (l ++ translate_val_list v' (max_bound_name_list l)))`
      by rw [DROP_TAKE_SNOC] >>
     fs [] >>
     `MEM i (TAKE pos l)` by METIS_TAC [DROP_CONS_TAKE_APPEND] >>
     `Completed_list sem_expr (State_st_list l (s |+ (t,v')) cs fs) i`
      by fs [Completed_list_up_to] >>
     `Completed (state_list_to_state (State_st_list l (s |+ (t,v')) cs fs)) i`
      by fs [Completed_list_correct] >>
     `MEM i l` by METIS_TAC [MEM_TAKE] >>
     `Completed_t (state_list_to_state (State_st_list l (s |+ (t,v')) cs fs)) (bound_name_instr i)`
      by (fs [state_list_to_state] >> rw [Completed_t] >> METIS_TAC []) >>

     `Completed_t (state_list_to_state (State_st_list (l ++ translate_val_list v' (max_bound_name_list l))
       (s |+ (t,v')) cs (t::fs))) (bound_name_instr i)`
       by METIS_TAC [state_list_to_state,
        out_of_order_step_list_sound,
        well_formed_state_OoO_completed_t_preserved,
        State_st_list_well_formed_ok] >>

     `Completed (state_list_to_state (State_st_list (l ++ translate_val_list v' (max_bound_name_list l))
       (s |+ (t,v')) cs (t::fs))) i` suffices_by METIS_TAC [Completed_list_correct] >>
     sg `!i'. MEM i' (translate_val_list v' (max_bound_name_list l)) ==>
       bound_name_instr i < bound_name_instr i'` >-
      (`FINITE (set l)` by rw [] >>
       rw [] >>
       `i' IN (translate_val v' (MAX_SET (bound_names_program (set l))))`
        by METIS_TAC [translate_val_list_correct,max_bound_name_list_correct] >>
       METIS_TAC [translate_val_max_name_lt]) >>
     fs [state_list_to_state,Completed_t,State_st_list_well_formed_ok] >-
     METIS_TAC [wfs_unique_instr_names] >>
     `bound_name_instr i < bound_name_instr i` suffices_by DECIDE_TAC >>
     METIS_TAC []) >>

   sg `SORTED bound_name_instr_le (l ++ translate_val_list v' (max_bound_name_list l))` >-
    (`!x y. MEM x l ==> MEM y (translate_val_list v' (max_bound_name_list l)) ==> bound_name_instr_le x y`
       suffices_by METIS_TAC [SORTED_APPEND,transitive_bound_name_instr_le] >>
     rw [bound_name_instr_le,name_le] >>
     `bound_name_instr x < bound_name_instr y` suffices_by rw [] >>
     `y IN (translate_val v' (MAX_SET (bound_names_program (set l))))`
       by METIS_TAC [translate_val_list_correct,max_bound_name_list_correct] >>
     `FINITE (set l)` by rw [] >>
     METIS_TAC [translate_val_max_name_lt]) >>
   `stl' = State_st_list (l ++ translate_val_list v' (max_bound_name_list l)) (s |+ (t,v')) cs (t::fs)`
    by METIS_TAC [OoO_Ftc_list_stored_result_form] >>
   rw [Abbr `pi0`] >>

   (* FIXME: METIS problems *)
   sg `?pi'. pi = [(State_st_list l s cs fs,ll,State_st_list l (s |+ (t,v')) cs fs);
     (State_st_list l (s |+ (t,v')) cs fs,ll',State_st_list (l ++ translate_val_list v' (max_bound_name_list l))
       (s |+ (t,v')) cs (t::fs))] ++ pi' /\
     step_execution in_order_step_list pi /\
     Completed_list_up_to sem_expr (SND (SND (LAST pi))) (SUC pos + n) /\
     LENGTH pi' <= 2 * n` >-
    (`translate_val_list_SORTED` by rw [translate_val_list_SORTED] >>
     `!l s cs fs pi pi'.
     State_st_list_well_formed_ok (State_st_list l s cs fs) ==>
     SORTED bound_name_instr_le l ==>
     Completed_list_up_to sem_expr (State_st_list l s cs fs) (SUC pos) ==>
     step_execution in_order_step_list pi ==>
     SND (SND (LAST pi)) = State_st_list l s cs fs ==>
     IO_bounded_execution_acc translate_val_list sem_expr (State_st_list l s cs fs) (SUC pos) n pi = SOME pi' ==>
     ?pi''. pi' = pi ++ pi'' /\
      step_execution in_order_step_list pi' /\
      Completed_list_up_to sem_expr (SND (SND (LAST pi'))) (SUC pos + n) /\
      LENGTH pi'' <= 2 * n` by rw [IO_bounded_execution_acc_IO_execution_sound] >>
     METIS_TAC []) >>

   `?pi'. pi = [(State_st_list l s cs fs,ll,State_st_list l (s |+ (t,v')) cs fs);
     (State_st_list l (s |+ (t,v')) cs fs,ll',State_st_list (l ++ translate_val_list v' (max_bound_name_list l))
       (s |+ (t,v')) cs (t::fs))] ++ pi' /\
     step_execution in_order_step_list pi /\
     Completed_list_up_to sem_expr (SND (SND (LAST pi))) (SUC pos + n) /\
     LENGTH pi' <= 2 * n`
    by METIS_TAC [IO_bounded_execution_acc_IO_execution_sound,translate_val_list_SORTED] >>

   `FST (HD ([(State_st_list l s cs fs,ll,State_st_list l (s |+ (t,v')) cs fs);
     (State_st_list l (s |+ (t,v')) cs fs,ll',
      State_st_list (l ++ translate_val_list v' (max_bound_name_list l)) (s |+ (t,v')) cs (t::fs))] ++ pi')) =
    State_st_list l s cs fs` by fs [] >>
   `LENGTH pi <= 2 * SUC n` by rw [] >>
   `SUC pos + n = pos + SUC n` by rw [] >>
   METIS_TAC [step_execution_list_IO_HD],

   rename1 `o_store res_REG ta tv` >>
   Cases_on `sem_instr_exe sem_expr (i_assign t c (o_store res_REG ta tv)) (State_st_list l s cs fs)` >> fs [] >>
   Cases_on `x` >> rename1 `(v',obs)` >> fs [] >>
   Cases_on `OoO_Exe_list_instr_not_stored_guard_true_sem_instr (State_st_list l s cs fs)
    (i_assign t c (o_store res_REG ta tv)) v' obs` >>
   fs [] >> rename1 `(ll,stl)` >>

   `State_st_list_ok (State_st_list l s cs fs)` by fs [State_st_list_ok,State_st_list_well_formed_ok] >>
   `out_of_order_step_list (State_st_list l s cs fs) ll stl`
    by METIS_TAC [OoO_Exe_list_instr_not_stored_guard_true_sem_instr_SOME_out_of_order_step_list] >>
   `State_st_list_ok stl` by METIS_TAC [step_invariant,step_invariant_out_of_order_step_list_ok] >>
   `State_st_list_well_formed_ok stl`
    by METIS_TAC [step_invariant,step_invariant_out_of_order_step_list_well_formed_ok] >>

   sg `in_order_step_list (State_st_list l s cs fs) ll stl` >-
    (`ll = ll_lb obs act_exe_list t /\ stl = State_st_list l (s |+ (t,v')) cs fs`
      by METIS_TAC [OoO_Exe_list_instr_not_stored_guard_true_sem_instr_result_form] >>     
     rw [in_order_step_list,IO_step_list] >>
     fs [out_of_order_step_list] >>
     rw [EVERY_MEM] >>
     fs [MEM_FILTER] >>
     `bound_name_instr i < t` by DECIDE_TAC >>
     `MEM i l` by fs [state_list_to_state,instr_in_State] >>

     `Completed_list sem_expr (State_st_list l s cs fs) i`
      suffices_by rw [Completed_list_correct] >>
     `MEM i (TAKE pos l)` suffices_by fs [Completed_list_up_to] >>
     `MEM i (TAKE pos l) \/ MEM i (DROP pos l)`
      by METIS_TAC [TAKE_DROP,MEM_APPEND] >>
     `i <> i_assign t c (o_store res_REG ta tv)` by (Cases_on `i` >> fs [bound_name_instr]) >>
     `MEM i (i_assign t c (o_store res_REG ta tv)::il)` by METIS_TAC [] >>
     fs [] >> rw [] >>
     sg `SORTED bound_name_instr_le ((TAKE pos l ++ [i_assign t c (o_store res_REG ta tv)]) ++ il)` >-
      (`(TAKE pos l ++ [i_assign t c (o_store res_REG ta tv)]) ++ il = l` suffices_by rw [] >>
       `l = TAKE pos l ++ (i_assign t c (o_store res_REG ta tv)::il)` by METIS_TAC [TAKE_DROP] >>
       once_rewrite_tac [GSYM APPEND_ASSOC] >>
       `[i_assign t c (o_store res_REG ta tv)] ++ il = i_assign t c (o_store res_REG ta tv)::il` by rw [] >>
       METIS_TAC []) >>
     `!x y. MEM x (TAKE pos l ++ [i_assign t c (o_store res_REG ta tv)]) ==> MEM y il ==> bound_name_instr_le x y`
      by METIS_TAC [SORTED_APPEND,transitive_bound_name_instr_le] >>
     `MEM (i_assign t c (o_store res_REG ta tv)) (TAKE pos l ++ [i_assign t c (o_store res_REG ta tv)])` by rw [] >>
     `bound_name_instr_le (i_assign t c (o_store res_REG ta tv)) i` by METIS_TAC [] >>
     fs [bound_name_instr_le,name_le,bound_name_instr]) >>

   `step_execution in_order_step_list [(State_st_list l s cs fs,ll,stl)]`
    by (fs [step_list_to_step] >> METIS_TAC [step_execution_rules]) >>
   `SND (SND (LAST [(State_st_list l s cs fs,ll,stl)])) = stl` by fs [] >>
   sg `Completed_list sem_expr stl (i_assign t c (o_store res_REG ta tv))` >-
    (fs [OoO_Exe_list_instr_not_stored_guard_true_sem_instr] >>
     rw [Completed_list,FLOOKUP_DEF]) >>

   sg `Completed_list_up_to sem_expr stl (SUC pos)` >-
    (`stl = State_st_list l (s |+ (t,v')) cs fs`
      by METIS_TAC [OoO_Exe_list_instr_not_stored_guard_true_sem_instr_result_form] >>
     rw [Completed_list_up_to] >>
     `MEM i l` by METIS_TAC [MEM_TAKE] >>
     `TAKE (SUC pos) l = SNOC (i_assign t c (o_store res_REG ta tv)) (TAKE pos l)`
      by rw [DROP_TAKE_SNOC] >>
     fs [] >>
     `Completed_list sem_expr (State_st_list l s cs fs) i`
      by fs [Completed_list_up_to] >>
     `Completed (state_list_to_state (State_st_list l s cs fs)) i`
      by METIS_TAC [Completed_list_correct] >>
     `Completed (state_list_to_state (State_st_list l (s |+ (t,v')) cs fs)) i`
      suffices_by METIS_TAC [Completed_list_correct] >>
     `Completed_t (state_list_to_state (State_st_list l s cs fs)) (bound_name_instr i)`
      by (fs [state_list_to_state] >> rw [Completed_t] >> METIS_TAC []) >>

     `Completed_t (state_list_to_state (State_st_list l (s |+ (t,v')) cs fs)) (bound_name_instr i)`
       by METIS_TAC [state_list_to_state,
        out_of_order_step_list_sound,
        well_formed_state_OoO_completed_t_preserved,
        State_st_list_well_formed_ok] >>

     fs [state_list_to_state,Completed_t,State_st_list_well_formed_ok] >>
     METIS_TAC [wfs_unique_instr_names]) >>

   `stl = State_st_list l (s |+ (t,v')) cs fs`
    by METIS_TAC [OoO_Exe_list_instr_not_stored_guard_true_sem_instr_result_form] >>
   rw [] >>
   `?pi'. pi = [(State_st_list l s cs fs,ll,State_st_list l (s |+ (t,v')) cs fs)] ++ pi' /\
     step_execution in_order_step_list pi /\
     Completed_list_up_to sem_expr (SND (SND (LAST pi))) (SUC pos + n) /\
     LENGTH pi' <= 2 * n`
    by METIS_TAC [IO_bounded_execution_acc_IO_execution_sound,translate_val_list_SORTED] >>
   `FST (HD ([(State_st_list l s cs fs,ll,State_st_list l (s |+ (t,v')) cs fs)] ++ pi')) =
    State_st_list l s cs fs` by fs [] >>
   `LENGTH pi <= 2 * SUC n` by rw [] >>
   `SUC pos + n = pos + SUC n` by rw [] >>
   METIS_TAC [step_execution_list_IO_HD],

   rename1 `o_store res_MEM ta tv` >>
   Cases_on `sem_instr_exe sem_expr (i_assign t c (o_store res_MEM ta tv)) (State_st_list l s cs fs)` >> fs [] >>
   Cases_on `x` >> fs [] >> rename1 `(v',obs)` >>
   Cases_on `OoO_Exe_list_instr_not_stored_guard_true_sem_instr (State_st_list l s cs fs) (i_assign t c (o_store res_MEM ta tv)) v' obs` >> fs [] >>
   rename1 `(ll,stl)` >>
   Cases_on `OoO_Cmt_list_stored sem_expr stl t ta tv` >> fs [] >>
   Cases_on `x` >> fs [] >> rename1 `(ll',stl')` >>

   `State_st_list_ok (State_st_list l s cs fs)` by fs [State_st_list_ok,State_st_list_well_formed_ok] >>   
   `out_of_order_step_list (State_st_list l s cs fs) ll stl`
    by METIS_TAC [OoO_Exe_list_instr_not_stored_guard_true_sem_instr_SOME_out_of_order_step_list] >>
   `State_st_list_ok stl` by METIS_TAC [step_invariant,step_invariant_out_of_order_step_list_ok] >>
   `State_st_list_well_formed_ok stl`
    by METIS_TAC [step_invariant,step_invariant_out_of_order_step_list_well_formed_ok] >>

   `stl = State_st_list l (s |+ (t,v')) cs fs`
    by METIS_TAC [OoO_Exe_list_instr_not_stored_guard_true_sem_instr_result_form] >>
   rw [] >>
   `FLOOKUP (s |+ (t,v')) t = SOME v'` by fs [FLOOKUP_UPDATE] >>
   `FLOOKUP (s |+ (t,v')) t <> NONE` by fs [] >>

   `out_of_order_step_list (State_st_list l (s |+ (t,v')) cs fs) ll' stl'`
    by METIS_TAC [OoO_Cmt_list_stored_SOME_out_of_order_step_list] >>
   `State_st_list_ok stl'` by METIS_TAC [step_invariant,step_invariant_out_of_order_step_list_ok] >>
   `State_st_list_well_formed_ok stl'`
    by METIS_TAC [step_invariant,step_invariant_out_of_order_step_list_well_formed_ok] >>

   Q.ABBREV_TAC `pi0 = [(State_st_list l s cs fs,ll,State_st_list l (s |+ (t,v')) cs fs);
    (State_st_list l (s |+ (t,v')) cs fs,ll',stl')]` >>
   `SND (SND (LAST pi0)) = stl'` by fs [Abbr `pi0`] >>

   sg `in_order_step_list (State_st_list l s cs fs) ll (State_st_list l (s |+ (t,v')) cs fs)` >-
    (`ll = ll_lb obs act_exe_list t`
      by METIS_TAC [OoO_Exe_list_instr_not_stored_guard_true_sem_instr_result_form] >>
     rw [in_order_step_list,IO_step_list] >>
     fs [out_of_order_step_list] >>
     rw [EVERY_MEM] >>
     fs [MEM_FILTER] >>
     `bound_name_instr i < t` by DECIDE_TAC >>
     `MEM i l` by fs [state_list_to_state,instr_in_State] >>
     `Completed_list sem_expr (State_st_list l s cs fs) i`
      suffices_by rw [Completed_list_correct] >>
     `MEM i (TAKE pos l)` suffices_by fs [Completed_list_up_to] >>
     `MEM i (TAKE pos l) \/ MEM i (DROP pos l)`
      by METIS_TAC [TAKE_DROP,MEM_APPEND] >>
     `i <> i_assign t c (o_store res_MEM ta tv)` by (Cases_on `i` >> fs [bound_name_instr]) >>
     `MEM i (i_assign t c (o_store res_MEM ta tv)::il)` by METIS_TAC [] >>
     fs [] >> rw [] >>
     sg `SORTED bound_name_instr_le ((TAKE pos l ++ [i_assign t c (o_store res_MEM ta tv)]) ++ il)` >-
      (`(TAKE pos l ++ [i_assign t c (o_store res_MEM ta tv)]) ++ il = l` suffices_by rw [] >>
       `l = TAKE pos l ++ (i_assign t c (o_store res_MEM ta tv)::il)` by METIS_TAC [TAKE_DROP] >>
       once_rewrite_tac [GSYM APPEND_ASSOC] >>
       `[i_assign t c (o_store res_MEM ta tv)] ++ il = i_assign t c (o_store res_MEM ta tv)::il` by rw [] >>
       METIS_TAC []) >>
     `!x y. MEM x (TAKE pos l ++ [i_assign t c (o_store res_MEM ta tv)]) ==> MEM y il ==> bound_name_instr_le x y`
      by METIS_TAC [SORTED_APPEND,transitive_bound_name_instr_le] >>
     `MEM (i_assign t c (o_store res_MEM ta tv)) (TAKE pos l ++ [i_assign t c (o_store res_MEM ta tv)])` by rw [] >>
     `bound_name_instr_le (i_assign t c (o_store res_MEM ta tv)) i` by METIS_TAC [] >>
     fs [bound_name_instr_le,name_le,bound_name_instr]) >>

   sg `Completed_list_up_to sem_expr (State_st_list l (s |+ (t,v')) cs fs) pos` >-
    (rw [Completed_list_up_to] >>
     `MEM i l` by METIS_TAC [MEM_TAKE] >>
     `Completed_list sem_expr (State_st_list l s cs fs) i`
      by fs [Completed_list_up_to] >>
     `Completed (state_list_to_state (State_st_list l s cs fs)) i`
      by METIS_TAC [Completed_list_correct] >>
     `Completed (state_list_to_state (State_st_list l (s |+ (t,v')) cs fs)) i`
      suffices_by METIS_TAC [Completed_list_correct] >>
     `Completed_t (state_list_to_state (State_st_list l s cs fs)) (bound_name_instr i)`
      by (fs [state_list_to_state] >> rw [Completed_t] >> METIS_TAC []) >>

     `Completed_t (state_list_to_state (State_st_list l (s |+ (t,v')) cs fs)) (bound_name_instr i)`
       by METIS_TAC [state_list_to_state,
        out_of_order_step_list_sound,
        well_formed_state_OoO_completed_t_preserved,
        State_st_list_well_formed_ok] >>

     fs [state_list_to_state,Completed_t,State_st_list_well_formed_ok] >>
     METIS_TAC [wfs_unique_instr_names]) >>

   sg `in_order_step_list (State_st_list l (s |+ (t,v')) cs fs) ll' stl'` >-
    (`?a v. ll' = ll_lb (obs_ds a) (act_cmt_list a v) t /\
       stl' = State_st_list l (s |+ (t,v')) (t::cs) fs`
      by METIS_TAC [OoO_Cmt_list_stored_result_form] >>
     rw [in_order_step_list,IO_step_list] >>
     fs [out_of_order_step_list] >>
     rw [EVERY_MEM] >>
     fs [MEM_FILTER] >>
     `bound_name_instr i < t` by DECIDE_TAC >>
     `MEM i l` by fs [state_list_to_state,instr_in_State] >>

     `Completed_list sem_expr (State_st_list l (s |+ (t,v')) cs fs) i`
      suffices_by rw [Completed_list_correct] >>
     `MEM i (TAKE pos l)` suffices_by fs [Completed_list_up_to] >>
     `MEM i (TAKE pos l) \/ MEM i (DROP pos l)`
      by METIS_TAC [TAKE_DROP,MEM_APPEND] >>
     `i <> i_assign t c (o_store res_MEM ta tv)` by (Cases_on `i` >> fs [bound_name_instr]) >>
     `MEM i (i_assign t c (o_store res_MEM ta tv)::il)` by METIS_TAC [] >>
     fs [] >> rw [] >>
     sg `SORTED bound_name_instr_le ((TAKE pos l ++ [i_assign t c (o_store res_MEM ta tv)]) ++ il)` >-
      (`(TAKE pos l ++ [i_assign t c (o_store res_MEM ta tv)]) ++ il = l` suffices_by rw [] >>
       `l = TAKE pos l ++ (i_assign t c (o_store res_MEM ta tv))::il` by METIS_TAC [TAKE_DROP] >>
       once_rewrite_tac [GSYM APPEND_ASSOC] >>
       `[i_assign t c (o_store res_MEM ta tv)] ++ il = i_assign t c (o_store res_MEM ta tv)::il` by rw [] >>
       METIS_TAC []) >>
     `!x y. MEM x (TAKE pos l ++ [i_assign t c (o_store res_MEM ta tv)]) ==> MEM y il ==> bound_name_instr_le x y`
      by METIS_TAC [SORTED_APPEND,transitive_bound_name_instr_le] >>
     `MEM (i_assign t c (o_store res_MEM ta tv)) (TAKE pos l ++ [i_assign t c (o_store res_MEM ta tv)])` by rw [] >>
     `bound_name_instr_le (i_assign t c (o_store res_MEM ta tv)) i` by METIS_TAC [] >>
     fs [bound_name_instr_le,name_le,bound_name_instr]) >>

   sg `step_execution in_order_step_list pi0` >-
    (rw [Abbr `pi0`,step_list_to_step] >>
     `step_execution in_order_step_list ([] ++
       [(State_st_list l s cs fs,ll,State_st_list l (s |+ (t,v')) cs fs);
        (State_st_list l (s |+ (t,v')) cs fs,ll',stl')])`
      suffices_by fs [] >>
     `step_execution in_order_step_list ([] ++
       [(State_st_list l s cs fs,ll,State_st_list l (s |+ (t,v')) cs fs)])`
      suffices_by METIS_TAC [step_execution_rules] >>
     fs [] >> METIS_TAC [step_execution_rules]) >>

   `Completed_list sem_expr (State_st_list l (s |+ (t,v')) (t::cs) fs)
     (i_assign t c (o_store res_MEM ta tv))` by rw [Completed_list] >>

   sg `Completed_list_up_to sem_expr stl' (SUC pos)` >-
    (`stl' = State_st_list l (s |+ (t,v')) (t::cs) fs`
      by METIS_TAC [OoO_Cmt_list_stored_result_form] >>
     rw [Completed_list_up_to] >>
     `TAKE (SUC pos) l = SNOC (i_assign t c (o_store res_MEM ta tv)) (TAKE pos l)`
      by rw [DROP_TAKE_SNOC] >>
     fs [Completed_list_up_to] >>
     `Completed_list sem_expr (State_st_list l (s |+ (t,v')) cs fs) i` by METIS_TAC [] >>
     `Completed (state_list_to_state (State_st_list l (s |+ (t,v')) cs fs)) i`
      by METIS_TAC [Completed_list_correct] >>
     `Completed (state_list_to_state (State_st_list l (s |+ (t,v')) (t::cs) fs)) i`
      suffices_by METIS_TAC [Completed_list_correct] >>
     `MEM i l` by METIS_TAC [MEM_TAKE] >>
     `Completed_t (state_list_to_state (State_st_list l (s |+ (t,v')) cs fs)) (bound_name_instr i)`
      by (fs [state_list_to_state] >> rw [Completed_t] >> METIS_TAC []) >>

     `Completed_t (state_list_to_state (State_st_list l (s |+ (t,v')) (t::cs) fs)) (bound_name_instr i)`
      by METIS_TAC [state_list_to_state,
        out_of_order_step_list_sound,
        well_formed_state_OoO_completed_t_preserved,
        State_st_list_well_formed_ok] >>

     fs [state_list_to_state,Completed_t,State_st_list_well_formed_ok,Abbr `pi0`] >>
     METIS_TAC [wfs_unique_instr_names]) >>

   `stl' = State_st_list l (s |+ (t,v')) (t::cs) fs`
    by METIS_TAC [OoO_Cmt_list_stored_result_form] >>
   rw [Abbr `pi0`] >>

   sg `?pi'. pi = [(State_st_list l s cs fs,ll,State_st_list l (s |+ (t,v')) cs fs);
      (State_st_list l (s |+ (t,v')) cs fs,ll',State_st_list l (s |+ (t,v')) (t::cs) fs)] ++ pi' /\
     step_execution in_order_step_list pi /\
     Completed_list_up_to sem_expr (SND (SND (LAST pi))) (SUC pos + n) /\
     LENGTH pi' <= 2 * n` >-
    (`translate_val_list_SORTED` by rw [translate_val_list_SORTED] >>
     `!l s cs fs pi pi'.
     State_st_list_well_formed_ok (State_st_list l s cs fs) ==>
     SORTED bound_name_instr_le l ==>
     Completed_list_up_to sem_expr (State_st_list l s cs fs) (SUC pos) ==>
     step_execution in_order_step_list pi ==>
     SND (SND (LAST pi)) = State_st_list l s cs fs ==>
     IO_bounded_execution_acc translate_val_list sem_expr (State_st_list l s cs fs) (SUC pos) n pi = SOME pi' ==>
     ?pi''. pi' = pi ++ pi'' /\
      step_execution in_order_step_list pi' /\
      Completed_list_up_to sem_expr (SND (SND (LAST pi'))) (SUC pos + n) /\
      LENGTH pi'' <= 2 * n` by rw [IO_bounded_execution_acc_IO_execution_sound] >>
     METIS_TAC []) >>

   `FST (HD ([(State_st_list l s cs fs,ll,State_st_list l (s |+ (t,v')) cs fs);
     (State_st_list l (s |+ (t,v')) cs fs,ll',State_st_list l (s |+ (t,v')) (t::cs) fs)] ++ pi')) =
    State_st_list l s cs fs` by fs [] >>
   `LENGTH pi <= 2 * SUC n` by rw [] >>
   `SUC pos + n = pos + SUC n` by rw [] >>
   METIS_TAC [step_execution_list_IO_HD]
  ],

  rename1 `o_store r ta tv` >>
  rename1 `FLOOKUP s t = SOME v` >>
  Cases_on `r` >> fs [Completed_list] >-
   (Cases_on `MEM t fs` >> fs [] >>
    Cases_on `OoO_Ftc_list_stored_incomplete translate_val_list sem_expr (State_st_list l s cs fs) t v` >> fs [] >>
    Cases_on `x` >> fs [] >>
    rename1 `(ll,stl)` >>

    `State_st_list_ok (State_st_list l s cs fs)` by fs [State_st_list_ok,State_st_list_well_formed_ok] >>
    `out_of_order_step_list (State_st_list l s cs fs) ll stl`
     by METIS_TAC [OoO_Ftc_list_stored_incomplete_SOME_out_of_order_step_list] >>
    `State_st_list_ok stl` by METIS_TAC [step_invariant,step_invariant_out_of_order_step_list_ok] >>
    `State_st_list_well_formed_ok stl`
     by METIS_TAC [step_invariant,step_invariant_out_of_order_step_list_well_formed_ok] >>

    sg `in_order_step_list (State_st_list l s cs fs) ll stl` >-
     (`ll = ll_lb (obs_il v) (act_ftc_list (translate_val_list v (max_bound_name_list l))) t /\
       stl = State_st_list (l ++ translate_val_list v (max_bound_name_list l)) s cs (t::fs)`
       by METIS_TAC [OoO_Ftc_list_stored_incomplete_result_form] >>
      rw [in_order_step_list,IO_step_list] >>
      fs [out_of_order_step_list] >>
      rw [EVERY_MEM] >>
      fs [MEM_FILTER] >>
      `bound_name_instr i < t` by DECIDE_TAC >>
      `MEM i l` by fs [state_list_to_state,instr_in_State] >>
      `Completed_list sem_expr (State_st_list l s cs fs) i`
       suffices_by rw [Completed_list_correct] >>
      `MEM i (TAKE pos l)` suffices_by fs [Completed_list_up_to] >>
      `MEM i (TAKE pos l) \/ MEM i (DROP pos l)`
       by METIS_TAC [TAKE_DROP,MEM_APPEND] >>
      `i <> i_assign t c (o_store res_PC ta tv)` by (Cases_on `i` >> fs [bound_name_instr]) >>
      `MEM i (i_assign t c (o_store res_PC ta tv)::il)` by METIS_TAC [] >>
      fs [] >> rw [] >>
      sg `SORTED bound_name_instr_le ((TAKE pos l ++ [i_assign t c (o_store res_PC ta tv)]) ++ il)` >-
       (`(TAKE pos l ++ [i_assign t c (o_store res_PC ta tv)]) ++ il = l` suffices_by rw [] >>
        `l = TAKE pos l ++ (i_assign t c (o_store res_PC ta tv)::il)` by METIS_TAC [TAKE_DROP] >>
        once_rewrite_tac [GSYM APPEND_ASSOC] >>
        `[i_assign t c (o_store res_PC ta tv)] ++ il = i_assign t c (o_store res_PC ta tv)::il` by rw [] >>
        METIS_TAC []) >>
      `!x y. MEM x (TAKE pos l ++ [i_assign t c (o_store res_PC ta tv)]) ==> MEM y il ==> bound_name_instr_le x y`
       by METIS_TAC [SORTED_APPEND,transitive_bound_name_instr_le] >>
      `MEM (i_assign t c (o_store res_PC ta tv)) (TAKE pos l ++ [i_assign t c (o_store res_PC ta tv)])` by rw [] >>
      `bound_name_instr_le (i_assign t c (o_store res_PC ta tv)) i` by METIS_TAC [] >>
      fs [bound_name_instr_le,name_le,bound_name_instr]) >>

    `step_execution in_order_step_list [(State_st_list l s cs fs,ll,stl)]`
     by (fs [step_list_to_step] >> METIS_TAC [step_execution_rules]) >>
    `SND (SND (LAST [(State_st_list l s cs fs,ll,stl)])) = stl` by fs [] >>
    sg `Completed_list sem_expr stl (i_assign t c (o_store res_PC ta tv))` >-
     (`stl = State_st_list (l ++ translate_val_list v (max_bound_name_list l)) s cs (t::fs)`
       by METIS_TAC [OoO_Ftc_list_stored_incomplete_result_form] >>
      rw [Completed_list]) >>

    sg `Completed_list_up_to sem_expr stl (SUC pos)` >-
     (`stl = State_st_list (l ++ translate_val_list v (max_bound_name_list l)) s cs (t::fs)`
       by METIS_TAC [OoO_Ftc_list_stored_incomplete_result_form] >>
      rw [Completed_list_up_to] >>
      `DROP pos (l ++ translate_val_list v (max_bound_name_list l)) =
        i_assign t c (o_store res_PC ta tv)::il ++ translate_val_list v (max_bound_name_list l)`
       by rw [DROP_CONS_APPEND] >>
      `TAKE (SUC pos) (l ++ translate_val_list v (max_bound_name_list l)) =
        SNOC (i_assign t c (o_store res_PC ta tv)) (TAKE pos (l ++ translate_val_list v (max_bound_name_list l)))`
       by rw [DROP_TAKE_SNOC] >>
      fs [] >>
      `MEM i (TAKE pos l)` by METIS_TAC [DROP_CONS_TAKE_APPEND] >>
      `Completed_list sem_expr (State_st_list l s cs fs) i`
       by fs [Completed_list_up_to] >>
      `Completed (state_list_to_state (State_st_list l s cs fs)) i`
       by fs [Completed_list_correct] >>
      `MEM i l` by METIS_TAC [MEM_TAKE] >>
      `Completed_t (state_list_to_state (State_st_list l s cs fs)) (bound_name_instr i)`
       by (fs [state_list_to_state] >> rw [Completed_t] >> METIS_TAC []) >>
      `Completed_t (state_list_to_state (State_st_list (l ++ translate_val_list v (max_bound_name_list l))
       s cs (t::fs))) (bound_name_instr i)`
       by METIS_TAC [state_list_to_state,
        out_of_order_step_list_sound,
        well_formed_state_OoO_completed_t_preserved,
        State_st_list_well_formed_ok] >>
      `Completed (state_list_to_state (State_st_list (l ++ translate_val_list v (max_bound_name_list l))
       s cs (t::fs))) i` suffices_by METIS_TAC [Completed_list_correct] >>
      sg `!i'. MEM i' (translate_val_list v (max_bound_name_list l)) ==> bound_name_instr i < bound_name_instr i'` >-
       (`FINITE (set l)` by rw [] >>
        rw [] >>
        `i' IN (translate_val v (MAX_SET (bound_names_program (set l))))`
         by METIS_TAC [translate_val_list_correct,max_bound_name_list_correct] >>
        METIS_TAC [translate_val_max_name_lt]) >>
      fs [state_list_to_state,Completed_t,State_st_list_well_formed_ok] >-
      METIS_TAC [wfs_unique_instr_names] >>
      `bound_name_instr i < bound_name_instr i` suffices_by DECIDE_TAC >>
      METIS_TAC []) >>
    sg `SORTED bound_name_instr_le (l ++ translate_val_list v (max_bound_name_list l))` >-
     (`!x y. MEM x l ==> MEM y (translate_val_list v (max_bound_name_list l)) ==> bound_name_instr_le x y`
       suffices_by METIS_TAC [SORTED_APPEND,transitive_bound_name_instr_le] >>
      rw [bound_name_instr_le,name_le] >>
      `bound_name_instr x < bound_name_instr y` suffices_by rw [] >>
      `y IN (translate_val v (MAX_SET (bound_names_program (set l))))`
       by METIS_TAC [translate_val_list_correct,max_bound_name_list_correct] >>
      `FINITE (set l)` by rw [] >>
      METIS_TAC [translate_val_max_name_lt]) >>
    `stl = State_st_list (l ++ translate_val_list v (max_bound_name_list l)) s cs (t::fs)`
     by METIS_TAC [OoO_Ftc_list_stored_incomplete_result_form] >>
    rw [] >>
    `?pi'. pi = [(State_st_list l s cs fs,ll,
       State_st_list (l ++ translate_val_list v (max_bound_name_list l)) s cs (t::fs))] ++ pi' /\
       step_execution in_order_step_list pi /\
       Completed_list_up_to sem_expr (SND (SND (LAST pi))) (SUC pos + n) /\
       LENGTH pi' <= 2 * n`
     by METIS_TAC [IO_bounded_execution_acc_IO_execution_sound,translate_val_list_SORTED] >>
    `FST (HD ([(State_st_list l s cs fs,ll,
      State_st_list (l ++ translate_val_list v (max_bound_name_list l)) s cs (t::fs))] ++ pi')) =
     State_st_list l s cs fs` by fs [] >>
    `LENGTH pi <= 2 * SUC n` by rw [] >>
    `SUC pos + n = pos + SUC n` by rw [] >>
    METIS_TAC [step_execution_list_IO_HD]) >>
  Cases_on `MEM t cs` >> fs [] >>
  Cases_on `OoO_Cmt_list_stored_incomplete sem_expr (State_st_list l s cs fs) t ta tv` >> fs [] >>
  Cases_on `x` >> fs [] >>
  rename1 `(ll,stl)` >>
  `FLOOKUP s t <> NONE` by fs [] >>

  `State_st_list_ok (State_st_list l s cs fs)` by fs [State_st_list_ok,State_st_list_well_formed_ok] >>   
  `out_of_order_step_list (State_st_list l s cs fs) ll stl`
   by METIS_TAC [OoO_Cmt_list_stored_incomplete_SOME_out_of_order_step_list] >>
  `State_st_list_ok stl` by METIS_TAC [step_invariant,step_invariant_out_of_order_step_list_ok] >>
  `State_st_list_well_formed_ok stl`
   by METIS_TAC [step_invariant,step_invariant_out_of_order_step_list_well_formed_ok] >>

  sg `in_order_step_list (State_st_list l s cs fs) ll stl` >-
   (`?a v. ll = ll_lb (obs_ds a) (act_cmt_list a v) t /\ stl = State_st_list l s (t::cs) fs`
     by METIS_TAC [OoO_Cmt_list_stored_incomplete_result_form] >>
    rw [in_order_step_list,IO_step_list] >>
    fs [out_of_order_step_list] >>
    rw [EVERY_MEM] >>
    fs [MEM_FILTER] >>
    `bound_name_instr i < t` by DECIDE_TAC >>
    `MEM i l` by fs [state_list_to_state,instr_in_State] >>
    `Completed_list sem_expr (State_st_list l s cs fs) i`
     suffices_by rw [Completed_list_correct] >>
    `MEM i (TAKE pos l)` suffices_by fs [Completed_list_up_to] >>
    `MEM i (TAKE pos l) \/ MEM i (DROP pos l)`
     by METIS_TAC [TAKE_DROP,MEM_APPEND] >>
    `i <> i_assign t c (o_store res_MEM ta tv)` by (Cases_on `i` >> fs [bound_name_instr]) >>
    `MEM i (i_assign t c (o_store res_MEM ta tv)::il)` by METIS_TAC [] >>
    fs [] >> rw [] >>
    sg `SORTED bound_name_instr_le ((TAKE pos l ++ [i_assign t c (o_store res_MEM ta tv)]) ++ il)` >-
     (`(TAKE pos l ++ [i_assign t c (o_store res_MEM ta tv)]) ++ il = l` suffices_by rw [] >>
      `l = TAKE pos l ++ (i_assign t c (o_store res_MEM ta tv))::il` by METIS_TAC [TAKE_DROP] >>
      once_rewrite_tac [GSYM APPEND_ASSOC] >>
      `[i_assign t c (o_store res_MEM ta tv)] ++ il = i_assign t c (o_store res_MEM ta tv)::il` by rw [] >>
      METIS_TAC []) >>
    `!x y. MEM x (TAKE pos l ++ [i_assign t c (o_store res_MEM ta tv)]) ==> MEM y il ==> bound_name_instr_le x y`
     by METIS_TAC [SORTED_APPEND,transitive_bound_name_instr_le] >>
    `MEM (i_assign t c (o_store res_MEM ta tv)) (TAKE pos l ++ [i_assign t c (o_store res_MEM ta tv)])` by rw [] >>
    `bound_name_instr_le (i_assign t c (o_store res_MEM ta tv)) i` by METIS_TAC [] >>
    fs [bound_name_instr_le,name_le,bound_name_instr]) >>
  `step_execution in_order_step_list [(State_st_list l s cs fs,ll,stl)]`
   by (fs [step_list_to_step] >> METIS_TAC [step_execution_rules]) >>
  `SND (SND (LAST [(State_st_list l s cs fs,ll,stl)])) = stl` by fs [] >>
  sg `Completed_list sem_expr stl (i_assign t c (o_store res_MEM ta tv))` >-
   (`stl = State_st_list l s (t::cs) fs`
     by METIS_TAC [OoO_Cmt_list_stored_incomplete_result_form] >>
    rw [Completed_list]) >>

  sg `Completed_list_up_to sem_expr stl (SUC pos)` >-
   (`stl = State_st_list l s (t::cs) fs`
     by METIS_TAC [OoO_Cmt_list_stored_incomplete_result_form] >>
    rw [Completed_list_up_to] >>
    `TAKE (SUC pos) l = SNOC (i_assign t c (o_store res_MEM ta tv)) (TAKE pos l)`
     by rw [DROP_TAKE_SNOC] >>
    fs [Completed_list_up_to] >>
    `Completed_list sem_expr (State_st_list l s cs fs) i` by METIS_TAC [] >>
    `Completed (state_list_to_state (State_st_list l s cs fs)) i`
     by METIS_TAC [Completed_list_correct] >>
    `Completed (state_list_to_state (State_st_list l s (t::cs) fs)) i`
     suffices_by METIS_TAC [Completed_list_correct] >>
    `MEM i l` by METIS_TAC [MEM_TAKE] >>
    `Completed_t (state_list_to_state (State_st_list l s cs fs)) (bound_name_instr i)`
     by (fs [state_list_to_state] >> rw [Completed_t] >> METIS_TAC []) >>
    `Completed_t (state_list_to_state (State_st_list l s (t::cs) fs)) (bound_name_instr i)`
      by METIS_TAC [state_list_to_state,
        out_of_order_step_list_sound,
        well_formed_state_OoO_completed_t_preserved,
        State_st_list_well_formed_ok] >>
    fs [state_list_to_state,Completed_t,State_st_list_well_formed_ok] >>
    METIS_TAC [wfs_unique_instr_names]) >>

  `stl = State_st_list l s (t::cs) fs`
   by METIS_TAC [OoO_Cmt_list_stored_incomplete_result_form] >>
  rw [] >>
  `?pi'. pi = [(State_st_list l s cs fs,ll,State_st_list l s (t::cs) fs)] ++ pi' /\
    step_execution in_order_step_list pi /\
    Completed_list_up_to sem_expr (SND (SND (LAST pi))) (SUC pos + n) /\
    LENGTH pi' <= 2 * n`
   by METIS_TAC [IO_bounded_execution_acc_IO_execution_sound,translate_val_list_SORTED] >>
  `FST (HD ([(State_st_list l s cs fs,ll,State_st_list l s (t::cs) fs)] ++ pi')) =
    State_st_list l s cs fs` by fs [] >>
  `LENGTH pi <= 2 * SUC n` by rw [] >>
  `SUC pos + n = pos + SUC n` by rw [] >>
  METIS_TAC [step_execution_list_IO_HD]
 ]
QED

(* TODO: it also suffices that some instruction in the range is incomplete. *)
(* FIXME: switch to NTH as version below? *)
Theorem IO_bounded_execution_in_order_step_list_sound:
 translate_val_list_SORTED ==>
 !l s cs fs pos n i il pi.
  State_st_list_well_formed_ok (State_st_list l s cs fs) ==>
  SORTED bound_name_instr_le l ==>
  Completed_list_up_to sem_expr (State_st_list l s cs fs) (PRE pos) ==>
  DROP (PRE pos) l = i::il ==>
  ~(Completed_list sem_expr (State_st_list l s cs fs) i) ==>
  IO_bounded_execution translate_val_list sem_expr (State_st_list l s cs fs) pos (SUC n) = SOME pi ==>
  FST (HD pi) = State_st_list l s cs fs /\
  step_execution in_order_step_list pi /\
  Completed_list_up_to sem_expr (SND (SND (LAST pi))) (PRE pos + SUC n) /\
  LENGTH pi <= 2 * n + 2
Proof
 rw [IO_bounded_execution] >>
 `2 * SUC n = 2 * n + 2` by DECIDE_TAC >> 
 METIS_TAC [IO_bounded_execution_acc_IO_empty_sound,step_execution_list_IO_HD]
QED

Theorem IO_bounded_execution_in_order_step_list_sound_NTH:
 translate_val_list_SORTED ==>
 !stl pos n i pi.
  State_st_list_well_formed_ok stl ==>
  SORTED bound_name_instr_le (state_program_list stl) ==>
  Completed_list_up_to sem_expr stl (PRE pos) ==>
  NTH (PRE pos) (state_program_list stl) = SOME i ==>
  ~(Completed_list sem_expr stl i) ==>
  IO_bounded_execution translate_val_list sem_expr stl pos (SUC n) = SOME pi ==>
  FST (HD pi) = stl /\
  step_execution in_order_step_list pi /\
  Completed_list_up_to sem_expr (SND (SND (LAST pi))) (PRE pos + SUC n) /\
  LENGTH pi <= 2 * n + 2
Proof
 strip_tac >> Cases_on `stl` >>
 rw [state_program_list] >>
 METIS_TAC [
  NTH_SOME_DROP,
  IO_bounded_execution_in_order_step_list_sound
 ]
QED

(* FIXME: switch to NTH as version below? *)
Theorem IO_bounded_execution_in_order_step_sound:
 translate_val_list_SORTED ==>
 !l s cs fs pos n i il pi.
  State_st_list_well_formed_ok (State_st_list l s cs fs) ==>
  SORTED bound_name_instr_le l ==>
  Completed_list_up_to sem_expr (State_st_list l s cs fs) (PRE pos) ==>
  DROP (PRE pos) l = i::il ==>
  ~(Completed_list sem_expr (State_st_list l s cs fs) i) ==>
  IO_bounded_execution translate_val_list sem_expr (State_st_list l s cs fs) pos (SUC n) = SOME pi ==>
  FST (HD pi) = State_st_list l s cs fs /\
  step_execution in_order_step (MAP step_list_to_step pi) /\
  Completed_list_up_to sem_expr (SND (SND (LAST pi))) (PRE pos + SUC n) /\
  LENGTH pi <= 2 * n + 2
Proof
 METIS_TAC [
  step_execution_in_order_step_list_step,
  IO_bounded_execution_in_order_step_list_sound
 ]
QED

Theorem IO_bounded_execution_in_order_step_sound_NTH:
 translate_val_list_SORTED ==>
 !stl pos n i pi.
  State_st_list_well_formed_ok stl ==>
  SORTED bound_name_instr_le (state_program_list stl) ==>
  Completed_list_up_to sem_expr stl (PRE pos) ==>
  NTH (PRE pos) (state_program_list stl) = SOME i ==>
  ~(Completed_list sem_expr stl i) ==>
  IO_bounded_execution translate_val_list sem_expr stl pos (SUC n) = SOME pi ==>
  FST (HD pi) = stl /\
  step_execution in_order_step (MAP step_list_to_step pi) /\
  Completed_list_up_to sem_expr (SND (SND (LAST pi))) (PRE pos + SUC n) /\
  LENGTH pi <= 2 * n + 2
Proof
 strip_tac >> Cases_on `stl` >>
 rw [state_program_list] >>
 METIS_TAC [
  NTH_SOME_DROP,
  IO_bounded_execution_in_order_step_sound
 ]
QED

val _ = export_theory ();
