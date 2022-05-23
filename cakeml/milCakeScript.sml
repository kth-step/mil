open preamble ml_translatorLib ml_translatorTheory ml_progLib ml_progTheory mllistTheory mlmapTheory mlprettyprinterTheory comparisonTheory totoTheory milTheory milExecutableUtilityTheory milExecutableTransitionTheory milExecutableInitializationTheory milExecutableIOTheory milExecutableIOTraceTheory milExecutableExamplesTheory basisFunctionsLib Word64ProgTheory;

(* ================================================ *)
(* CakeML friendly versions of executable functions *)
(* ================================================ *)

val _ = new_theory "milCake";

(* ----------------------------------- *)
(* Datatypes and auxiliary definitions *)
(* ----------------------------------- *)

(* FIXME: does not get converted to use Map.map properly *)
Datatype:
 State_list_cake =
  State_st_list_cake (i list) ((num,word64) mlmap$map) (num list) (num list)
End

Definition state_list_cake_to_state:
 state_list_cake_to_state (State_st_list_cake l s cs fs) =
  State_st (LIST_TO_SET l) (to_fmap s) (LIST_TO_SET cs) (LIST_TO_SET fs)
End

Definition state_list_cake_to_state_list:
 state_list_cake_to_state_list (State_st_list_cake l s cs fs) =
  State_st_list l (to_fmap s) cs fs
End

Definition ll_state_list_cake_to_ll_state_list:
 ll_state_list_cake_to_ll_state_list ((ll:ll),stlc) =
  (ll,state_list_cake_to_state_list stlc)
End

(* TODO: generalize to arbitrary type, option_f *)
Definition option_ll_state_list_cake_to_ll_state_list:
 (option_ll_state_list_cake_to_ll_state_list NONE = NONE)
 /\
 (option_ll_state_list_cake_to_ll_state_list (SOME llstlc) =
   SOME (ll_state_list_cake_to_ll_state_list llstlc))
End

Definition step_list_cake_to_step_list:
 step_list_cake_to_step_list (stlc,(ll:ll),stlc') =
  (state_list_cake_to_state_list stlc,ll,state_list_cake_to_state_list stlc')
End

(* TODO: generalize to arbitrary type, option_f *)
Definition option_map_step_list_cake_to_step_list:
 (option_map_step_list_cake_to_step_list NONE = NONE)
 /\
 (option_map_step_list_cake_to_step_list (SOME exec) =
   SOME (MAP step_list_cake_to_step_list exec))
End

Definition option_state_list_cake_obs_list_to_state_list_obs_list:
 (option_state_list_cake_obs_list_to_state_list_obs_list NONE = NONE)
 /\
 (option_state_list_cake_obs_list_to_state_list_obs_list (SOME (stlc,(tr:obs list))) =
  SOME (state_list_cake_to_state_list stlc,tr))
End

Definition State_list_cake_ok:
 State_list_cake_ok (State_st_list_cake l s cs fs) = (map_ok s)
End

Definition sem_expr_cake_ok:
 sem_expr_cake_ok 
  (f : e -> (num,word64) map -> word64 option)
  (f' : e -> s -> word64 option) =
  (!s c. map_ok s ==> f c s = f' c (to_fmap s))
End

Definition str_may_list_find_cake:
 (str_may_list_find_cake f [] s t r ta = [])
 /\
 (str_may_list_find_cake f ((i_assign t' c' (o_internal e))::ls) s t r ta =
   str_may_list_find_cake f ls s t r ta)
 /\
 (str_may_list_find_cake f ((i_assign t' c' (o_load r' ta'))::ls) s t r ta =
   str_may_list_find_cake f ls s t r ta)
 /\
 (str_may_list_find_cake f ((i_assign t' c' (o_store r' ta' tv'))::ls) s t r ta =
  case lookup s ta' of
  | NONE =>
    if (t' >= t) \/ (r' <> r) then
      str_may_list_find_cake f ls s t r ta
    else
      (case f c' s of
      | NONE => i_assign t' c' (o_store r' ta' tv')::str_may_list_find_cake f ls s t r ta
      | SOME v =>
        if v <> val_false then
          i_assign t' c' (o_store r' ta' tv')::str_may_list_find_cake f ls s t r ta
        else
          str_may_list_find_cake f ls s t r ta)
   | SOME v1 =>
     case lookup s ta of
     | NONE =>
       if (t' >= t) \/ (r' <> r) then
         str_may_list_find_cake f ls s t r ta
       else
         (case f c' s of
         | NONE => i_assign t' c' (o_store r' ta' tv')::str_may_list_find_cake f ls s t r ta
         | SOME v =>
           if v <> val_false then
             i_assign t' c' (o_store r' ta' tv')::str_may_list_find_cake f ls s t r ta
           else
             str_may_list_find_cake f ls s t r ta)
     | SOME v2 =>
       if (t' >= t) \/ (r' <> r) \/ (v1 <> v2) then
         str_may_list_find_cake f ls s t r ta
       else
         (case f c' s of
         | NONE => i_assign t' c' (o_store r' ta' tv')::str_may_list_find_cake f ls s t r ta
         | SOME v =>
           if v <> val_false then
             i_assign t' c' (o_store r' ta' tv')::str_may_list_find_cake f ls s t r ta
           else
             str_may_list_find_cake f ls s t r ta))
End

Definition str_act_list_cond_cake:
 (str_act_list_cond_cake f [] s t' r' ta' ta = [])
 /\
 (str_act_list_cond_cake f ((i_assign t'' c'' (o_internal e))::ls) s t' r' ta' ta = str_act_list_cond_cake f ls s t' r' ta' ta)
 /\
 (str_act_list_cond_cake f ((i_assign t'' c'' (o_load r'' ta''))::ls) s t' r' ta' ta = str_act_list_cond_cake f ls s t' r' ta' ta)
 /\
 (str_act_list_cond_cake f ((i_assign t'' c'' (o_store r'' ta'' tv''))::ls) s t' r' ta' ta =
  case f c'' s of
  | NONE => str_act_list_cond_cake f ls s t' r' ta' ta
  | SOME fv =>
    case lookup s ta'' of
    | SOME v1 =>
      (case lookup s ta' of
       | SOME v2 =>
         (case lookup s ta of
          | SOME v3 =>
            if (t'' > t') /\ (r'' = r') /\ (fv <> val_false) /\ (v1 = v2 \/ v1 = v3) then
              (i_assign t'' c'' (o_store r'' ta'' tv''))::(str_act_list_cond_cake f ls s t' r' ta' ta)
            else
              str_act_list_cond_cake f ls s t' r' ta' ta
          | NONE =>
            if (t'' > t') /\ (r'' = r') /\ (fv <> val_false) /\ (v1 = v2) then
              (i_assign t'' c'' (o_store r'' ta'' tv''))::(str_act_list_cond_cake f ls s t' r' ta' ta)
            else
              str_act_list_cond_cake f ls s t' r' ta' ta)
       | NONE =>
         (case lookup s ta of
          | SOME v3 =>
              if (t'' > t') /\ (r'' = r') /\ (fv <> val_false) /\ (v1 = v3) then
                (i_assign t'' c'' (o_store r'' ta'' tv''))::(str_act_list_cond_cake f ls s t' r' ta' ta)
              else
                str_act_list_cond_cake f ls s t' r' ta' ta
          | NONE => str_act_list_cond_cake f ls s t' r' ta' ta))
    | NONE => str_act_list_cond_cake f ls s t' r' ta' ta)
End

Definition str_act_list_find_cake:
 (str_act_list_find_cake f [] s r ta l1 = [])
 /\
 (str_act_list_find_cake f ((i_assign t' c' (o_internal e))::ls) s r ta l1 = str_act_list_find_cake f ls s r ta l1)
 /\
 (str_act_list_find_cake f ((i_assign t' c' (o_load r' ta'))::ls) s r ta l1 = str_act_list_find_cake f ls s r ta l1)
 /\
 (str_act_list_find_cake f ((i_assign t' c' (o_store r' ta' tv'))::ls) s r ta l1 =
   case str_act_list_cond_cake f l1 s t' r' ta' ta of
   | [] =>
     if r' <> r then str_act_list_find_cake f ls s r ta l1
     else i_assign t' c' (o_store r' ta' tv')::str_act_list_find_cake f ls s r ta l1
   | _ => str_act_list_find_cake f ls s r ta l1)
End

Definition str_may_list_cake:
 str_may_list_cake f (State_st_list_cake l s cs fs) t =
  case addr_of_list l t of
  | SOME (r,ta) => str_may_list_find_cake f l s t r ta
  | NONE => []
End

Definition str_act_list_cake:
 str_act_list_cake f (State_st_list_cake l s cs fs) t =
  case addr_of_list l t of
  | NONE => []
  | SOME (r,ta) =>
    let l' = str_may_list_cake f (State_st_list_cake l s cs fs) t in
    str_act_list_find_cake f l' s r ta l'
End

Definition sem_instr_exe_cake:
 (sem_instr_exe_cake f (i_assign t c (o_internal e)) (State_st_list_cake l s cs fs) =
  case f e s of
  | NONE => NONE
  | SOME v => SOME (v, obs_internal))
 /\
 (sem_instr_exe_cake f (i_assign t c (o_store r ta tv)) (State_st_list_cake l s cs fs) =
  case lookup s tv of
  | NONE => NONE
  | SOME v =>
    (case lookup s ta of
     | NONE => NONE
     | SOME a => SOME (v, obs_internal)))
 /\
 (sem_instr_exe_cake f (i_assign t c (o_load res_MEM ta)) (State_st_list_cake l s cs fs) =
  case bound_names_program_list (str_act_list_cake f (State_st_list_cake l s cs fs) t) of
  | [] => NONE
  | [ts] =>
    (case lookup s ta of
     | NONE => NONE
     | SOME a =>
       (case lookup s ts of
        | NONE => NONE
        | SOME v =>
          if MEMBER ts cs then
            SOME (v, obs_dl a)
          else
            SOME (v, obs_internal)))
  | _::_::_ => NONE)
 /\
 (sem_instr_exe_cake f (i_assign t c (o_load r ta)) (State_st_list_cake l s cs fs) =
  case bound_names_program_list (str_act_list_cake f (State_st_list_cake l s cs fs) t) of
  | [] => NONE
  | [ts] =>
    (case lookup s ta of
     | NONE => NONE
     | SOME a =>
       (case lookup s ts of
        | NONE => NONE
        | SOME v => SOME (v, obs_internal)))
  | _::_::_ => NONE)
End

Definition Completed_list_cake:
 (Completed_list_cake f_sem (State_st_list_cake l s cs fs) (i_assign t c (o_store res_MEM t1 t2)) =
  (f_sem c s = SOME val_false \/ MEMBER t cs)) 
 /\
 (Completed_list_cake f_sem (State_st_list_cake l s cs fs) (i_assign t c (o_store res_PC t1 t2)) =
  (f_sem c s = SOME val_false \/ MEMBER t fs))
 /\
 (Completed_list_cake f_sem (State_st_list_cake l s cs fs) (i_assign t c op) =
  (f_sem c s = SOME val_false \/ lookup s t <> NONE))
End

(* ------------------------ *)
(* Initialization functions *)
(* ------------------------ *)

Definition empty_state_list_cake:
 empty_state_list_cake = State_st_list_cake [] (empty num_cmp) [] []
End

Definition initialize_resource_at_list_cake:
 (initialize_resource_at_list_cake (State_st_list_cake il0 s0 cl0 fl0) res_PC a v t t' t'' =
   let il1 = il0 ++ instrs_completed_store_list res_PC val_zero v t t' t'' in
   let s1 = insert (insert (insert s0 t val_zero) t' v) t'' v in
   let fl1 = t''::fl0 in
   (State_st_list_cake il1 s1 cl0 fl1))
 /\
 (initialize_resource_at_list_cake (State_st_list_cake il0 s0 cl0 fl0) res_REG a v t t' t'' =
   let il1 = il0 ++ instrs_completed_store_list res_REG a v t t' t'' in
   let s1 = insert (insert (insert s0 t a) t' v) t'' v in
   (State_st_list_cake il1 s1 cl0 fl0))
 /\
 (initialize_resource_at_list_cake (State_st_list_cake il0 s0 cl0 fl0) res_MEM a v t t' t'' =
   let il1 = il0 ++ instrs_completed_store_list res_MEM a v t t' t'' in
   let s1 = insert (insert (insert s0 t a) t' v) t'' v in
   let cl1 = t''::cl0 in
   (State_st_list_cake il1 s1 cl1 fl0))
End

Definition initialize_pc_without_fetch_at_list_cake:
 initialize_pc_without_fetch_at_list_cake (State_st_list_cake il0 s0 cl0 fl0) (a:word64) v t t' t'' =
  let il1 = il0 ++ instrs_completed_store_list res_PC val_zero v t t' t'' in
  let s1 = insert (insert (insert s0 t val_zero) t' v) t'' v in
  (State_st_list_cake il1 s1 cl0 fl0)
End

Definition init_res_val_list_cake:
 init_res_val_list_cake r (stlc,tmax) (a,v) =
  let t = SUC tmax in
  let t' = SUC t in
  let t'' = SUC t' in
  (initialize_resource_at_list_cake stlc r a v t t' t'', t'')
End

Definition init_pc_without_fetch_val_list_cake:
 init_pc_without_fetch_val_list_cake (stlc,tmax) ((a,v):word64#word64) =
  let t = SUC tmax in
  let t' = SUC t in
  let t'' = SUC t' in
  (initialize_pc_without_fetch_at_list_cake stlc a v t t' t'', t'')
End

Definition init_res_list_cake:
 init_res_list_cake r stlc tmax avl =
  FOLDL (init_res_val_list_cake r) (stlc,tmax) avl
End

Definition initialize_state_list_cake:
 initialize_state_list_cake memavl regavl pcv =
  let (stl,tmax) = (empty_state_list_cake,0) in
  let (stl,tmax) = init_res_list_cake res_MEM stl tmax memavl in
  let (stl,tmax) = init_res_list_cake res_REG stl tmax regavl in
  let (stl,tmax) = init_res_val_list_cake res_PC (stl,tmax) (val_zero,pcv) in
  (stl,tmax)
End

Definition initialize_state_without_pc_fetch_list:
 initialize_state_without_pc_fetch_list_cake memavl regavl pcv =
  let (stl,tmax) = (empty_state_list_cake,0) in
  let (stl,tmax) = init_res_list_cake res_MEM stl tmax memavl in
  let (stl,tmax) = init_res_list_cake res_REG stl tmax regavl in
  let (stl,tmax) = init_pc_without_fetch_val_list_cake (stl,tmax) (val_zero,pcv) in
  (stl,tmax)
End

(* -------------------- *)
(* Transition functions *)
(* -------------------- *)

Definition OoO_step_name_cake:
 OoO_step_name_cake step_list (State_st_list_cake l s cs fs) t : (ll # State_list_cake) option =
  case FIND_instr t l of
  | NONE => NONE
  | SOME i => step_list (State_st_list_cake l s cs fs) i
End

Definition OoO_Exe_list_instr_not_stored_guard_true_sem_instr_cake:
 OoO_Exe_list_instr_not_stored_guard_true_sem_instr_cake (State_st_list_cake l s cs fs)
  (i_assign t c mop) v obs : (ll # State_list_cake) =
 (ll_lb obs act_exe_list t, State_st_list_cake l (insert s t v) cs fs)
End

Definition OoO_Exe_list_instr_not_stored_guard_true_cake:
 OoO_Exe_list_instr_not_stored_guard_true_cake f stlc i =
  case sem_instr_exe_cake f i stlc of
  | NONE => NONE
  | SOME (v,obs) => SOME (OoO_Exe_list_instr_not_stored_guard_true_sem_instr_cake stlc i v obs)
End

Definition OoO_Exe_list_instr_not_stored_cake:
 OoO_Exe_list_instr_not_stored_cake f (State_st_list_cake l s cs fs)
  (i_assign t c mop) : (ll # State_list_cake) option =
  case f c s of
  | NONE => NONE
  | SOME v =>
    if v <> val_false then
      OoO_Exe_list_instr_not_stored_guard_true_cake f (State_st_list_cake l s cs fs) (i_assign t c mop)
    else NONE
End

Definition OoO_Exe_list_instr_cake:
 OoO_Exe_list_instr_cake f (State_st_list_cake l s cs fs)
  (i_assign t c mop) : (ll # State_list_cake) option =
  case lookup s t of
  | NONE => OoO_Exe_list_instr_not_stored_cake f (State_st_list_cake l s cs fs) (i_assign t c mop)
  | SOME _ => NONE
End

Definition OoO_Exe_list_cake:
 OoO_Exe_list_cake f = OoO_step_name_cake (OoO_Exe_list_instr_cake f)
End

Definition OoO_Cmt_list_stored_incomplete_cake:
 OoO_Cmt_list_stored_incomplete_cake f (State_st_list_cake l s cs fs) t ta tv : (ll # State_list_cake) option =
  case lookup s ta of
  | NONE => NONE
  | SOME a =>
    (case lookup s tv of
     | NONE => NONE
     | SOME v =>
       (case str_may_list_cake f (State_st_list_cake l s cs fs) t of
        | [] => SOME (ll_lb (obs_ds a) (act_cmt_list a v) t, (State_st_list_cake l s (t::cs) fs))
        | i::il =>
          if MEMBER (max_bound_name_list (i::il)) cs then
            SOME (ll_lb (obs_ds a) (act_cmt_list a v) t, (State_st_list_cake l s (t::cs) fs))
          else NONE))
End

Definition OoO_Cmt_list_stored_cake:
 OoO_Cmt_list_stored_cake f (State_st_list_cake l s cs fs) t ta tv : (ll # State_list_cake) option =
  if MEMBER t cs then NONE else
  OoO_Cmt_list_stored_incomplete_cake f (State_st_list_cake l s cs fs) t ta tv
End

Definition OoO_Cmt_list_instr_cake:
 (OoO_Cmt_list_instr_cake f (State_st_list_cake l s cs fs)
  (i_assign t c (o_store res_MEM ta tv)) : (ll # State_list_cake) option =
  case lookup s t of
  | NONE => NONE
  | SOME _ => OoO_Cmt_list_stored_cake f (State_st_list_cake l s cs fs) t ta tv)
 /\
 (OoO_Cmt_list_instr_cake f stl i = NONE)
End

Definition OoO_Cmt_list_cake:
 OoO_Cmt_list_cake f = OoO_step_name_cake (OoO_Cmt_list_instr_cake f)
End

Definition OoO_Ftc_list_stored_incomplete_cake:
 OoO_Ftc_list_stored_incomplete_cake f1 f2
  (State_st_list_cake l s cs fs) t v : (ll # State_list_cake) option =
  case str_may_list_cake f2 (State_st_list_cake l s cs fs) t of
  | [] =>
    let l' = f1 v (max_bound_name_list l) in
    SOME (ll_lb (obs_il v) (act_ftc_list l') t, (State_st_list_cake (l++l') s cs (t::fs)))
  | i::il =>
    if MEMBER (max_bound_name_list (i::il)) fs then
      let l' = f1 v (max_bound_name_list l) in
      SOME (ll_lb (obs_il v) (act_ftc_list l') t, (State_st_list_cake (l++l') s cs (t::fs)))
    else NONE
End

Definition OoO_Ftc_list_stored_cake:
 OoO_Ftc_list_stored_cake f1 f2 (State_st_list_cake l s cs fs) t v : (ll # State_list_cake) option =
  if MEMBER t fs then NONE else
  OoO_Ftc_list_stored_incomplete_cake f1 f2 (State_st_list_cake l s cs fs) t v
End

Definition OoO_Ftc_list_instr_cake:
 (OoO_Ftc_list_instr_cake f1 f2 (State_st_list_cake l s cs fs)
  (i_assign t c (o_store res_PC t1 t2):i) : (ll # State_list_cake) option =
  case lookup s t of
  | NONE => NONE
  | SOME v => OoO_Ftc_list_stored_cake f1 f2 (State_st_list_cake l s cs fs) t v)
 /\
 (OoO_Ftc_list_instr_cake f1 f2 stlc i = NONE)
End

Definition OoO_Ftc_list_cake:
 OoO_Ftc_list_cake f1 f2 = OoO_step_name_cake (OoO_Ftc_list_instr_cake f1 f2)
End

Definition OoO_step_list_instr_cake:
 OoO_step_list_instr_cake f1 f2 ((State_st_list_cake l s cs fs):State_list_cake) (i_assign t c mop) =
  case lookup s t of
  | NONE => OoO_Exe_list_instr_not_stored_cake f2 (State_st_list_cake l s cs fs) (i_assign t c mop)
  | SOME v =>
    (case mop of
     | o_store res_MEM ta tv => OoO_Cmt_list_stored_cake f2 (State_st_list_cake l s cs fs) t ta tv
     | o_store res_PC ta tv => OoO_Ftc_list_stored_cake f1 f2 (State_st_list_cake l s cs fs) t v
     | _ => NONE)
End

Definition OoO_step_list_cake:
 OoO_step_list_cake f1 f2 = OoO_step_name_cake (OoO_step_list_instr_cake f1 f2)
End

Definition IO_bounded_execution_acc_cake:
 IO_bounded_execution_acc_cake f_tran f_sem
  (State_st_list_cake l s cs fs) (pos:num) (n:num)
  (exec:(State_list_cake # ll # State_list_cake) list) :
 ((State_list_cake # ll # State_list_cake) list) option =
 case n of
 | 0 => SOME exec
 | SUC n' =>
   (case drop l pos of
    | [] => SOME exec
    | i_assign t c mop::il =>
      (case lookup s t of
      | NONE =>
        (case f_sem c s of
        | NONE => NONE
        | SOME v =>
          if v <> val_false then
            (case sem_instr_exe_cake f_sem (i_assign t c mop) (State_st_list_cake l s cs fs) of
             | NONE => NONE
             | SOME (v',obs) =>
               let (ll,stl) = OoO_Exe_list_instr_not_stored_guard_true_sem_instr_cake
                 (State_st_list_cake l s cs fs) (i_assign t c mop) v' obs in
                case mop of
                | o_store res_MEM ta tv =>
                  (case OoO_Cmt_list_stored_cake f_sem stl t ta tv of
                   | NONE => NONE
                   | SOME (ll',stl') =>
                     IO_bounded_execution_acc_cake f_tran f_sem stl' (SUC pos) n'
                      (exec++[(State_st_list_cake l s cs fs,ll,stl);(stl,ll',stl')]))
                | o_store res_PC ta tv =>
                  (case OoO_Ftc_list_stored_cake f_tran f_sem stl t v' of
                   | NONE => NONE
                   | SOME (ll',stl') =>
                     IO_bounded_execution_acc_cake f_tran f_sem stl' (SUC pos) n'
                      (exec++[((State_st_list_cake l s cs fs),ll,stl);(stl,ll',stl')]))
                | _ => (* instruction is completed, move on *)
                  IO_bounded_execution_acc_cake f_tran f_sem stl (SUC pos) n'
                   (exec++[(State_st_list_cake l s cs fs,ll,stl)]))
          else (* instruction is completed, move on *)
            IO_bounded_execution_acc_cake f_tran f_sem (State_st_list_cake l s cs fs) (SUC pos) n' exec)
      | SOME v =>
        (case mop of
         | o_store res_MEM ta tv =>
           if MEMBER t cs then (* instruction is completed, move on *)
             IO_bounded_execution_acc_cake f_tran f_sem (State_st_list_cake l s cs fs) (SUC pos) n' exec
           else
             (case OoO_Cmt_list_stored_incomplete_cake f_sem (State_st_list_cake l s cs fs) t ta tv of
             | NONE => NONE
             | SOME (ll,stl) => (* instruction is completed, move on *)
               IO_bounded_execution_acc_cake f_tran f_sem stl (SUC pos) n'
                (exec++[(State_st_list_cake l s cs fs,ll,stl)]))
         | o_store res_PC ta tv =>
           if MEMBER t fs then (* instruction is completed, move on *)
             IO_bounded_execution_acc_cake f_tran f_sem (State_st_list_cake l s cs fs) (SUC pos) n' exec
           else
             (case OoO_Ftc_list_stored_incomplete_cake f_tran f_sem (State_st_list_cake l s cs fs) t v of
              | NONE => NONE
              | SOME (ll,stl) => (* instruction is completed, move on *)
                IO_bounded_execution_acc_cake f_tran f_sem stl (SUC pos) n'
                 (exec++[(State_st_list_cake l s cs fs,ll,stl)]))
         | _ => (* instruction is completed, move on *)
           IO_bounded_execution_acc_cake f_tran f_sem (State_st_list_cake l s cs fs) (SUC pos) n' exec)))
End

Definition IO_bounded_execution_cake:
 IO_bounded_execution_cake f_tran f_sem
  (stlc:State_list_cake) (pos:num) (n:num) :
 ((State_list_cake # ll # State_list_cake) list) option =
  IO_bounded_execution_acc_cake f_tran f_sem stlc (PRE pos) n []
End

Definition IO_bounded_trace_acc_cake:
 IO_bounded_trace_acc_cake f_tran f_sem
  (State_st_list_cake l s cs fs) (pos:num) (n:num)
  (tr:obs list) : (State_list_cake # obs list) option =
 case n of
 | 0 => SOME (State_st_list_cake l s cs fs,tr)
 | SUC n' =>
   (case drop l pos of
    | [] => SOME (State_st_list_cake l s cs fs,tr)
    | i_assign t c mop::il =>
      (case lookup s t of
      | NONE =>
        (case f_sem c s of
        | NONE => NONE
        | SOME v =>
          if v <> val_false then
            (case sem_instr_exe_cake f_sem (i_assign t c mop) (State_st_list_cake l s cs fs) of
             | NONE => NONE
             | SOME (v',obs) =>
               let (ll,stl) =
                OoO_Exe_list_instr_not_stored_guard_true_sem_instr_cake
                 (State_st_list_cake l s cs fs) (i_assign t c mop) v' obs in
                case mop of
                | o_store res_MEM ta tv =>
                  (case OoO_Cmt_list_stored_cake f_sem stl t ta tv of
                   | NONE => NONE
                   | SOME (ll',stl') =>
                     let ob = obs_of_ll ll in
                     let ob' = obs_of_ll ll' in
                     if obs_visible ob then
                       IO_bounded_trace_acc_cake f_tran f_sem stl' (SUC pos) n' (tr++[ob;ob'])
                     else
                       IO_bounded_trace_acc_cake f_tran f_sem stl' (SUC pos) n' (tr++[ob']))
                | o_store res_PC ta tv =>
                  (case OoO_Ftc_list_stored_cake f_tran f_sem stl t v' of
                   | NONE => NONE
                   | SOME (ll',stl') =>
                     let ob = obs_of_ll ll in
                     let ob' = obs_of_ll ll' in
                     if obs_visible ob then
                       IO_bounded_trace_acc_cake f_tran f_sem stl' (SUC pos) n' (tr++[ob;ob'])
                     else
                       IO_bounded_trace_acc_cake f_tran f_sem stl' (SUC pos) n' (tr++[ob']))
                | _ => (* instruction is completed, move on *)
                  let ob = obs_of_ll ll in
                  if obs_visible ob then
                    IO_bounded_trace_acc_cake f_tran f_sem stl (SUC pos) n' (tr++[ob])
                  else
                    IO_bounded_trace_acc_cake f_tran f_sem stl (SUC pos) n' tr)
          else (* instruction is completed, move on *)
            IO_bounded_trace_acc_cake f_tran f_sem (State_st_list_cake l s cs fs) (SUC pos) n' tr)
      | SOME v =>
        (case mop of
         | o_store res_MEM ta tv =>
           if MEMBER t cs then (* instruction is completed, move on *)
             IO_bounded_trace_acc_cake f_tran f_sem (State_st_list_cake l s cs fs) (SUC pos) n' tr
           else
             (case OoO_Cmt_list_stored_incomplete_cake f_sem (State_st_list_cake l s cs fs) t ta tv of
             | NONE => NONE
             | SOME (ll,stl) => (* instruction is completed, move on *)
               let ob = obs_of_ll ll in
               IO_bounded_trace_acc_cake f_tran f_sem stl (SUC pos) n' (tr++[ob]))
         | o_store res_PC ta tv =>
           if MEMBER t fs then (* instruction is completed, move on *)
             IO_bounded_trace_acc_cake f_tran f_sem (State_st_list_cake l s cs fs) (SUC pos) n' tr
           else
             (case OoO_Ftc_list_stored_incomplete_cake f_tran f_sem (State_st_list_cake l s cs fs) t v of
              | NONE => NONE
              | SOME (ll,stl) => (* instruction is completed, move on *)
                let ob = obs_of_ll ll in
                IO_bounded_trace_acc_cake f_tran f_sem stl (SUC pos) n' (tr++[ob]))
         | _ => (* instruction is completed, move on *)
           IO_bounded_trace_acc_cake f_tran f_sem (State_st_list_cake l s cs fs) (SUC pos) n' tr)))
End

Definition IO_bounded_trace_aux_cake:
 IO_bounded_trace_aux_cake f_tran f_sem stlc (pos:num) (n:num) : (State_list_cake # obs list) option =
  IO_bounded_trace_acc_cake f_tran f_sem stlc (PRE pos) n []
End

Definition IO_bounded_trace_cake:
 IO_bounded_trace_cake f_tran f_sem stlc (pos:num) (n:num) : (obs list) option =
  case IO_bounded_trace_aux_cake f_tran f_sem stlc pos n of
  | SOME (stlc,tr) => SOME tr
  | _ => NONE
End

(* ------------------------------- *)
(* Expression evaluation functions *)
(* ------------------------------- *)

Definition word_2comp_cake:
 word_2comp_cake (v:mil$v) : mil$v =
  n2w ((2**64) - w2n v)
End

Definition i2w_cake:
 i2w_cake (i:int) : mil$v =
  if i < 0 then word_2comp_cake (n2w (Num(-i))) else n2w (Num i)
End

Definition word_msb_cake:
 word_msb_cake (v:mil$v) : bool =
  ((word_and 0x8000000000000000w v) = 0x8000000000000000w)
End

Definition w2i_cake:
 w2i_cake (v:mil$v) =
  if word_msb_cake v then
    ~(int_of_num (w2n (word_2comp_cake v)))
  else
    int_of_num (w2n v)
End

Definition nzcv_cake:
 nzcv_cake (a:mil$v) (b:mil$v) =
  let q = w2n a + w2n (word_2comp_cake b) in
  let r = (n2w q):mil$v in
  (word_msb_cake r, r = 0w, BIT 64 q \/ (b = 0w),
   ~(word_msb_cake a = word_msb_cake b) /\ ~(word_msb_cake r = word_msb_cake a))
End

Definition v_and_cake:
 v_and_cake (v1:mil$v) (v2:mil$v) : mil$v = word_and v1 v2
End

Definition v_or_cake:
 v_or_cake (v1:mil$v) (v2:mil$v) : mil$v = word_or v1 v2
End

Definition v_xor_cake:
 v_xor_cake (v1:mil$v) (v2:mil$v) : mil$v = word_xor v1 v2
End

Definition v_add_cake:
 v_add_cake (v1:mil$v) (v2:mil$v) : mil$v = word_add v1 v2
End

Definition v_sub_cake:
 v_sub_cake (v1:mil$v) (v2:mil$v) : mil$v = word_sub v1 v2
End

Definition v_mul_cake:
 v_mul_cake (v1:mil$v) (v2:mil$v) : mil$v = n2w (w2n v1 * w2n v2)
End

Definition v_div_cake:
 v_div_cake (v1:mil$v) (v2:mil$v) : mil$v = n2w (w2n v1 DIV w2n v2)
End

Definition v_sdiv_cake:
 v_sdiv_cake (v1:mil$v) (v2:mil$v) : mil$v =
  i2w_cake (w2i_cake v1 / w2i_cake v2)
End

Definition v_mod_cake:
 v_mod_cake (v1:mil$v) (v2:mil$v) : mil$v = n2w (w2n v1 MOD w2n v2)
End

Definition v_smod_cake:
 v_smod_cake (v1:mil$v) (v2:mil$v) : mil$v =
  i2w_cake (w2i_cake v1 % w2i_cake v2)
End

Definition v_lsl_cake:
 v_lsl_cake (v1:mil$v) (v2:mil$v) : mil$v = var_word_lsl v1 (w2n v2)
End

Definition v_lsr_cake:
 v_lsr_cake (v1:mil$v) (v2:mil$v) : mil$v = var_word_lsr v1 (w2n v2)
End

Definition v_asr_cake:
 v_asr_cake (v1:mil$v) (v2:mil$v) : mil$v = var_word_asr v1 (w2n v2)
End

Definition v_eq_cake:
 v_eq_cake (v1:mil$v) (v2:mil$v) : mil$v =
  if v1 = v2 then
    val_true
  else
    val_false
End

Definition v_neq_cake:
 v_neq_cake (v1:mil$v) (v2:mil$v) : mil$v =
  if v1 = v2 then
    val_false
  else
    val_true
End

Definition v_lt_cake:
 v_lt_cake (v1:mil$v) (v2:mil$v) : mil$v =
  let lt = (let (n,z,c,v) = nzcv_cake v1 v2 in ~c) in
  if lt then val_true else val_false
End

Definition v_slt_cake:
 v_slt_cake (v1:mil$v) (v2:mil$v) : mil$v =
  let lo = (let (n,z,c,v) = nzcv_cake v1 v2 in ~(n = v)) in
  if lo then val_true else val_false
End

Definition v_le_cake:
 v_le_cake (v1:mil$v) (v2:mil$v) : mil$v =
  let ls = (let (n,z,c,v) = nzcv_cake v1 v2 in ~c \/ z) in
  if ls then val_true else val_false
End

Definition v_sle_cake:
 v_sle_cake (v1:mil$v) (v2:mil$v) : mil$v =
  let le = (let (n,z,c,v) = nzcv_cake v1 v2 in z \/ ~(n = v)) in
  if le then val_true else val_false
End

Definition v_comp_cake:
 v_comp_cake (v:mil$v) : mil$v = word_1comp v
End

Definition v_not_cake:
 v_not_cake (v:mil$v) : mil$v =
  if v = val_false then
    val_true
  else
    val_false
End

Definition sem_expr_exe_cake:
 (sem_expr_exe_cake (e_val v) s = SOME v)
 /\
 (sem_expr_exe_cake (e_name t) s = lookup s t)
 /\
 (sem_expr_exe_cake (e_and e1 e2) s =
  case sem_expr_exe_cake e1 s of
  | SOME v1 =>
    (case sem_expr_exe_cake e2 s of
     | SOME v2 => SOME (v_and_cake v1 v2)
     | NONE => NONE)
  | NONE => NONE)
 /\
 (sem_expr_exe_cake (e_or e1 e2) s =
  case sem_expr_exe_cake e1 s of
  | SOME v1 =>
    (case sem_expr_exe_cake e2 s of
     | SOME v2 => SOME (v_or_cake v1 v2)
     | NONE => NONE)
  | NONE => NONE)
 /\
 (sem_expr_exe_cake (e_xor e1 e2) s =
  case sem_expr_exe_cake e1 s of
  | SOME v1 =>
    (case sem_expr_exe_cake e2 s of
     | SOME v2 => SOME (v_xor_cake v1 v2)
     | NONE => NONE)
  | NONE => NONE)
 /\
 (sem_expr_exe_cake (e_add e1 e2) s =
  case sem_expr_exe_cake e1 s of
  | SOME v1 =>
    (case sem_expr_exe_cake e2 s of
     | SOME v2 => SOME (v_add_cake v1 v2)
     | NONE => NONE)
  | NONE => NONE)
 /\
 (sem_expr_exe_cake (e_sub e1 e2) s =
  case sem_expr_exe_cake e1 s of
  | SOME v1 =>
    (case sem_expr_exe_cake e2 s of
     | SOME v2 => SOME (v_sub_cake v1 v2)
     | NONE => NONE)
  | NONE => NONE)
 /\
 (sem_expr_exe_cake (e_mul e1 e2) s =
  case sem_expr_exe_cake e1 s of
  | SOME v1 =>
    (case sem_expr_exe_cake e2 s of
     | SOME v2 => SOME (v_mul_cake v1 v2)
     | NONE => NONE)
  | NONE => NONE)
 /\
 (sem_expr_exe_cake (e_div e1 e2) s =
  case sem_expr_exe_cake e1 s of
  | SOME v1 =>
    (case sem_expr_exe_cake e2 s of
     | SOME v2 => SOME (v_div_cake v1 v2)
     | NONE => NONE)
  | NONE => NONE)
 /\
 (sem_expr_exe_cake (e_sdiv e1 e2) s =
  case sem_expr_exe_cake e1 s of
  | SOME v1 =>
    (case sem_expr_exe_cake e2 s of
     | SOME v2 => SOME (v_sdiv_cake v1 v2)
     | NONE => NONE)
  | NONE => NONE)
 /\
 (sem_expr_exe_cake (e_mod e1 e2) s =
  case sem_expr_exe_cake e1 s of
  | SOME v1 =>
    (case sem_expr_exe_cake e2 s of
     | SOME v2 => SOME (v_mod_cake v1 v2)
     | NONE => NONE)
  | NONE => NONE)
 /\
 (sem_expr_exe_cake (e_smod e1 e2) s =
  case sem_expr_exe_cake e1 s of
  | SOME v1 =>
    (case sem_expr_exe_cake e2 s of
     | SOME v2 => SOME (v_smod_cake v1 v2)
     | NONE => NONE)
  | NONE => NONE)
 /\
 (sem_expr_exe_cake (e_lsl e1 e2) s =
  case sem_expr_exe_cake e1 s of
  | SOME v1 =>
    (case sem_expr_exe_cake e2 s of
     | SOME v2 => SOME (v_lsl_cake v1 v2)
     | NONE => NONE)
  | NONE => NONE)
 /\
 (sem_expr_exe_cake (e_lsr e1 e2) s =
  case sem_expr_exe_cake e1 s of
  | SOME v1 =>
    (case sem_expr_exe_cake e2 s of
     | SOME v2 => SOME (v_lsr_cake v1 v2)
     | NONE => NONE)
  | NONE => NONE)
 /\
 (sem_expr_exe_cake (e_asr e1 e2) s =
  case sem_expr_exe_cake e1 s of
  | SOME v1 =>
    (case sem_expr_exe_cake e2 s of
     | SOME v2 => SOME (v_asr_cake v1 v2)
     | NONE => NONE)
  | NONE => NONE)
 /\
 (sem_expr_exe_cake (e_eq e1 e2) s =
  case sem_expr_exe_cake e1 s of
  | SOME v1 =>
    (case sem_expr_exe_cake e2 s of
     | SOME v2 => SOME (v_eq_cake v1 v2)
     | NONE => NONE)
  | NONE => NONE)
 /\
 (sem_expr_exe_cake (e_neq e1 e2) s =
  case sem_expr_exe_cake e1 s of
  | SOME v1 =>
    (case sem_expr_exe_cake e2 s of
     | SOME v2 => SOME (v_neq_cake v1 v2)
     | NONE => NONE)
  | NONE => NONE)
 /\
 (sem_expr_exe_cake (e_lt e1 e2) s =
  case sem_expr_exe_cake e1 s of
  | SOME v1 =>
    (case sem_expr_exe_cake e2 s of
     | SOME v2 => SOME (v_lt_cake v1 v2)
     | NONE => NONE)
  | NONE => NONE)
 /\
 (sem_expr_exe_cake (e_slt e1 e2) s =
  case sem_expr_exe_cake e1 s of
  | SOME v1 =>
    (case sem_expr_exe_cake e2 s of
     | SOME v2 => SOME (v_slt_cake v1 v2)
     | NONE => NONE)
  | NONE => NONE)
 /\
 (sem_expr_exe_cake (e_le e1 e2) s =
  case sem_expr_exe_cake e1 s of
  | SOME v1 =>
    (case sem_expr_exe_cake e2 s of
     | SOME v2 => SOME (v_le_cake v1 v2)
     | NONE => NONE)
  | NONE => NONE)
 /\
 (sem_expr_exe_cake (e_sle e1 e2) s =
  case sem_expr_exe_cake e1 s of
  | SOME v1 =>
    (case sem_expr_exe_cake e2 s of
     | SOME v2 => SOME (v_sle_cake v1 v2)
     | NONE => NONE)
  | NONE => NONE)
 /\
 (sem_expr_exe_cake (e_comp e) s =
  case sem_expr_exe_cake e s of
  | NONE => NONE
  | SOME v => SOME (v_comp_cake v))
 /\
 (sem_expr_exe_cake (e_not e) s =
  case sem_expr_exe_cake e s of
  | NONE => NONE
  | SOME v => SOME (v_not_cake v))
End

(* ----------------------------- *)
(* String functions for printing *)
(* ----------------------------- *)

Definition string_app_list_of_res:
 string_app_list_of_res r =
  case r of
  | res_PC => List [strlit "PC"]
  | res_REG => List [strlit "REG"]
  | res_MEM => List [strlit "MEM"]
End

Definition string_app_paren_binop:
 string_app_paren_binop lhs op rhs = 
  let lpar = List [strlit "("] in
  let ops = List [strlit " "; op; strlit " "] in
  let rpar = List [strlit ")"] in
  Append (Append (Append (Append lpar lhs) ops) rhs) rpar
End

Definition string_app_paren_unop:
 string_app_paren_unop op rhs = 
  let lpar = List [strlit "("] in
  let ops = List [op; strlit " "] in
  let rpar = List [strlit ")"] in
  Append (Append (Append lpar ops) rhs) rpar
End

Definition string_app_list_of_e:
 string_app_list_of_e e =
  case e of
  | e_val v => fromWord64 v
  | e_name t => fromNum t
  | e_and e1 e2 =>
    string_app_paren_binop (string_app_list_of_e e1) (strlit "&&") (string_app_list_of_e e2)
  | e_or e1 e2 =>
    string_app_paren_binop (string_app_list_of_e e1) (strlit "||") (string_app_list_of_e e2)
  | e_xor e1 e2 =>
    string_app_paren_binop (string_app_list_of_e e1) (strlit "\094") (string_app_list_of_e e2)
  | e_add e1 e2 =>
    string_app_paren_binop (string_app_list_of_e e1) (strlit "+") (string_app_list_of_e e2)
  | e_sub e1 e2 =>
    string_app_paren_binop (string_app_list_of_e e1) (strlit "-") (string_app_list_of_e e2)
  | e_mul e1 e2 =>
    string_app_paren_binop (string_app_list_of_e e1) (strlit "*") (string_app_list_of_e e2)
  | e_div e1 e2 =>
    string_app_paren_binop (string_app_list_of_e e1) (strlit "//") (string_app_list_of_e e2)
  | e_sdiv e1 e2 =>
    string_app_paren_binop (string_app_list_of_e e1) (strlit "/") (string_app_list_of_e e2)
  | e_mod e1 e2 =>
    string_app_paren_binop (string_app_list_of_e e1) (strlit "mod") (string_app_list_of_e e2)
  | e_smod e1 e2 =>
    string_app_paren_binop (string_app_list_of_e e1) (strlit "smod") (string_app_list_of_e e2)
  | e_lsl e1 e2 =>
    string_app_paren_binop (string_app_list_of_e e1) (strlit "<<") (string_app_list_of_e e2)
  | e_lsr e1 e2 =>
    string_app_paren_binop (string_app_list_of_e e1) (strlit ">>") (string_app_list_of_e e2)
  | e_asr e1 e2 =>
    string_app_paren_binop (string_app_list_of_e e1) (strlit "->>") (string_app_list_of_e e2)
  | e_eq e1 e2 =>
    string_app_paren_binop (string_app_list_of_e e1) (strlit "==") (string_app_list_of_e e2)
  | e_neq e1 e2 =>
    string_app_paren_binop (string_app_list_of_e e1) (strlit "!=") (string_app_list_of_e e2)
  | e_lt e1 e2 =>
    string_app_paren_binop (string_app_list_of_e e1) (strlit "<") (string_app_list_of_e e2)
  | e_slt e1 e2 =>
    string_app_paren_binop (string_app_list_of_e e1) (strlit "-<") (string_app_list_of_e e2)
  | e_le e1 e2 => 
    string_app_paren_binop (string_app_list_of_e e1) (strlit "<=") (string_app_list_of_e e2)
  | e_sle e1 e2 =>
    string_app_paren_binop (string_app_list_of_e e1) (strlit "-<=") (string_app_list_of_e e2)
  | e_comp e' => 
    string_app_paren_unop (strlit "~") (string_app_list_of_e e')
  | e_not e' =>
    string_app_paren_unop (strlit "!") (string_app_list_of_e e')
End

Definition string_app_list_of_o:
 string_app_list_of_o mop =
  case mop of 
  | o_internal e =>
    string_app_list_of_e e
  | o_load r ta =>
    let lhs = List [strlit "load"; strlit "("] in
    let rs = string_app_list_of_res r in
    let comma = List [strlit ","] in
    let rparen = List [strlit ")"] in
    Append (Append (Append (Append lhs rs) comma) (fromNum ta)) rparen
  | o_store r ta tv =>
    let lhs = List [strlit "store"; strlit "("] in
    let rs = string_app_list_of_res r in
    let comma = List [strlit ","] in
    let rparen = List [strlit ")"] in
    Append (Append (Append (Append (Append (Append lhs rs) comma) (fromNum ta)) comma) (fromNum tv)) rparen
End

Definition string_app_list_of_i:
 string_app_list_of_i (i_assign t c mop) =
  let asn = List [strlit " = "] in
  let qt = List [strlit " ? "] in
  Append (Append (Append (Append (fromNum t) asn) (string_app_list_of_e c)) qt) (string_app_list_of_o mop)
End

Definition string_app_list_of_obs:
 string_app_list_of_obs (ob:obs) =
  case ob of 
  | obs_internal => List [strlit "internal"]
  | obs_dl v => Append (List [strlit "dl "]) (fromWord64 v)
  | obs_ds v => Append (List [strlit "ds "]) (fromWord64 v)
  | obs_il v => Append (List [strlit "il "]) (fromWord64 v)
End

Definition string_app_list_of_act_list:
 string_app_list_of_act_list ac =
  case ac of
  | act_exe_list =>
    List [strlit "Exe"]
  | act_cmt_list a v =>
    let lpar = List [strlit "Cmt"; strlit "("] in
    let comma = List [strlit ","] in
    let rpar = List [strlit ")"] in
    Append (Append (Append (Append lpar (fromWord64 a)) comma) (fromWord64 v)) rpar
  | act_ftc_list l =>
    let lpar = List [strlit "Ftc"; strlit "("] in
    let rpar = List [strlit ")"] in
    Append (Append lpar (fromList string_app_list_of_i l)) rpar
End

Definition string_app_list_of_ll:
 string_app_list_of_ll (ll_lb ob ac t) =
  let lpar = List [strlit "<"] in
  let semicol = List [strlit ";"] in
  let rpar = List [strlit ">"] in
  Append (Append (Append (Append (Append (Append lpar (string_app_list_of_obs ob)) semicol)
   (string_app_list_of_act_list ac)) semicol) (fromNum t)) rpar
End

val _ = export_theory ();
