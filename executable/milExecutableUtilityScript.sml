open HolKernel boolLib Parse bossLib wordsLib optionTheory wordsTheory pred_setTheory listTheory rich_listTheory finite_mapTheory relationTheory sortingTheory ottTheory milUtilityTheory milTheory milSemanticsUtilityTheory milTracesTheory milMetaTheory milStoreTheory;

(* ========================================== *)
(* MIL semantics executable utility functions *)
(* ========================================== *)

val _ = new_theory "milExecutableUtility";

(* --------------------- *)
(* Auxiliary definitions *)
(* --------------------- *)

Definition FIND_instr:
 (FIND_instr t ([]:i list) : i option = NONE)
 /\
 (FIND_instr t (i::il) = if bound_name_instr i = t then SOME i else FIND_instr t il)
End

Definition FILTER_instr:
  FILTER_instr t (l:i list) : i list =
  FILTER ($= t o bound_name_instr) l
End

Definition NO_DUPLICATE:
  NO_DUPLICATE (i:'a) (l:'a list) = (MEM i l ==> UNIQUE i l)
End

Definition NO_DUPLICATES:
  NO_DUPLICATES (l:i list) = ALL_DISTINCT (MAP bound_name_instr l)
End

Definition NO_DUPLICATES_ALT:
  NO_DUPLICATES_ALT (l:i list) = (!t. NO_DUPLICATE t (MAP bound_name_instr l))
End

Definition NONCONT_SUBLIST:
 (NONCONT_SUBLIST l [] = T)
 /\
 (NONCONT_SUBLIST [] (h::t) = F)
 /\
 (NONCONT_SUBLIST (h1::t1) (h2::t2) =
  ((h1 = h2 /\ NONCONT_SUBLIST t1 t2) \/ (NONCONT_SUBLIST t1 (h2::t2))))
End

Definition MEM_bound_name_instr_unique:
 MEM_bound_name_instr_unique l =
  (!i i'. MEM i l ==> MEM i' l ==>
   bound_name_instr i = bound_name_instr i' ==>
   i = i')
End

(* ------------------------------- *)
(* Concrete datatypes and mappings *)
(* ------------------------------- *)

Datatype:
 State_list = State_st_list (i list) s (t list) (t list)
End

(* convert State_st_list to State_st *)
Definition state_list_to_state:
 state_list_to_state (State_st_list l s c fs) =
  State_st (LIST_TO_SET l) s (LIST_TO_SET c) (LIST_TO_SET fs)
End

Datatype:
 act_list = act_exe_list | act_cmt_list v v | act_ftc_list (i list)
End

Definition act_list_to_act:
 (act_list_to_act act_exe_list = act_exe)
 /\
 (act_list_to_act (act_cmt_list a v) = act_cmt a v)
 /\
 (act_list_to_act (act_ftc_list l) = act_ftc (LIST_TO_SET l))
End

Datatype:
 ll = ll_lb obs act_list t
End

Definition ll_to_l:
 ll_to_l (ll_lb (obs:obs) (al:act_list) (t:t)) = l_lb obs (act_list_to_act al) t
End

Definition State_st_list_ok:
 State_st_list_ok (State_st_list l s cs fs) = NO_DUPLICATES l
End

Definition State_st_list_well_formed_ok:
 State_st_list_well_formed_ok (State_st_list l s c fs) =
  (NO_DUPLICATES l /\ well_formed_state (state_list_to_state (State_st_list l s c fs)))
End

Definition instr_in_State_list:
 instr_in_State_list i (State_st_list l s cs fs) = MEM i l
End

(* ------------------------------------ *)
(* Executable semantic helper functions *)
(* ------------------------------------ *)

Definition addr_of_list:
 addr_of_list (il:i list) (t:t) : (res # t) option =
  case FIND_instr t il of
  | SOME (i_assign t' c (o_load r ta)) => SOME (r,ta)
  | SOME (i_assign t' c (o_store r ta tv)) => SOME (r,ta)
  | _ => NONE
End

(* find the certain store operations *)
Definition str_may_list_find:
 (str_may_list_find (f:e -> (t |-> v) -> v option) ([]:i list) (s:(t |-> v)) (t:t) (r:res) (ta:t): i list = [])
 /\
 (str_may_list_find f ((i_assign t' c' (o_internal e))::ls) s t r ta = str_may_list_find f ls s t r ta)
 /\
 (str_may_list_find f ((i_assign t' c' (o_load r' ta'))::ls) s t r ta = str_may_list_find f ls s t r ta)
 /\
 (str_may_list_find f ((i_assign t' c' (o_store r' ta' tv'))::ls) s t r ta =
  case FLOOKUP s ta' of
  | NONE =>
    if (t' >= t) \/ (r' <> r) then
      str_may_list_find f ls s t r ta
    else
      (case f c' s of
      | NONE => i_assign t' c' (o_store r' ta' tv')::str_may_list_find f ls s t r ta
      | SOME v =>
        if v <> val_false then
          i_assign t' c' (o_store r' ta' tv')::str_may_list_find f ls s t r ta
        else
          str_may_list_find f ls s t r ta)
   | SOME v1 =>
     case FLOOKUP s ta of
     | NONE =>
       if (t' >= t) \/ (r' <> r) then
         str_may_list_find f ls s t r ta
       else
         (case f c' s of
         | NONE => i_assign t' c' (o_store r' ta' tv')::str_may_list_find f ls s t r ta
         | SOME v =>
           if v <> val_false then
             i_assign t' c' (o_store r' ta' tv')::str_may_list_find f ls s t r ta
           else
             str_may_list_find f ls s t r ta)
     | SOME v2 =>
       if (t' >= t) \/ (r' <> r) \/ (v1 <> v2) then
         str_may_list_find f ls s t r ta
       else
         (case f c' s of
         | NONE => i_assign t' c' (o_store r' ta' tv')::str_may_list_find f ls s t r ta
         | SOME v =>
           if v <> val_false then
             i_assign t' c' (o_store r' ta' tv')::str_may_list_find f ls s t r ta
           else
             str_may_list_find f ls s t r ta))
End

Definition str_may_list:
 str_may_list (f: e -> (t |-> v) -> v option) ((State_st_list l s cs fs):State_list) (t:t) : i list =
  case addr_of_list l t of
  | SOME (r,ta) => str_may_list_find f l s t r ta
  | NONE => []
End

Definition str_act_list_cond:
 (str_act_list_cond (f:e -> (t |-> v) -> v option) ([]:i list) (s:(t |-> v)) (t':t) (r':res) (ta':t) (ta:t): i list = [])
 /\
 (str_act_list_cond f ((i_assign t'' c'' (o_internal e))::ls) s t' r' ta' ta = str_act_list_cond f ls s t' r' ta' ta)
 /\
 (str_act_list_cond f ((i_assign t'' c'' (o_load r'' ta''))::ls) s t' r' ta' ta = str_act_list_cond f ls s t' r' ta' ta)
 /\
 (str_act_list_cond f ((i_assign t'' c'' (o_store r'' ta'' tv''))::ls) s t' r' ta' ta =
  case f c'' s of
  | NONE => str_act_list_cond f ls s t' r' ta' ta
  | SOME fv =>
    case FLOOKUP s ta''  of
    | SOME v1 =>
      (case FLOOKUP s ta' of
       | SOME v2 =>
         (case FLOOKUP s ta of
          | SOME v3 =>
            if (t'' > t') /\ (r'' = r') /\ (fv <> val_false) /\ (v1 = v2 \/ v1 = v3) then
              (i_assign t'' c'' (o_store r'' ta'' tv''))::(str_act_list_cond f ls s t' r' ta' ta)
            else
              str_act_list_cond f ls s t' r' ta' ta
          | NONE =>
            if (t'' > t') /\ (r'' = r') /\ (fv <> val_false) /\ (v1 = v2) then
              (i_assign t'' c'' (o_store r'' ta'' tv''))::(str_act_list_cond f ls s t' r' ta' ta)
            else
              str_act_list_cond f ls s t' r' ta' ta)
       | NONE =>
         (case FLOOKUP s ta of
          | SOME v3 =>
              if (t'' > t') /\ (r'' = r') /\ (fv <> val_false) /\ (v1 = v3) then
                (i_assign t'' c'' (o_store r'' ta'' tv''))::(str_act_list_cond f ls s t' r' ta' ta)
              else
                str_act_list_cond f ls s t' r' ta' ta
          | NONE => str_act_list_cond f ls s t' r' ta' ta))
    | NONE => str_act_list_cond f ls s t' r' ta' ta)
End

Definition str_act_list_find:
 (str_act_list_find (f:e -> (t |-> v) -> v option) ([]:i list) (s:(t |-> v)) (r:res) (ta:t) (l1:i list): i list = [])
 /\
 (str_act_list_find f ((i_assign t' c' (o_internal e))::ls) s r ta l1 = str_act_list_find f ls s r ta l1)
 /\
 (str_act_list_find f ((i_assign t' c' (o_load r' ta'))::ls) s r ta l1 = str_act_list_find f ls s r ta l1)
 /\
 (str_act_list_find f ((i_assign t' c' (o_store r' ta' tv'))::ls) s r ta l1 =
   case str_act_list_cond f l1 s t' r' ta' ta of
   | [] =>
     if r' <> r then str_act_list_find f ls s r ta l1
     else i_assign t' c' (o_store r' ta' tv')::str_act_list_find f ls s r ta l1
   | _ => str_act_list_find f ls s r ta l1)
End

Definition str_act_list:
 str_act_list (f:e -> (t |-> v) -> v option) ((State_st_list l s fs cs):State_list) (t:t) : i list =
  case addr_of_list l t of
  | NONE => []
  | SOME (r,ta) =>
    let l' = str_may_list f (State_st_list l s fs cs) t in
    str_act_list_find f l' s r ta l'
End

Definition bound_names_program_list:
 bound_names_program_list (il:i list) : t list =
  MAP bound_name_instr il
End

Definition state_program_list:
 state_program_list (State_st_list il s0 cl fl) = il
End

Definition append_program_state_list:
 append_program_state_list (State_st_list il s0 cl fl) il' =
  State_st_list (il ++ il') s0 cl fl
End

Definition sem_instr_exe:
 (sem_instr_exe (f: e -> (t |-> v) -> v option) ((i_assign t c (o_internal e)):i)
  ((State_st_list l s cs fs):State_list) : (v # obs) option =
  case f e s of
  | NONE => NONE
  | SOME v => SOME (v, obs_internal))
 /\
 (sem_instr_exe f (i_assign t c (o_store r ta tv)) (State_st_list l s cs fs) =
  case FLOOKUP s tv of
  | NONE => NONE
  | SOME v =>
    (case FLOOKUP s ta of
     | NONE => NONE
     | SOME a => SOME (v, obs_internal)))
 /\
 (sem_instr_exe f (i_assign t c (o_load res_MEM ta)) (State_st_list l s cs fs) =
  case bound_names_program_list (str_act_list f (State_st_list l s cs fs) t) of
  | [] => NONE
  | [ts] =>
    (case FLOOKUP s ta of
     | NONE => NONE
     | SOME a =>
       (case FLOOKUP s ts of
        | NONE => NONE
        | SOME v =>
          if MEM ts cs then
            SOME (v, obs_dl a)
          else
            SOME (v, obs_internal)))
  | _::_::_ => NONE)
 /\
 (sem_instr_exe f (i_assign t c (o_load r ta)) (State_st_list l s cs fs) =
  case bound_names_program_list (str_act_list f (State_st_list l s cs fs) t) of
  | [] => NONE
  | [ts] =>
    (case FLOOKUP s ta of
     | NONE => NONE
     | SOME a =>
       (case FLOOKUP s ts of
        | NONE => NONE
        | SOME v => SOME (v, obs_internal)))
  | _::_::_ => NONE)
End

Definition name_le:
 name_le (t1:t) (t2:t) = (t1 <= t2)
End

Definition bound_name_instr_le:
 bound_name_instr_le i1 i2 = (name_le (bound_name_instr i1) (bound_name_instr i2))
End

Definition max_bound_name_list:
 max_bound_name_list (l:i list) =
  FOLDL (\t i. if name_le t (bound_name_instr i) then (bound_name_instr i) else t) 0 l
End

Definition max_name_in_state_list:
 max_name_in_state_list (State_st_list il s0 cl fl) =
  (max_bound_name_list il)
End

Definition Completed_list:
 (Completed_list f_sem (State_st_list l s c' fs) (i_assign t c (o_store res_MEM t1 t2)) =
  (f_sem c s = SOME val_false \/ MEM t c'))
 /\
 (Completed_list f_sem (State_st_list l s c' fs) (i_assign t c (o_store res_PC t1 t2)) =
  (f_sem c s = SOME val_false \/ MEM t fs))
 /\
 (Completed_list f_sem (State_st_list l s c' fs) (i_assign t c op) =
  (f_sem c s = SOME val_false \/ FLOOKUP s t <> NONE))
End

Definition Completed_list_up_to:
 Completed_list_up_to f (State_st_list l s cs fs) k =
  !i. MEM i (TAKE k l) ==> Completed_list f (State_st_list l s cs fs) i
End

Definition names_e_list:
 (names_e_list (e_val v) = [])
 /\
 (names_e_list (e_name t) = [t])
 /\
 (names_e_list (e_and e1 e2) = names_e_list e1 ++ names_e_list e2)
 /\
 (names_e_list (e_or e1 e2) = names_e_list e1 ++ names_e_list e2)
 /\
 (names_e_list (e_xor e1 e2) = names_e_list e1 ++ names_e_list e2)
 /\
 (names_e_list (e_add e1 e2) = names_e_list e1 ++ names_e_list e2)
 /\
 (names_e_list (e_sub e1 e2) = names_e_list e1 ++ names_e_list e2)
 /\
 (names_e_list (e_mul e1 e2) = names_e_list e1 ++ names_e_list e2)
 /\
 (names_e_list (e_div e1 e2) = names_e_list e1 ++ names_e_list e2)
 /\
 (names_e_list (e_sdiv e1 e2) = names_e_list e1 ++ names_e_list e2)
 /\
 (names_e_list (e_mod e1 e2) = names_e_list e1 ++ names_e_list e2)
 /\
 (names_e_list (e_smod e1 e2) = names_e_list e1 ++ names_e_list e2)
 /\
 (names_e_list (e_lsl e1 e2) = names_e_list e1 ++ names_e_list e2)
 /\
 (names_e_list (e_lsr e1 e2) = names_e_list e1 ++ names_e_list e2)
 /\
 (names_e_list (e_asr e1 e2) = names_e_list e1 ++ names_e_list e2)
 /\
 (names_e_list (e_eq e1 e2) = names_e_list e1 ++ names_e_list e2)
 /\
 (names_e_list (e_neq e1 e2) = names_e_list e1 ++ names_e_list e2)
 /\
 (names_e_list (e_lt e1 e2) = names_e_list e1 ++ names_e_list e2)
 /\
 (names_e_list (e_slt e1 e2) = names_e_list e1 ++ names_e_list e2)
 /\
 (names_e_list (e_le e1 e2) = names_e_list e1 ++ names_e_list e2)
 /\
 (names_e_list (e_sle e1 e2) = names_e_list e1 ++ names_e_list e2)
 /\
 (names_e_list (e_comp e) = names_e_list e)
 /\
 (names_e_list (e_not e) = names_e_list e)
End

Definition sort_instr_bound_name:
 sort_bound_name_instr = QSORT bound_name_instr_le
End

Definition translate_val_set_to_list:
 translate_val_set_to_list v t = SET_TO_LIST (translate_val v t)
End

Definition translate_val_list:
 translate_val_list = @(f : v -> t -> i list). !(v:v) (t:t).
  (LIST_TO_SET (f v t) = translate_val v t)
  /\
  (NO_DUPLICATES (f v t))
End

Definition translate_val_list_SORTED:
 translate_val_list_SORTED =
  (!v t. SORTED bound_name_instr_le (translate_val_list v t))
End

(* additional executable funcions for str_may/act_addr and str_may/act_opt
 * str_may/act_addr: the input has the value of address ta.
 * str_may/act_opt: the input has the value option of address ta (NONE / SOME a).
 *)
Definition str_may_addr_list_find:
 (str_may_addr_list_find (f:e -> (t |-> v) -> v option) ([]:i list) (s:(t |-> v)) (t:t) (r:res) (vop:v option): i list = [])
 /\
 (str_may_addr_list_find f ((i_assign t' c' (o_internal e))::ls) s t r vop = str_may_addr_list_find f ls s t r vop)
 /\
 (str_may_addr_list_find f ((i_assign t' c' (o_load r' ta'))::ls) s t r vop = str_may_addr_list_find f ls s t r vop)
 /\
 (str_may_addr_list_find f ((i_assign t' c' (o_store r' ta' tv'))::ls) s t r vop =
  case FLOOKUP s ta' of
  | NONE =>
    if (t' >= t) \/ (r' <> r) then
      str_may_addr_list_find f ls s t r vop
    else
      (case f c' s of
      | NONE => i_assign t' c' (o_store r' ta' tv')::str_may_addr_list_find f ls s t r vop
      | SOME v =>
        if v <> val_false then
          i_assign t' c' (o_store r' ta' tv')::str_may_addr_list_find f ls s t r vop
        else
          str_may_addr_list_find f ls s t r vop)
   | SOME v1 =>
     case vop of
     | NONE =>
       if (t' >= t) \/ (r' <> r) then
         str_may_addr_list_find f ls s t r vop
       else
         (case f c' s of
         | NONE => i_assign t' c' (o_store r' ta' tv')::str_may_addr_list_find f ls s t r vop
         | SOME v =>
           if v <> val_false then
             i_assign t' c' (o_store r' ta' tv')::str_may_addr_list_find f ls s t r vop
           else
             str_may_addr_list_find f ls s t r vop)
     | SOME v2 =>
       if (t' >= t) \/ (r' <> r) \/ (v1 <> v2) then
         str_may_addr_list_find f ls s t r vop
       else
         (case f c' s of
         | NONE => i_assign t' c' (o_store r' ta' tv')::str_may_addr_list_find f ls s t r vop
         | SOME v =>
           if v <> val_false then
             i_assign t' c' (o_store r' ta' tv')::str_may_addr_list_find f ls s t r vop
           else
             str_may_addr_list_find f ls s t r vop))
End

Definition str_may_addr_list:
 str_may_addr_list (f: e -> (t |-> v) -> v option) ((State_st_list l s cs fs):State_list) (t:t) (r:res) (a:v): i list =
   str_may_addr_list_find f l s t r (SOME a)
End

Definition str_may_opt_list:
 str_may_opt_list (f:e -> (t |-> v) -> v option) ((State_st_list l s cs fs):State_list) (t:t) (r:res) (aop:v option): i list =
   str_may_addr_list_find f l s t r aop
End

Definition str_act_addr_list_cond:
  (str_act_addr_list_cond (f:e -> (t |-> v) -> v option) ([]:i list) (s:(t |-> v)) (t':t) (r':res) (ta':t) (aop:v option): i list = [])
 /\
 (str_act_addr_list_cond f ((i_assign t'' c'' (o_internal e))::ls) s t' r' ta' aop = str_act_addr_list_cond f ls s t' r' ta' aop)
 /\
 (str_act_addr_list_cond f ((i_assign t'' c'' (o_load r'' ta''))::ls) s t' r' ta' aop = str_act_addr_list_cond f ls s t' r' ta' aop)
 /\
 (str_act_addr_list_cond f ((i_assign t'' c'' (o_store r'' ta'' tv''))::ls) s t' r' ta' aop =
  case f c'' s of
  | NONE => str_act_addr_list_cond f ls s t' r' ta' aop
  | SOME fv =>
    case FLOOKUP s ta''  of
    | SOME v1 =>
      (case FLOOKUP s ta' of
       | SOME v2 =>
         (case aop of
          | SOME v3 =>
            if (t'' > t') /\ (r'' = r') /\ (fv <> val_false) /\ (v1 = v3) then
              (i_assign t'' c'' (o_store r'' ta'' tv''))::(str_act_addr_list_cond f ls s t' r' ta' aop)
            else
              str_act_addr_list_cond f ls s t' r' ta' aop
          | NONE =>
            if (t'' > t') /\ (r'' = r') /\ (fv <> val_false) /\ (v1 = v2) then
              (i_assign t'' c'' (o_store r'' ta'' tv''))::(str_act_addr_list_cond f ls s t' r' ta' aop)
            else
              str_act_addr_list_cond f ls s t' r' ta' aop)
       | NONE =>
         (case aop of
          | SOME v3 =>
              if (t'' > t') /\ (r'' = r') /\ (fv <> val_false) /\ (v1 = v3) then
                (i_assign t'' c'' (o_store r'' ta'' tv''))::(str_act_addr_list_cond f ls s t' r' ta' aop)
              else
                str_act_addr_list_cond f ls s t' r' ta' aop
          | NONE => str_act_addr_list_cond f ls s t' r' ta' aop))
    | NONE => str_act_addr_list_cond f ls s t' r' ta' aop)
End

Definition str_act_addr_list_find:
 (str_act_addr_list_find (f:e -> (t |-> v) -> v option) ([]:i list) (s:(t |-> v)) (r:res) (aop:v option) (l1:i list): i list = [])
 /\
 (str_act_addr_list_find f ((i_assign t' c' (o_internal e))::ls) s r aop l1 = str_act_addr_list_find f ls s r aop l1)
 /\
 (str_act_addr_list_find f ((i_assign t' c' (o_load r' ta'))::ls) s r aop l1 = str_act_addr_list_find f ls s r aop l1)
 /\
 (str_act_addr_list_find f ((i_assign t' c' (o_store r' ta' tv'))::ls) s r aop l1 =
   case str_act_addr_list_cond f l1 s t' r' ta' aop of
   | [] =>
     if r' <> r then str_act_addr_list_find f ls s r aop l1
     else i_assign t' c' (o_store r' ta' tv')::str_act_addr_list_find f ls s r aop l1
   | _ => str_act_addr_list_find f ls s r aop l1)
End

Definition str_act_addr_list:
 str_act_addr_list (f:e -> (t |-> v) -> v option) ((State_st_list l s fs cs):State_list) (t:t) (r:res) (a:v) : i list =
    let l' = str_may_addr_list f (State_st_list l s fs cs) t r a in
    str_act_addr_list_find f l' s r (SOME a) l'
End

Definition str_act_opt_list:
 str_act_opt_list (f:e -> (t |-> v) -> v option) ((State_st_list l s fs cs):State_list) (t:t) (r:res) (aop:v option) : i list =
    let l' = str_may_opt_list f (State_st_list l s fs cs) t r aop in
    str_act_addr_list_find f l' s r aop l'
End

(* --------------------------------------- *)
(* Properties of general helper functions  *)
(* --------------------------------------- *)

Theorem OPTION_MAP_INDEX_FIND_eq[local]:
 !P l n m. OPTION_MAP SND (INDEX_FIND n P l) = OPTION_MAP SND (INDEX_FIND m P l)
Proof
 strip_tac >> Induct_on `l` >> rw [OPTION_MAP_DEF,INDEX_FIND_def]
QED

Theorem FIND_instr_eq_FIND[local]:
 !il t. FIND_instr t il = FIND (\i. bound_name_instr i = t) il
Proof
 Induct_on `il` >>
 rw [FIND_instr,FIND_def,OPTION_MAP_DEF,INDEX_FIND_def,OPTION_MAP_INDEX_FIND_eq]
QED

Theorem FIND_instr_eq_NONE:
  !t l. FIND_instr t l = NONE <=> ~MEM t (MAP bound_name_instr l)
Proof
 Induct_on `l` >> rw [FIND_instr]
QED

Theorem FIND_instr_eq_SOME:
 !t l i. FIND_instr t l = SOME i ==> bound_name_instr i = t /\ MEM i l
Proof
 Induct_on `l` >> rw [FIND_instr] >> METIS_TAC []
QED

(* Cannot eval NO_DUPLICATES since cannot eval UNIQUE. *)

Theorem MEM_SINGLE[local]:
  !l a b. (l = [a]) /\ (MEM b l) ==> b = a
Proof
  SIMP_TAC list_ss []
QED

Theorem NO_DUPLICATES_ALT_bound_name_instr:
 !l i i'. NO_DUPLICATES_ALT l ==>
  MEM i l ==> MEM i' l ==>
  bound_name_instr i = bound_name_instr i' ==>
  i = i'
Proof
 rw [NO_DUPLICATES_ALT] >>
 `UNIQUE (bound_name_instr i) (MAP bound_name_instr l)` by METIS_TAC [MEM_MAP,NO_DUPLICATE] >>
 `UNIQUE (bound_name_instr i') (MAP bound_name_instr l)` by METIS_TAC [MEM_MAP,NO_DUPLICATE] >>
 `MEM (bound_name_instr i') (MAP bound_name_instr l)` by METIS_TAC [MEM_MAP] >>
 `MEM (bound_name_instr i) (MAP bound_name_instr l)` by METIS_TAC [MEM_MAP] >>
 fs [UNIQUE_FILTER,FILTER_MAP] >>
 `[x0] = [x0']` by METIS_TAC [] >> rw [] >>
 `MEM i' (FILTER ($= (bound_name_instr i') o bound_name_instr) l)` by rw [MEM_FILTER] >>
 `MEM i (FILTER ($= (bound_name_instr i) o bound_name_instr) l)` by rw [MEM_FILTER] >>
 METIS_TAC [MEM_SINGLE]
QED

Theorem NO_DUPLICATES_bound_name_instr:
 !l i i'. NO_DUPLICATES l ==>
          MEM i l ==> MEM i' l ==>
          bound_name_instr i = bound_name_instr i' ==>
          i = i'
Proof
  rw [NO_DUPLICATES] >>
  `MEM (bound_name_instr i) (MAP bound_name_instr l)` by METIS_TAC [MEM_MAP] >>
  `MEM (bound_name_instr i') (MAP bound_name_instr l)` by METIS_TAC [MEM_MAP] >>
  `FILTER ($= (bound_name_instr i)) (MAP bound_name_instr l) = [bound_name_instr i]` by fs [ALL_DISTINCT_FILTER] >>
  `FILTER ($= (bound_name_instr i')) (MAP bound_name_instr l) = [bound_name_instr i']` by fs [ALL_DISTINCT_FILTER] >>
  fs [FILTER_MAP] >>
  `[x0] = [x0']` by METIS_TAC [] >> rw [] >>
  `MEM i' (FILTER ($= (bound_name_instr i') o bound_name_instr) l)` by rw [MEM_FILTER] >>
  `MEM i (FILTER ($= (bound_name_instr i) o bound_name_instr) l)` by rw [MEM_FILTER] >>
  METIS_TAC [MEM_SINGLE]
QED

Theorem UNIQUE_FILTER_instr:
  !l t. UNIQUE t (MAP (bound_name_instr) l) ==>
    ?c mop. FILTER_instr t l = [i_assign t c mop]
Proof
  GEN_TAC >>
  rw [FILTER_instr] >>
  `FILTER ($= t) (MAP bound_name_instr l) = [t]` by METIS_TAC [UNIQUE_FILTER] >>
  FULL_SIMP_TAC list_ss [FILTER_MAP] >>
  Cases_on `x0` >>
  EXISTS_TAC ``e:e`` >>
  EXISTS_TAC ``o':op`` >>
  rw [bound_name_instr]
QED

Theorem FILTER_instr_MEM:
  !l t i. FILTER_instr t l = [i] ==> MEM i l
Proof
  rw [FILTER_instr] >>
  `MEM i (FILTER ($= t o bound_name_instr) l)` by rw [] >>
  fs [MEM_FILTER]
QED

Theorem not_MEM_notin:
  !l t. ~MEM t (MAP bound_name_instr l) ==>
     (!i. i IN (LIST_TO_SET l) ==> bound_name_instr i <> t)
Proof
  rw [MEM_MAP] >> METIS_TAC []
QED

Theorem not_MEM_FILTER_t_NIL:
 !l t. ~MEM t (MAP bound_name_instr l) ==>
  FILTER_instr t l = []
Proof
  rw [FILTER_instr, MEM_MAP] >>
  `!y. MEM y l ==> bound_name_instr y <> t` by METIS_TAC [] >>
  `!y. MEM y l ==> ~(($= t o bound_name_instr) y)` by fs [] >>
  METIS_TAC [NULL_FILTER, NULL_EQ]
QED

(* theorems for NONCONT_SUBLIST *)
Theorem NONCONT_SUBLIST_MEM:
  !l l' x.
    NONCONT_SUBLIST l l' ==>
    MEM x l' ==>
    MEM x l
Proof
  Induct_on `l'` >>
  Induct_on `l` >>
  rw [NONCONT_SUBLIST] >>
  fs [] >>
  METIS_TAC []
QED

Theorem NONCONT_SUBLIST_APPEND:
  !l1 l2 l.
    NONCONT_SUBLIST l (l1 ++ l2) ==>
    (NONCONT_SUBLIST l l1) /\ (NONCONT_SUBLIST l l2)
Proof
  Induct_on `l2` >>
  Induct_on `l1` >>
  Induct_on `l` >>
  rw [NONCONT_SUBLIST] >>
  `h'::(l1++h''::l2) = h'::l1 ++ h''::l2` by fs [] >>
  METIS_TAC []
QED

Theorem NONCONT_SUBLIST_MEM_single:
  !l x.
    MEM x l ==>
    NONCONT_SUBLIST l [x]
Proof
  rw [MEM_SPLIT] >>
  Induct_on `l1` >>
  rw [NONCONT_SUBLIST]
QED

Theorem NONCONT_SUBLIST_not_MEM[local]:
  !l1 l2 h t.
    NONCONT_SUBLIST (l1 ++ l2) (h::t) ==>
    ~MEM h l1 ==>
    NONCONT_SUBLIST l2 (h::t)
Proof
  rw [] >>
  Induct_on `l1` >>
  rw [NONCONT_SUBLIST] >>
  fs []
QED

Theorem NONCONT_SUBLIST_two_x[local]:
  !l1 l2 l1' l2' x.
    NONCONT_SUBLIST (l1 ++ [x] ++ l2) (x::l1' ++ x::l2') ==>
    (NONCONT_SUBLIST l1 [x]) \/ (NONCONT_SUBLIST l2 [x])
Proof
  REVERSE (Cases_on `l1` >> rw [NONCONT_SUBLIST]) >-
  (Cases_on `NONCONT_SUBLIST t [x]` >> rw [] >>
   `~ MEM x t` by METIS_TAC [NONCONT_SUBLIST_MEM_single] >>
   `t ++ [x] ++ l2 = t ++ ([x] ++ l2)` by rw [] >>
   `NONCONT_SUBLIST ([x] ++ l2) (x::(l1' ++ x::l2'))` by METIS_TAC [NONCONT_SUBLIST_not_MEM] >>
   fs [NONCONT_SUBLIST] >>
   `x::(l1' ++ x::l2') = (x::l1') ++ (x::l2')` by rw [] >>
   `NONCONT_SUBLIST l2 (x::l2')` by METIS_TAC [NONCONT_SUBLIST_APPEND] >>
   `x::l2' = [x] ++ l2'` by rw [] >>
   METIS_TAC [NONCONT_SUBLIST_APPEND]) >>
  `x::(l1' ++ x::l2') = (x::l1') ++ (x::l2')` by rw [] >>
  `NONCONT_SUBLIST l2 (x::l2')` by METIS_TAC [NONCONT_SUBLIST_APPEND] >>
  `x::l2' = [x] ++ l2'` by rw [] >>
  METIS_TAC [NONCONT_SUBLIST_APPEND]
QED

Theorem NONCONT_SUBLIST_FILTER_MEM:
  !l l' x P.
    NONCONT_SUBLIST l l' ==>
    MEM x l' ==>
    FILTER P l = [x] ==>
    FILTER P l' = [x]
Proof
  rw [FILTER_EQ_CONS, FILTER_EQ_NIL, EVERY_MEM] >>
  `?l1' l2'. l' = l1' ++ [x] ++ l2' /\ ~ (MEM x l1')` by METIS_TAC [MEM_SPLIT_APPEND_first] >>
  Q.EXISTS_TAC `l1'` >>
  Q.EXISTS_TAC `l2'` >>
  rw [] >>
  `MEM x' (l1 ++ [x] ++ l2)` by METIS_TAC [MEM_APPEND, NONCONT_SUBLIST_MEM] >>
  fs [MEM_APPEND] >-
   (METIS_TAC []) >>
  `?l1'' l2''. l2' = l1'' ++ x::l2''` by METIS_TAC [MEM_SPLIT] >>
  rw [] >>
  `l1' ++ [x] ++ (l1''++x::l2'') = l1' ++ (x::l1'' ++ x::l2'')` by rw [] >>
  `NONCONT_SUBLIST (l1 ++ [x] ++ l2) (x::l1'' ++ x::l2'')` by METIS_TAC [NONCONT_SUBLIST_APPEND] >>
  `NONCONT_SUBLIST l1 [x] \/ NONCONT_SUBLIST l2 [x]` by METIS_TAC [NONCONT_SUBLIST_two_x] >>
  `MEM x [x]` by rw [] >>
  METIS_TAC [NONCONT_SUBLIST_MEM]
QED

Theorem NO_DUPLICATES_ALT_NONCONT_SUBLIST:
  !l l'.
    NO_DUPLICATES_ALT l ==>
    NONCONT_SUBLIST l l' ==>
    NO_DUPLICATES_ALT l'
Proof
  rw [NO_DUPLICATES_ALT, NO_DUPLICATE, MEM_MAP] >>
  `MEM y l` by METIS_TAC [NONCONT_SUBLIST_MEM] >>
  `?t. t = bound_name_instr y` by rw [bound_name_instr] >>
  `UNIQUE t (MAP bound_name_instr l)` by METIS_TAC [] >>
  fs [UNIQUE_FILTER, FILTER_MAP] >>
  `MEM y (FILTER ($= (bound_name_instr x0) o bound_name_instr) l)` by fs [MEM_FILTER] >>
  `x0 = y` by METIS_TAC [MEM_SINGLE] >>
   METIS_TAC [NONCONT_SUBLIST_FILTER_MEM]
QED

Theorem NO_DUPLICATES_NONCONT_SUBLIST:
  !l l'.
    NO_DUPLICATES l ==>
    NONCONT_SUBLIST l l' ==>
    NO_DUPLICATES l'
Proof
  rw [NO_DUPLICATES,ALL_DISTINCT_FILTER,MEM_MAP] >>
  `MEM y l` by METIS_TAC [NONCONT_SUBLIST_MEM] >>
  `?t. t = bound_name_instr y` by rw [bound_name_instr] >>
  `FILTER ($=t) (MAP bound_name_instr l) = [t]` by METIS_TAC [] >>
  fs [FILTER_MAP] >>
  `MEM y (FILTER ($= (bound_name_instr x0) o bound_name_instr) l)` by fs [MEM_FILTER] >>
  `x0 = y` by METIS_TAC [MEM_SINGLE] >>
   METIS_TAC [NONCONT_SUBLIST_FILTER_MEM]
QED

Theorem NONCONT_SUBLIST_h_t:
  !h t l.
    NONCONT_SUBLIST t l ==>
    NONCONT_SUBLIST (h::t) l
Proof
  Cases_on `l` >>
  rw [NONCONT_SUBLIST]
QED

Theorem NONCONT_SUBLIST_third:
  !l1 l2 l3.
    NONCONT_SUBLIST l1 l2 ==>
    NONCONT_SUBLIST l2 l3 ==>
    NONCONT_SUBLIST l1 l3
Proof
  Induct_on `l3` >>
  Induct_on `l2` >>
  Induct_on `l1` >>
  fs [NONCONT_SUBLIST] >>
  rw [] >>
  METIS_TAC []
QED

Theorem NO_DUPLICATES_ALT_FIND_instr:
  !l t i.
    (NO_DUPLICATES_ALT l) ==>
    (MEM i l) ==>
    (bound_name_instr i = t) ==>
    FIND_instr t l = SOME i
Proof
 rw [] >>
 Cases_on `FIND_instr (bound_name_instr i) l` >-
 METIS_TAC [FIND_instr_eq_NONE,MEM_MAP,NO_DUPLICATES_ALT_bound_name_instr] >>
 METIS_TAC [FIND_instr_eq_SOME,NO_DUPLICATES_ALT_bound_name_instr]
QED

Theorem UNIQUE_APP_MEM:
 !l l' a. UNIQUE a (l ++ l') ==>
          ~MEM a l' ==>
          MEM a l
Proof
 Induct_on `l` >> rw [UNIQUE_DEF] >> fs [] >>
 Cases_on `a = h` >> rw [] >>
 Cases_on `L1` >> fs [] >> rw [] >>
 `UNIQUE a (l ++ l')` by METIS_TAC [UNIQUE_DEF] >>
 METIS_TAC []
QED

Theorem UNIQUE_MEM_APP:
 !l l' a. UNIQUE a (l ++ l') ==>
 MEM a l ==>
 ~MEM a l'
Proof
 Induct_on `l` >> rw [UNIQUE_DEF] >> fs [] >-
  (Cases_on `L1` >> fs [] >> rw [] >>
   strip_tac >>
   METIS_TAC [MEM_APPEND]) >>
 Cases_on `a = h` >> rw [] >-
  (Cases_on `L1` >> fs [] >> rw [] >>
   METIS_TAC [MEM_APPEND]) >>
 Cases_on `L1` >> fs [] >> rw [] >>
 `UNIQUE a (l ++ l')` by METIS_TAC [UNIQUE_DEF] >>
 METIS_TAC []
QED

Theorem transitive_name_le:
 transitive name_le
Proof
 rw [transitive_def,name_le]
QED

Theorem antisymmetric_name_le:
 antisymmetric name_le
Proof
 rw [antisymmetric_def,name_le]
QED

Theorem total_name_le:
 total name_le
Proof
 rw [total_def,name_le]
QED

Theorem transitive_bound_name_instr_le:
 transitive bound_name_instr_le
Proof
 rw [transitive_def,bound_name_instr_le] >>
 METIS_TAC [transitive_name_le,transitive_def]
QED

Theorem total_bound_name_instr_le:
 total bound_name_instr_le
Proof
 rw [total_def,bound_name_instr_le] >> METIS_TAC [total_name_le,total_def]
QED

Theorem sort_bound_name_instr_SORTED:
 !l. SORTED bound_name_instr_le (sort_bound_name_instr l)
Proof
 rw [
  sort_instr_bound_name,
  QSORT_SORTED,
  transitive_bound_name_instr_le,
  total_bound_name_instr_le
 ]
QED

Theorem ALL_DISTINCT_MAP_NO_DUPLICATES_ALT:
 !l. ALL_DISTINCT (MAP bound_name_instr l) <=> NO_DUPLICATES_ALT l
Proof
 strip_tac >> EQ_TAC >-
  (Induct_on `l` >> rw [ALL_DISTINCT,NO_DUPLICATES_ALT,NO_DUPLICATE] >-
    (rw [UNIQUE_DEF] >>
     Q.EXISTS_TAC `[]` >>
     Q.EXISTS_TAC `MAP bound_name_instr l` >>
     fs []) >>
   Cases_on `h` >> rename1 `i_assign t' c mop` >>
   fs [bound_name_instr] >>
   Cases_on `t = t'` >> rw [] >- METIS_TAC [] >>
   fs [NO_DUPLICATES_ALT,NO_DUPLICATE] >>
   `UNIQUE t (MAP bound_name_instr l)` by METIS_TAC [] >>
   `?l1 l2. MAP bound_name_instr l = l1 ++ t::l2` by METIS_TAC [MEM_SPLIT] >>
   rw [UNIQUE_DEF] >>
   Q.EXISTS_TAC `t'::l1` >>
   Q.EXISTS_TAC `l2` >>
   fs [] >>
   `l1 ++ [t] ++ l2 = l1 ++ t::l2` by fs [] >>
   `MEM t (t::l2)` by rw [] >>
   `MEM t (l1 ++ [t])` by rw [] >>
   METIS_TAC [UNIQUE_MEM_APP]) >>
 Induct_on `l` >> rw [ALL_DISTINCT,NO_DUPLICATES_ALT,NO_DUPLICATE] >-
  (Cases_on `h` >> rename1 `i_assign t c mop` >>
   fs [bound_name_instr] >>
   strip_tac >>
   `UNIQUE t (t::MAP bound_name_instr l)` by METIS_TAC [] >>
   fs [UNIQUE_DEF] >>
   Cases_on `L1` >> fs [] >> rw [] >>
   METIS_TAC []) >>
 Cases_on `h` >> rename1 `i_assign t c mop` >>
 fs [bound_name_instr] >>
 `UNIQUE t (t::MAP bound_name_instr l)` by METIS_TAC [] >>
 sg `~MEM t (MAP bound_name_instr l)` >-
  (fs [UNIQUE_DEF] >>
   Cases_on `L1` >> fs [] >> rw []) >>
 sg `!t'. MEM t' (MAP bound_name_instr l) ==> UNIQUE t' (MAP bound_name_instr l)` >-
  (rw [] >>
   `UNIQUE t' (t::MAP bound_name_instr l)` by METIS_TAC [] >>
   Cases_on `t = t'` >> fs [] >>
   fs [UNIQUE_DEF] >>
   Cases_on `L1'` >> fs [] >> rw [] >>
   METIS_TAC []) >>
 METIS_TAC [NO_DUPLICATES_ALT,NO_DUPLICATE]
QED

Theorem NO_DUPLICATES_EQ_NO_DUPLICATES_ALT:
  !l. NO_DUPLICATES l <=> NO_DUPLICATES_ALT l
Proof
  rw [NO_DUPLICATES,ALL_DISTINCT_MAP_NO_DUPLICATES_ALT]
QED

Theorem MEM_MAP_bound_name_instr:
 !l t c mop.
  MEM_bound_name_instr_unique (i_assign t c mop::l) ==>
  MEM t (MAP bound_name_instr l) ==>
  MEM (i_assign t c mop) l
Proof
 Induct_on `l` >> rw [] >-
  (DISJ1_TAC >>
   Cases_on `h` >> rw [bound_name_instr] >>
   `i_assign n c mop = i_assign n e o'` suffices_by rw [bound_name_instr] >>
   `MEM (i_assign n c mop) (i_assign n c mop::i_assign n e o'::l)` by rw [] >>
   `MEM (i_assign n e o') (i_assign n c mop::i_assign n e o'::l)` by rw [] >>
   `bound_name_instr (i_assign n c mop) = bound_name_instr (i_assign n e o')`
    by rw [bound_name_instr] >>
   `MEM_bound_name_instr_unique (i_assign n c mop::i_assign n e o'::l)`
    by fs [bound_name_instr] >>
   METIS_TAC [MEM_bound_name_instr_unique]) >>
 Cases_on `h` >>
 sg `MEM_bound_name_instr_unique (i_assign t c mop::l)` >-
  (`MEM (i_assign t c mop) (i_assign t c mop::i_assign n e o'::l)` by rw [] >>
   `!i. MEM i l ==> MEM i (i_assign t c mop::i_assign n e o'::l)` by rw [] >>
   `!i. MEM i (i_assign t c mop::l) ==> i = i_assign t c mop \/ MEM i l` by rw [] >>
   METIS_TAC [MEM_bound_name_instr_unique]) >>
 METIS_TAC []
QED

Theorem MEM_MAP_bound_name_instr_unfolded[local]:
 !l t c mop.
 (!i i'. i = i_assign t c mop \/ MEM i l ==>
   i' = i_assign t c mop \/ MEM i' l ==>
   bound_name_instr i = bound_name_instr i' ==>
   i = i') ==>
  MEM t (MAP bound_name_instr l) ==>
  MEM (i_assign t c mop) l
Proof
 rw [] >>
 sg `MEM_bound_name_instr_unique (i_assign t c mop::l)` >-
  (rw [MEM_bound_name_instr_unique] >>
   METIS_TAC [bound_name_instr]) >>
 METIS_TAC [MEM_MAP_bound_name_instr]
QED

Theorem ALL_DISTINCT_NO_DUPLICATES_ALT:
 !l. ALL_DISTINCT l ==>
  (!i i'. MEM i l ==> MEM i' l ==>
   bound_name_instr i = bound_name_instr i' ==>
   i = i') ==>
  NO_DUPLICATES_ALT l
Proof
 Induct_on `l` >> rw [ALL_DISTINCT,NO_DUPLICATES_ALT,NO_DUPLICATE] >-
  (Cases_on `h` >> rename1 `i_assign t c mop` >>
   fs [bound_name_instr] >>
   rw [UNIQUE_DEF] >>
   Q.EXISTS_TAC `[]` >>
   Q.EXISTS_TAC `MAP bound_name_instr l` >>
   rw [] >>
   strip_tac >>
   `MEM (i_assign t c mop) l` suffices_by METIS_TAC [] >>
   METIS_TAC [MEM_MAP_bound_name_instr_unfolded]) >>
 `NO_DUPLICATES_ALT l` by METIS_TAC [] >>
 Cases_on `h` >> rename1 `i_assign t' c mop` >>
 fs [bound_name_instr] >>
 fs [NO_DUPLICATES_ALT,NO_DUPLICATE] >>
 `UNIQUE t (MAP bound_name_instr l)` by METIS_TAC [] >>
 Cases_on `t = t'` >-
  (rw [] >>
   METIS_TAC [MEM_MAP,bound_name_instr]) >>
 `?l1 l2. MAP bound_name_instr l = l1 ++ t::l2` by METIS_TAC [MEM_SPLIT] >>
 rw [UNIQUE_DEF] >>
 Q.EXISTS_TAC `t'::l1` >>
 Q.EXISTS_TAC `l2` >>
 fs [] >> rw [] >-
  (`l1 ++ [t] ++ l2 = l1 ++ t::l2` by fs [] >>
   `MEM t (t::l2)` by rw [] >>
   METIS_TAC [UNIQUE_MEM_APP]) >>
 `MEM t (l1 ++ [t])` by rw [] >>
 strip_tac >>
 METIS_TAC [UNIQUE_MEM_APP]
QED

Theorem ALL_DISTINCT_MAP_APPEND:
 !l1 l2. ALL_DISTINCT (MAP bound_name_instr l1) ==> ALL_DISTINCT (MAP bound_name_instr l2) ==>
  (!i i'. MEM i l1 ==> MEM i' l2 ==> bound_name_instr i <> bound_name_instr i') ==>
  ALL_DISTINCT (MAP bound_name_instr (l1 ++ l2))
Proof
 Induct_on `l1` >> rw [ALL_DISTINCT] >-
  (Cases_on `h` >> rename1 `i_assign t c mop` >>
   fs [bound_name_instr] >>
   strip_tac >>
   `?i. MEM i l2 /\ bound_name_instr i = t` by METIS_TAC [MEM_MAP] >>
   METIS_TAC [bound_name_instr]) >>
 Cases_on `h` >> rename1 `i_assign t c mop` >>
 fs [bound_name_instr]
QED

Theorem NO_DUPLICATES_APPEND:
 !l1 l2. NO_DUPLICATES l1 ==> NO_DUPLICATES l2 ==>
 (!i i'. MEM i l1 ==> MEM i' l2 ==> bound_name_instr i <> bound_name_instr i') ==>
 NO_DUPLICATES (l1 ++ l2)
Proof
 METIS_TAC [NO_DUPLICATES,ALL_DISTINCT_MAP_APPEND]
QED

(* --------------------------------------- *)
(* Properties of semantic helper functions *)
(* --------------------------------------- *)

Theorem NO_DUPLICATES_translate_val_set_to_list:
 !v t. NO_DUPLICATES (translate_val_set_to_list v t)
Proof
 rw [translate_val_set_to_list] >>
 `FINITE (translate_val v t)` by METIS_TAC [translate_val_correct] >>
 `ALL_DISTINCT (SET_TO_LIST (translate_val v t))`
  by METIS_TAC [ALL_DISTINCT_SET_TO_LIST] >>
 `!i i'. i IN (translate_val v t) ==> i' IN (translate_val v t) ==>
   bound_name_instr i = bound_name_instr i' ==> i = i'`
  by METIS_TAC [translate_val_correct] >>
 `!i i'. MEM i (SET_TO_LIST (translate_val v t)) ==>
   MEM i' (SET_TO_LIST (translate_val v t)) ==>
   bound_name_instr i = bound_name_instr i' ==> i = i'`
  by fs [] >>
 METIS_TAC [ALL_DISTINCT_NO_DUPLICATES_ALT,NO_DUPLICATES_EQ_NO_DUPLICATES_ALT]
QED

Theorem translate_val_list_elim[local]:
 !v t. LIST_TO_SET (translate_val_list v t) = translate_val v t /\
  NO_DUPLICATES (translate_val_list v t)
Proof
 once_rewrite_tac [translate_val_list] >>
 SELECT_ELIM_TAC >> fs [] >>
 Q.EXISTS_TAC `translate_val_set_to_list` >>
 rw [] >-
  (`FINITE (translate_val v t)` by METIS_TAC [translate_val_correct] >>
   rw [translate_val_set_to_list,SET_TO_LIST_INV]) >>
 rw [NO_DUPLICATES_translate_val_set_to_list]
QED

Theorem translate_val_list_correct:
 !v t. LIST_TO_SET (translate_val_list v t) = translate_val v t
Proof
 rw [translate_val_list_elim]
QED

Theorem NO_DUPLICATES_translate_val_list:
 !v t. NO_DUPLICATES (translate_val_list v t)
Proof
 rw [translate_val_list_elim]
QED

Theorem names_e_list_correct:
 !e. LIST_TO_SET (names_e_list e) = names_e e
Proof
 Induct_on `e` >> rw [names_e_list,names_e]
QED

Theorem addr_of_list_correct:
 !l t. NO_DUPLICATES l ==> addr_of_list l t = addr_of (LIST_TO_SET l) t
Proof
 rw [] >>
 `!i i'. i IN (LIST_TO_SET l) ==> i' IN (LIST_TO_SET l) ==>
   bound_name_instr i = bound_name_instr i' ==> i = i'`
  by METIS_TAC [NO_DUPLICATES_bound_name_instr] >>
 Cases_on `MEM t (MAP bound_name_instr l)` >-
  (fs [NO_DUPLICATES] >>
   `UNIQUE t (MAP bound_name_instr l)` by fs [ALL_DISTINCT_FILTER,UNIQUE_FILTER] >>
   rw [addr_of_list] >>
   Cases_on `FIND_instr t l` >> fs [] >- METIS_TAC [FIND_instr_eq_NONE] >>
   Cases_on `x` >> rename1 `i_assign t' c mop` >>
   `t = t' /\ MEM (i_assign t c mop) l` by METIS_TAC [bound_name_instr,FIND_instr_eq_SOME] >> rw [] >>
   `?i. t = bound_name_instr i /\ MEM i l` by METIS_TAC [MEM_MAP] >>
   Cases_on `mop` >> fs [] >| [
    METIS_TAC [addr_of_internal_none],
    METIS_TAC [addr_of_contains_unique_load],
    METIS_TAC [addr_of_contains_unique_store]
   ]) >>
 `FIND_instr t l = NONE` by METIS_TAC [FIND_instr_eq_NONE] >>
 `!i. i IN (LIST_TO_SET l) ==> bound_name_instr i <> t` by METIS_TAC [not_MEM_notin] >>
 rw [addr_of_list] >>
 METIS_TAC [addr_of_no_t_none]
QED

Theorem load_or_store_addr_of_list_non_empty:
  !l t. NO_DUPLICATES l ==>
    ((?c r ta. (i_assign t c (o_load r ta)) IN (LIST_TO_SET l)) \/
    (?c r ta tv. (i_assign t c (o_store r ta tv)) IN (LIST_TO_SET l))) ==>
    addr_of_list l t <> NONE
Proof
 rw [addr_of_list] >> strip_tac >> Cases_on `FIND_instr t l` >> fs [] >| [
  METIS_TAC [FIND_instr_eq_NONE,MEM_MAP,bound_name_instr],
  `bound_name_instr x = t /\ MEM x l` by METIS_TAC [FIND_instr_eq_SOME] >>
  `x = i_assign t c (o_load r ta)`
   by METIS_TAC [NO_DUPLICATES_bound_name_instr,bound_name_instr] >>
  rw [] >> fs [],
  `~MEM t (MAP bound_name_instr l)` by METIS_TAC [FIND_instr_eq_NONE] >>
  METIS_TAC [MEM_MAP,bound_name_instr],
  `bound_name_instr x = t /\ MEM x l` by METIS_TAC [FIND_instr_eq_SOME] >>
  `x = i_assign t c (o_store r ta tv)`
   by METIS_TAC [NO_DUPLICATES_bound_name_instr,bound_name_instr] >>
  rw [] >> fs []
 ]
QED

Theorem addr_of_list_empty_no_load_or_store:
  !l t. NO_DUPLICATES l ==>
    addr_of_list l t = NONE ==>
    ~((?c r ta. (i_assign t c (o_load r ta)) IN (LIST_TO_SET l)) \/
    (?c r ta tv. (i_assign t c (o_store r ta tv)) IN (LIST_TO_SET l)))
Proof
   METIS_TAC [load_or_store_addr_of_list_non_empty]
QED

Theorem str_may_list_find_APPEND:
 !f l1 l2 s t r ta.
  str_may_list_find f (l1 ++ l2) s t r ta =
  (str_may_list_find f l1 s t r ta) ++ (str_may_list_find f l2 s t r ta)
Proof
  strip_tac >>
  Induct_on `l1` >|
  [rw [str_may_list_find],
   Cases_on `h` >>
   Cases_on `o'` >>
   rw [str_may_list_find] >>
   Cases_on `FLOOKUP s n'` >>
   Cases_on `FLOOKUP s ta` >>
   Cases_on `f e s` >>
   rw []]
QED

Theorem str_act_list_find_APPEND:
 !f l1 l2 l s r ta.
  str_act_list_find f (l1 ++ l2) s r ta l =
  ((str_act_list_find f l1 s r ta l) ++ (str_act_list_find f l2 s r ta l))
Proof
 Induct_on `l1` >- rw [str_act_list_find] >>
 Cases_on `h` >>
 Cases_on `o'` >>
 rw [str_act_list_find] >>
 Cases_on `str_act_list_cond f l s n r n' ta` >>
 rw [] >> fs []
QED

(* Theorems about str_may_addr_list, str_may_opt_list and str_may_list *)
Theorem str_may_addr_list_find_MEM:
 !f l s t r vop x. MEM x (str_may_addr_list_find f l s t r vop) ==> MEM x l
Proof
  rw [] >>
  Induct_on `l` >- rw [str_may_addr_list_find] >> strip_tac >>
  Cases_on `h` >>
  Cases_on `o'` >>
  rw [str_may_addr_list_find] >>
  Cases_on `FLOOKUP s n'` >>
  Cases_on `vop` >>
  Cases_on `f e s` >>
  fs [] >| [
    Cases_on `x' <> val_false` >> fs [],
    Cases_on `x'' <> val_false` >> fs [],
    Cases_on `x'' <> val_false` >> fs [],
    rw [] >> Cases_on `x' = x''` >>
    fs [] >>
    Cases_on `n >= t` >>
    fs [],
    rw [] >>
    Cases_on `x' = x''` >>
    fs [] >>
    Cases_on `n >= t` >>
    fs [] >>
    Cases_on `x''' <> val_false` >>
    fs []
  ]
QED

Theorem MEM_str_may_addr_list_find_store_only:
  !l s t r ta a x.
    MEM x (str_may_addr_list_find sem_expr l s t r (SOME a)) ==>
    ?t' c' ta' tv'.
      x = i_assign t' c' (o_store r ta' tv') /\ t'< t /\
      ((?v. sem_expr c' s = SOME v /\ v <> val_false) \/ sem_expr c' s = NONE) /\
      (FLOOKUP s ta' = SOME a \/ FLOOKUP s ta' = NONE)
Proof
  rw [] >> Induct_on `l` >- rw [str_may_addr_list_find] >>
  strip_tac >>
  Cases_on `h` >>
  Cases_on `o'` >>
  rw [str_may_addr_list_find] >>
  Cases_on `FLOOKUP s n'` >>
  Cases_on `sem_expr e s` >>
  fs [] >| [
   Cases_on `x' <> val_false` >> fs [],
   rw [] >>
   Cases_on `x' = a` >>
   fs [] >>
   Cases_on `n >= t` >>
   fs [],
   rw [] >>
   Cases_on `x' = a` >>
   fs [] >>
   Cases_on `n >= t` >>
   fs [] >>
   Cases_on `x'' <> val_false` >>
   fs []
  ]
QED

Theorem MEM_str_may_addr_list_find_store_only_NONE:
  !l s t r ta x.
    MEM x (str_may_addr_list_find sem_expr l s t r NONE) ==>
    ?t' c' ta' tv'.
      x = i_assign t' c' (o_store r ta' tv') /\ t'< t /\
      ((?v. sem_expr c' s = SOME v /\ v <> val_false) \/ sem_expr c' s = NONE)
Proof
  rw [] >> Induct_on `l` >- rw [str_may_addr_list_find] >>
  strip_tac >>
  Cases_on `h` >>
  Cases_on `o'` >>
  rw [str_may_addr_list_find] >>
  Cases_on `FLOOKUP s n'` >> fs [] >>
  Cases_on `sem_expr e s` >> fs [] >-
   (Cases_on `x' <> val_false` >> fs []) >>
  Cases_on `x'' <> val_false` >> fs []
QED

Theorem str_may_addr_list_find_APPEND:
 !f l1 l2 s t r vop.
  str_may_addr_list_find f (l1 ++ l2) s t r vop =
  (str_may_addr_list_find f l1 s t r vop) ++ (str_may_addr_list_find f l2 s t r vop)
Proof
  strip_tac >>
  Induct_on `l1` >-
   (rw [str_may_addr_list_find]) >>
  Cases_on `h` >>
  Cases_on `o'` >>
  rw [str_may_addr_list_find] >>
  Cases_on `FLOOKUP s n'` >>
  Cases_on `vop` >>
  Cases_on `f e s` >>
  rw []
QED

Theorem str_may_addr_list_correct:
  !stl t r a.
    State_st_list_ok stl ==>
    LIST_TO_SET (str_may_addr_list sem_expr stl t r a) =
    str_may_addr (state_list_to_state stl) t r a
Proof
  Cases_on `stl` >> strip_tac >> rename1 `State_st_list l s cs fs` >>
  rw [str_may_addr_list,State_st_list_ok,state_list_to_state,str_may_addr] >>
  fs [EXTENSION] >>
  GEN_TAC >> EQ_TAC >-
   (rw [] >> METIS_TAC [str_may_addr_list_find_MEM,MEM_str_may_addr_list_find_store_only]) >>
  rw [] >>
  `?l1 l2. l = l1 ++ (i_assign t' c' (o_store r ta' tv'))::l2` by METIS_TAC[MEM_SPLIT] >>
  rw [str_may_addr_list_find_APPEND] >>
  DISJ2_TAC >>
  rw [str_may_addr_list_find]
QED

Theorem str_may_opt_list_NONE_correct:
  !stl t r.
    State_st_list_ok stl ==>
    LIST_TO_SET (str_may_opt_list sem_expr stl t r NONE) =
    str_may_opt (state_list_to_state stl) t r NONE
Proof
  Cases_on `stl` >> rw [] >> rename1 `State_st_list l s cs fs` >>
  rw [str_may_opt_list,State_st_list_ok,state_list_to_state,str_may_opt] >>
  fs [EXTENSION] >>
  GEN_TAC >> EQ_TAC >-
   (rw [] >> METIS_TAC [str_may_addr_list_find_MEM,MEM_str_may_addr_list_find_store_only_NONE]) >>
  rw [] >>
  `?l1 l2. l = l1 ++ (i_assign t' c' (o_store r ta' tv'))::l2` by METIS_TAC[MEM_SPLIT] >>
  rw [str_may_addr_list_find_APPEND] >>
  DISJ2_TAC >>
  rw [str_may_addr_list_find] >>
  Cases_on `FLOOKUP s ta'` >> rw []
QED

Theorem str_may_opt_list_correct:
  !stl t r aop.
    State_st_list_ok stl ==>
    LIST_TO_SET (str_may_opt_list sem_expr stl t r aop) =
    str_may_opt (state_list_to_state stl) t r aop
Proof
  rw [] >> Cases_on `aop` >-
   fs [str_may_opt_list_NONE_correct] >>
  `str_may_opt_list sem_expr stl t r (SOME x) = str_may_addr_list sem_expr stl t r x`
    by (Cases_on `stl` >> rw [str_may_addr_list,str_may_opt_list]) >>
  `str_may_opt (state_list_to_state stl) t r (SOME x) = str_may_addr (state_list_to_state stl) t r x`
    by (Cases_on `state_list_to_state stl` >> rw [str_may_opt]) >>
  fs [str_may_addr_list_correct]
QED

Theorem str_may_list_find_eq_str_may_addr_list_find:
  !f l s t r ta.
    str_may_list_find f l s t r ta = str_may_addr_list_find f l s t r (FLOOKUP s ta)
Proof
  rw [] >> Induct_on `l` >-
   rw [str_may_list_find,str_may_addr_list_find] >>
  rw [] >> Cases_on `h` >> Cases_on `o'` >>
  rw [str_may_list_find,str_may_addr_list_find]
QED

Theorem str_may_list_eq_str_may_opt_list:
  !f l s cs fs t r ta.
    State_st_list_ok (State_st_list l s cs fs) ==>
    addr_of_list l t = SOME (r,ta) ==>
    str_may_list f (State_st_list l s cs fs) t =
    str_may_opt_list f (State_st_list l s cs fs) t r (FLOOKUP s ta)
Proof
  rw [str_may_list,str_may_opt_list,str_may_list_find_eq_str_may_addr_list_find]
QED

Theorem str_may_list_correct:
  !stl t. State_st_list_ok stl ==>
          LIST_TO_SET (str_may_list sem_expr stl t) = str_may (state_list_to_state stl) t
Proof
  Cases_on `stl` >> strip_tac >> rename1 `State_st_list l s cs fs` >>
  rw [state_list_to_state] >>
  Cases_on `addr_of_list l t` >> rw [] >-
    (rw [str_may_list] >>
     `addr_of (LIST_TO_SET l) t = NONE` by METIS_TAC [State_st_list_ok,addr_of_list_correct] >>
     fs [str_may_eq_str_may_opt]) >>
  Cases_on `x` >> rename1 `SOME (rs,ta)` >>
  `str_may_list sem_expr (State_st_list l s cs fs) t =
  str_may_opt_list sem_expr (State_st_list l s cs fs) t rs (FLOOKUP s ta)`
    by fs [str_may_list_eq_str_may_opt_list] >>
  `addr_of (LIST_TO_SET l) t = SOME (rs,ta)` by METIS_TAC [State_st_list_ok,addr_of_list_correct] >>
  `str_may (State_st (LIST_TO_SET l) s (LIST_TO_SET cs) (LIST_TO_SET fs)) t =
  str_may_opt (State_st (LIST_TO_SET l) s (LIST_TO_SET cs) (LIST_TO_SET fs)) t rs (FLOOKUP s ta)`
    by fs [str_may_eq_str_may_opt] >>
  fs [str_may_opt_list_correct,state_list_to_state]
QED

Theorem MEM_str_may_opt_list_same_address_value[local]:
  !l s cs fs t  r ta t' e' r' ta' tv' a a'.
    MEM (i_assign t' e' (o_store r' ta' tv')) (str_may_opt_list sem_expr (State_st_list l s cs fs) t r (FLOOKUP s ta)) ==>
    FLOOKUP s ta = SOME a ==>
    FLOOKUP s ta' = SOME a' ==> a = a'
Proof
  rw [] >> fs [str_may_opt_list] >>
  `?t'' c'' ta'' tv''.i_assign t' e' (o_store r' ta' tv') = i_assign t'' c'' (o_store r ta'' tv'') /\
  (FLOOKUP s ta'' = SOME a \/ FLOOKUP s ta'' = NONE)` by METIS_TAC [MEM_str_may_addr_list_find_store_only] >>
  fs []
QED

(* Theorems about str_act_addr_list, str_act_opt_list and str_act_list *)
Theorem str_act_addr_list_find_MEM:
  !f l l1 s r vop i.
     MEM i (str_act_addr_list_find f l s r vop l1) ==> MEM i l
Proof
 rw [] >>
 Induct_on `l` >- rw [str_act_addr_list_find] >>
 Cases_on `h` >>
 Cases_on `o'` >>
 rw [str_act_addr_list_find] >-
  (Cases_on `str_act_addr_list_cond f l1 s n r' n' vop` >>
   rw [] >> fs []) >>
 Cases_on `str_act_addr_list_cond f l1 s n r n' vop` >>
 rw [] >> fs []
QED

Theorem MEM_str_act_addr_list_find_store_only:
 !f l l1 s t r vop i. MEM i (str_act_addr_list_find f l s r vop l1) ==>
 ?t' c' ta' tv'. i = i_assign t' c' (o_store r ta' tv') /\
                 str_act_addr_list_cond f l1 s  t' r ta' vop = []
Proof
 rw [] >>
 Induct_on `l` >- rw [str_act_addr_list_find] >>
 Cases_on `h` >>
 Cases_on `o'` >>
 rw [str_act_addr_list_find] >-
  (Cases_on `str_act_addr_list_cond f l1 s n r' n' vop` >>
   rw [] >> fs []) >>
 Cases_on `str_act_addr_list_cond f l1 s n r n' vop` >>
 rw [] >> fs []
QED

Theorem str_act_addr_list_find_APPEND:
 !f l1 l2 l s r vop.
   str_act_addr_list_find f (l1 ++ l2) s r vop l =
   ((str_act_addr_list_find f l1 s r vop l) ++ (str_act_addr_list_find f l2 s r vop l))
Proof
  Induct_on `l1` >- rw [str_act_addr_list_find] >>
  Cases_on `h` >>
  Cases_on `o'` >>
  rw [str_act_addr_list_find] >>
  Cases_on `str_act_addr_list_cond f l s n r n' vop` >>
  rw [] >> fs []
QED

Theorem str_act_addr_list_cond_empty:
  !l s t' r ta' a.
  (~?i''.
  MEM i'' l /\
  ?t'' c'' ta'' tv''.
  i'' = i_assign t'' c'' (o_store r ta'' tv'') /\
  t'' >  t' /\ (?v. sem_expr c'' s = SOME v /\ v <> val_false) /\
  (FLOOKUP s ta'' = SOME a)) <=>
  str_act_addr_list_cond sem_expr l s t' r ta' (SOME a) = []
Proof
  rw [] >> EQ_TAC >> rw [] >-
   (Induct_on `l` >- rw [str_act_addr_list_cond] >>
    strip_tac >>
    Cases_on `h` >>
    Cases_on `o'` >>
    rw [str_act_addr_list_cond] >| [
      METIS_TAC [],
      METIS_TAC [],
      Cases_on `sem_expr e s` >>
      Cases_on `FLOOKUP s n'` >>
      Cases_on `FLOOKUP s ta'` >>
      fs [] >> METIS_TAC []
    ]) >>
  Induct_on `l` >- rw [] >> strip_tac >>
  Cases_on `h` >>
  Cases_on `o'` >>
  rw [str_act_addr_list_cond] >| [
   fs [] >>
   Cases_on `i'' = i_assign n e (o_internal e')` >>
   rw [],

   fs [] >>
   Cases_on `i'' = i_assign n e (o_load r' n')` >>
   rw [],

   Cases_on `sem_expr e s` >>
   Cases_on `FLOOKUP s n'` >>
   Cases_on `FLOOKUP s ta'` >>
   fs [] >>
   Cases_on `n > t' /\ r' = r /\ x <> val_false /\ x' = a` >>
   fs [] >>
   `str_act_addr_list_cond sem_expr l s t' r ta' (SOME a) = []` by METIS_TAC [] >>
   fs []
 ]
QED

Theorem str_act_addr_list_cond_empty_NONE:
  !l s t' r ta'.
  (~?i''.
  MEM i'' l /\
  ?t'' c'' ta'' tv''.
  i'' = i_assign t'' c'' (o_store r ta'' tv'') /\
  t'' >  t' /\ (?v. sem_expr c'' s = SOME v /\ v <> val_false) /\
  (?v.FLOOKUP s ta'' = SOME v /\ FLOOKUP s ta' = SOME v)) <=>
  str_act_addr_list_cond sem_expr l s t' r ta' NONE = []
Proof
  rw [] >> EQ_TAC >> rw [] >-
   (Induct_on `l` >- rw [str_act_addr_list_cond] >>
    strip_tac >>
    Cases_on `h` >>
    Cases_on `o'` >>
    rw [str_act_addr_list_cond] >| [
      METIS_TAC [],
      METIS_TAC [],
      Cases_on `sem_expr e s` >>
      Cases_on `FLOOKUP s n'` >>
      Cases_on `FLOOKUP s ta'` >>
      fs [] >> METIS_TAC []
    ]) >>
  Induct_on `l` >- rw [] >> strip_tac >>
  Cases_on `h` >>
  Cases_on `o'` >>
  rw [str_act_addr_list_cond] >| [
   fs [] >>
   Cases_on `i'' = i_assign n e (o_internal e')` >>
   rw [],

   fs [] >>
   Cases_on `i'' = i_assign n e (o_load r' n')` >>
   rw [],

   Cases_on `sem_expr e s` >>
   Cases_on `FLOOKUP s n'` >>
   Cases_on `FLOOKUP s ta'` >>
   fs [] >>
   Cases_on `n > t' /\ r' = r /\ x <> val_false /\ x' = x''` >>
   fs [] >>
   `str_act_addr_list_cond sem_expr l s t' r ta' NONE = []` by METIS_TAC [] >>
   fs []
 ]
QED

Theorem str_act_addr_list_correct:
  !stl t r a.
    State_st_list_ok stl ==>
    LIST_TO_SET (str_act_addr_list sem_expr stl t r a) =
    str_act_addr (state_list_to_state stl) t r a
Proof
  Cases_on `stl` >> strip_tac >> rename1 `State_st_list l s cs fs` >> REPEAT GEN_TAC >> strip_tac >>
  `LIST_TO_SET (str_may_addr_list sem_expr (State_st_list l s cs fs) t r a) =
  str_may_addr (state_list_to_state (State_st_list l s cs fs)) t r a`
    by METIS_TAC [str_may_addr_list_correct] >>
  fs [state_list_to_state,State_st_list_ok] >>
  rw [str_act_addr_list,str_act_addr] >> fs [EXTENSION] >>
  GEN_TAC >> EQ_TAC >> rw [] >| [
    METIS_TAC [str_act_addr_list_find_MEM],

    `?t' c' ta' tv'. x = i_assign t' c' (o_store r ta' tv') /\
    str_act_addr_list_cond sem_expr (str_may_addr_list sem_expr (State_st_list l s cs fs) t r a) s t' r ta' (SOME a) = []`
      by METIS_TAC [MEM_str_act_addr_list_find_store_only] >>
    Q.EXISTS_TAC `t'` >>
    Q.EXISTS_TAC `c'` >>
    Q.EXISTS_TAC `ta'` >>
    Q.EXISTS_TAC `tv'` >>
    fs [GSYM str_act_addr_list_cond_empty] >>
    METIS_TAC [],

    `MEM (i_assign t' c' (o_store r ta' tv')) (str_may_addr_list sem_expr (State_st_list l s cs fs) t r a)` by fs [] >>
    `?l1 l2. str_may_addr_list sem_expr (State_st_list l s cs fs) t r a = l1 ++ i_assign t' c' (o_store r ta' tv')::l2` by METIS_TAC [MEM_SPLIT] >>
    rw [str_act_addr_list_find_APPEND] >> DISJ2_TAC >>
    `str_act_addr_list_cond sem_expr (str_may_addr_list sem_expr (State_st_list l s cs fs) t r a) s t' r ta' (SOME a) = []` by METIS_TAC [str_act_addr_list_cond_empty] >>
    `str_act_addr_list_cond sem_expr (l1 ++ i_assign t' c' (o_store r ta' tv')::l2) s t' r ta' (SOME a) = []` by METIS_TAC [] >>
    rw [str_act_addr_list_find]
  ]
QED

Theorem str_act_opt_list_NONE_correct:
  !stl t r.
    State_st_list_ok stl ==>
    LIST_TO_SET (str_act_opt_list sem_expr stl t r NONE) =
    str_act_opt (state_list_to_state stl) t r NONE
Proof
   Cases_on `stl` >> rw [] >> rename1 `State_st_list l s cs fs` >>
   `LIST_TO_SET (str_may_opt_list sem_expr (State_st_list l s cs fs) t r NONE) =
   str_may_opt (state_list_to_state (State_st_list l s cs fs)) t r NONE`
     by METIS_TAC [str_may_opt_list_NONE_correct] >>
   fs [state_list_to_state,State_st_list_ok] >>
   rw [str_act_opt_list,str_act_opt] >> fs [EXTENSION] >>
   GEN_TAC >> EQ_TAC >> rw [] >| [
    METIS_TAC [str_act_addr_list_find_MEM],

    `?t' c' ta' tv'. x = i_assign t' c' (o_store r ta' tv') /\
    str_act_addr_list_cond sem_expr (str_may_opt_list sem_expr (State_st_list l s cs fs) t r NONE) s t' r ta' NONE = []`
      by METIS_TAC [MEM_str_act_addr_list_find_store_only] >>
    Q.EXISTS_TAC `t'` >>
    Q.EXISTS_TAC `c'` >>
    Q.EXISTS_TAC `ta'` >>
    Q.EXISTS_TAC `tv'` >>
    fs [GSYM str_act_addr_list_cond_empty_NONE] >>
    METIS_TAC [],

    `MEM (i_assign t' c' (o_store r ta' tv')) (str_may_opt_list sem_expr (State_st_list l s cs fs) t r NONE)` by fs [] >>
    `?l1 l2. str_may_opt_list sem_expr (State_st_list l s cs fs) t r NONE = l1 ++ i_assign t' c' (o_store r ta' tv')::l2` by METIS_TAC [MEM_SPLIT] >>
    rw [str_act_addr_list_find_APPEND] >> DISJ2_TAC >>
    `str_act_addr_list_cond sem_expr (str_may_opt_list sem_expr (State_st_list l s cs fs) t r NONE) s t' r ta' NONE = []` by METIS_TAC [str_act_addr_list_cond_empty_NONE] >>
    `str_act_addr_list_cond sem_expr (l1 ++ i_assign t' c' (o_store r ta' tv')::l2) s t' r ta' NONE = []` by METIS_TAC [] >>
    rw [str_act_addr_list_find]
  ]
QED

Theorem str_act_opt_list_correct:
  !stl t r aop.
    State_st_list_ok stl ==>
    LIST_TO_SET (str_act_opt_list sem_expr stl t r aop) =
    str_act_opt (state_list_to_state stl) t r aop
Proof
  rw [] >> Cases_on `aop` >-
     fs [str_act_opt_list_NONE_correct] >>
  `str_act_opt_list sem_expr stl t r (SOME x) = str_act_addr_list sem_expr stl t r x`
    by (Cases_on `stl` >> rw [str_act_addr_list,str_act_opt_list,str_may_opt_list,str_may_addr_list]) >>
  `str_act_opt (state_list_to_state stl) t r (SOME x) = str_act_addr (state_list_to_state stl) t r x`
    by (Cases_on `state_list_to_state stl` >> rw [str_act_opt]) >>
  fs [str_act_addr_list_correct]
QED

Theorem str_act_list_cond_eq_str_act_addr_list_cond:
  !f l s t' r ta' ta.
    (!a a'. FLOOKUP s ta = SOME a ==> FLOOKUP s ta' = SOME a' ==> a = a') ==>
    str_act_list_cond f l s t' r ta' ta = str_act_addr_list_cond f l s t' r ta' (FLOOKUP s ta)
Proof
  rw [] >> Induct_on `l` >-
   rw [str_act_list_cond,str_act_addr_list_cond] >>
  rw [] >> Cases_on `h` >> Cases_on `o'` >>
  rw [str_act_list_cond,str_act_addr_list_cond] >>
  Cases_on `f e s` >> fs [] >>
  Cases_on `FLOOKUP s n'` >> fs [] >>
  Cases_on `FLOOKUP s ta'` >> fs [] >>
  Cases_on `FLOOKUP s ta` >> fs []
QED

Theorem str_act_list_find_eq_str_act_addr_list_find:
  !f l s r ta l1.
    (!t' e' r' ta' tv' a a'. MEM (i_assign t' e' (o_store r' ta' tv')) l ==>
     FLOOKUP s ta = SOME a ==> FLOOKUP s ta' = SOME a' ==> a = a') ==>
    str_act_list_find f l s r ta l1 = str_act_addr_list_find f l s r (FLOOKUP s ta) l1
Proof
  rw [] >> Induct_on `l` >-
   rw [str_act_list_find,str_act_addr_list_find] >>
  rw [] >> Cases_on `h` >> Cases_on `o'` >>
  rw [str_act_list_find,str_act_addr_list_find] >| [
    METIS_TAC [],
    METIS_TAC [],
    Cases_on `str_act_list_cond f l1 s n r' n' ta` >>
    Cases_on `str_act_addr_list_cond f l1 s n r' n' (FLOOKUP s ta)` >>
    fs [] >> METIS_TAC [],
    Cases_on `str_act_list_cond f l1 s n r n' ta` >>
    Cases_on `str_act_addr_list_cond f l1 s n r n' (FLOOKUP s ta)` >> fs [] >- METIS_TAC [] >>
    NTAC 2 (`!a a'. FLOOKUP s ta = SOME a ==> FLOOKUP s n' = SOME a' ==> a = a'` by fs [] >>
            `str_act_list_cond f l1 s n r n' ta = str_act_addr_list_cond f l1 s n r n' (FLOOKUP s ta)`
              by fs [str_act_list_cond_eq_str_act_addr_list_cond] >> fs []) >>
    METIS_TAC []
  ]
QED

Theorem str_act_list_eq_str_act_opt_list:
  !l s cs fs t r ta.
    State_st_list_ok (State_st_list l s cs fs) ==>
    addr_of_list l t = SOME (r,ta) ==>
    str_act_list sem_expr (State_st_list l s cs fs) t =
    str_act_opt_list sem_expr (State_st_list l s cs fs) t r (FLOOKUP s ta)
Proof
  rw [str_act_list,str_act_opt_list] >>
  `str_may_list sem_expr (State_st_list l s cs fs) t =
  str_may_opt_list sem_expr (State_st_list l s cs fs) t r (FLOOKUP s ta)`
    by fs [str_may_list_eq_str_may_opt_list] >> rw [] >>
  `!t' e' r' ta' tv' a a'. MEM (i_assign t' e' (o_store r' ta' tv')) (str_may_opt_list sem_expr (State_st_list l s cs fs) t r (FLOOKUP s ta)) ==>
  FLOOKUP s ta = SOME a ==> FLOOKUP s ta' = SOME a' ==> a = a'`
   by METIS_TAC [MEM_str_may_opt_list_same_address_value] >>
  rw [] >> METIS_TAC [str_act_list_find_eq_str_act_addr_list_find]
QED

Theorem str_act_list_correct:
  !stl t. State_st_list_ok stl ==>
          LIST_TO_SET (str_act_list sem_expr stl t) = str_act (state_list_to_state stl) t
Proof
  Cases_on `stl` >> strip_tac >> rename1 `State_st_list l s cs fs` >>
  rw [state_list_to_state] >>
  Cases_on `addr_of_list l t` >> rw [] >-
    (rw [str_act_list] >>
     `addr_of (LIST_TO_SET l) t = NONE` by METIS_TAC [State_st_list_ok,addr_of_list_correct] >>
     fs [str_act_eq_str_act_opt]) >>
  Cases_on `x` >> rename1 `SOME (rs,ta)` >>
  `str_act_list sem_expr (State_st_list l s cs fs) t =
  str_act_opt_list sem_expr (State_st_list l s cs fs) t rs (FLOOKUP s ta)`
    by fs [str_act_list_eq_str_act_opt_list] >>
  `addr_of (LIST_TO_SET l) t = SOME (rs,ta)` by METIS_TAC [State_st_list_ok,addr_of_list_correct] >>
  `str_act (State_st (LIST_TO_SET l) s (LIST_TO_SET cs) (LIST_TO_SET fs)) t =
  str_act_opt (State_st (LIST_TO_SET l) s (LIST_TO_SET cs) (LIST_TO_SET fs)) t rs (FLOOKUP s ta)`
    by fs [str_act_eq_str_act_opt] >>
  fs [str_act_opt_list_correct,state_list_to_state]
QED

Theorem bound_names_program_list_correct:
 !il. LIST_TO_SET (bound_names_program_list il) = bound_names_program (LIST_TO_SET il)
Proof
 rw [
  bound_names_program_list,
  bound_names_program_IMAGE,
  MAP_IMAGE
 ]
QED

Theorem sing_bound_names_program_str_act[local]:
  !I s C Fs t.
    (!i i'. i IN I ==> i' IN I ==> bound_name_instr i = bound_name_instr i' ==> i = i') ==>
    SING (bound_names_program (str_act (State_st I s C Fs) t)) ==>
    SING (str_act (State_st I s C Fs) t)
Proof
  rw [] >>
  fs [SING_DEF] >>
  `x IN bound_names_program (str_act (State_st I' s C Fs) t)` by METIS_TAC [IN_SING] >>
  `!y. y IN bound_names_program (str_act (State_st I' s C Fs) t) ==> y = x` by METIS_TAC [IN_SING] >>
  fs [bound_names_program] >>
  `i IN I'` by METIS_TAC [str_act_in_I] >>
  Q.EXISTS_TAC `i` >>
  Cases_on `i` >> fs [bound_name_instr] >> rw [] >>
  rw [EXTENSION] >> EQ_TAC >> rw [] >>
  Cases_on `x` >>
  `i_assign n' e' o'' IN I'` by METIS_TAC [str_act_in_I] >>
  METIS_TAC [bound_name_instr]
QED

Theorem state_program_list_correct:
 !stl. set (state_program_list stl) = state_program (state_list_to_state stl)
Proof
 Cases_on `stl` >>
 rw [state_program_list,state_list_to_state,state_program]
QED

Theorem append_program_state_list_correct:
 !stl il.
  state_list_to_state (append_program_state_list stl il) =
  union_program_state (state_list_to_state stl) (set il)
Proof
 Cases_on `stl` >>
 rw [union_program_state,append_program_state_list,state_list_to_state]
QED

Theorem str_may_list_find_NONCONT_SUBLIST:
 !f l s t r ta. NONCONT_SUBLIST l (str_may_list_find f l s t r ta)
Proof
  rw [] >>
  Induct_on `l` >>
  rw [str_may_list_find, NONCONT_SUBLIST] >>
  Cases_on `h` >>
  Cases_on `o'` >>
  rw [str_may_list_find, NONCONT_SUBLIST_h_t] >-
   (Cases_on `FLOOKUP s n'` >>
    Cases_on `FLOOKUP s ta` >>
    rw [NONCONT_SUBLIST_h_t]) >>
  `r = r'` by fs [] >>
  Cases_on `FLOOKUP s n'` >>
  Cases_on `f e s` >>
  Cases_on `FLOOKUP s ta` >>
  rw [NONCONT_SUBLIST, NONCONT_SUBLIST_h_t]
QED

Theorem str_may_list_NONCONT_SUBLIST:
 !f l s cs fs t. NONCONT_SUBLIST l (str_may_list f (State_st_list l s cs fs) t)
Proof
 rw [str_may_list] >>
 Cases_on `addr_of_list l t` >-
  (rw [NONCONT_SUBLIST]) >>
 Cases_on `x` >>
 rw [str_may_list_find_NONCONT_SUBLIST]
QED

Theorem str_act_list_find_NONCONT_SUBLIST:
 !f l s r ta l'. NONCONT_SUBLIST l (str_act_list_find f l s r ta l')
Proof
 rw [] >>
 Induct_on `l` >>
 rw [str_act_list_find, NONCONT_SUBLIST] >>
 Cases_on `h` >>
 Cases_on `o'` >>
 rw [str_act_list_find] >-
  (Cases_on `str_act_list_cond f l' s n r' n' ta` >>
   rw [NONCONT_SUBLIST_h_t,NONCONT_SUBLIST]) >>
 rw [NONCONT_SUBLIST_h_t,NONCONT_SUBLIST] >-
  (Cases_on `str_act_list_cond f l' s n r' n' ta` >>
   rw [NONCONT_SUBLIST_h_t,NONCONT_SUBLIST]) >>
 Cases_on `str_act_list_cond f l' s n r n' ta` >>
 rw [NONCONT_SUBLIST_h_t,NONCONT_SUBLIST]
QED

Theorem str_act_list_NONCONT_SUBLIST:
 !l s cs fs t. NONCONT_SUBLIST l (str_act_list sem_expr (State_st_list l s cs fs) t)
Proof
 rw [] >>
 sg `NONCONT_SUBLIST (str_may_list sem_expr (State_st_list l s cs fs) t)
  (str_act_list sem_expr (State_st_list l s cs fs) t)` >-
  (rw [str_act_list] >>
   Cases_on `addr_of_list l t` >-
   rw [NONCONT_SUBLIST] >>
   Cases_on `x` >>
   rw [str_act_list_find_NONCONT_SUBLIST]) >>
 `NONCONT_SUBLIST l (str_may_list sem_expr (State_st_list l s cs fs) t)`
  by rw [str_may_list_NONCONT_SUBLIST] >>
  METIS_TAC [NONCONT_SUBLIST_third]
QED

Theorem bound_names_program_list_str_act_sing_eq[local]:
 !stl t ts. State_st_list_ok stl ==>
  bound_names_program (str_act (state_list_to_state stl) t) = {ts} ==>
  bound_names_program_list (str_act_list sem_expr stl t) = [ts]
Proof
 Cases_on `stl` >> rename1 `State_st_list l s cs fs` >>
 strip_tac >> strip_tac >> rw [State_st_list_ok,state_list_to_state] >>
 `!i i'. i IN (LIST_TO_SET l) ==> i' IN (LIST_TO_SET l) ==>
   bound_name_instr i = bound_name_instr i' ==> i = i'`
  by METIS_TAC [NO_DUPLICATES_bound_name_instr] >>
 `SING (bound_names_program (str_act (State_st (set l) s (set cs) (set fs)) t))`
  by rw [SING_DEF] >>
 `SING (str_act (State_st (LIST_TO_SET l) s (LIST_TO_SET cs) (LIST_TO_SET fs)) t)`
  by fs [sing_bound_names_program_str_act] >>
 `?i. str_act (State_st (LIST_TO_SET l) s (LIST_TO_SET cs) (LIST_TO_SET fs)) t = {i}`
  by METIS_TAC [SING_DEF] >>
 Cases_on `i` >> rename1 `i_assign t' c mop` >>
 `bound_names_program (str_act (State_st (LIST_TO_SET l) s (LIST_TO_SET cs) (LIST_TO_SET fs)) t) = {t'}`
  by fs [bound_names_program,bound_name_instr] >>
 `ts = t'` by fs [] >> rw [] >>
 `bound_names_program (str_act (State_st (set l) s (set cs) (set fs)) t) =
  LIST_TO_SET (bound_names_program_list (str_act_list sem_expr (State_st_list l s cs fs) t))`
  by METIS_TAC [str_act_list_correct,bound_names_program_list_correct,state_list_to_state,State_st_list_ok] >>
 `EVERY ($= t') (bound_names_program_list (str_act_list sem_expr (State_st_list l s cs fs) t))`
  by fs [LIST_TO_SET_EQ_SING] >>
 `NONCONT_SUBLIST l (str_act_list sem_expr (State_st_list l s cs fs) t)`
  by fs [str_act_list_NONCONT_SUBLIST] >>
 `NO_DUPLICATES (str_act_list sem_expr (State_st_list l s cs fs) t)`
  by METIS_TAC [NO_DUPLICATES_NONCONT_SUBLIST] >>
 fs [NO_DUPLICATES,NO_DUPLICATE,bound_names_program_list] >>
 Cases_on `str_act_list sem_expr (State_st_list l s cs fs) t` >> fs [] >> rw [] >>
 rename1 `bound_name_instr i INSERT set (MAP bound_name_instr l')` >>
 Cases_on `l'` >> fs [] >>
 rename1 `str_act_list sem_expr (State_st_list l s cs fs) t = i::i'::l'` >>
 Cases_on `i` >> Cases_on `i'` >>
 rename1 `str_act_list sem_expr (State_st_list l s cs fs) t =
  i_assign t1 c1 mop1::i_assign t2 c2 mop2::l'` >>
 fs [bound_name_instr] >> rw [] >>
 `UNIQUE t1 (t1::t1::MAP bound_name_instr l')` by METIS_TAC [] >>
 fs [UNIQUE_FILTER]
QED

(* sem_instr_exe correctness *)
Theorem sem_instr_exe_correct:
 !stl i. State_st_list_ok stl ==>
  sem_instr_exe sem_expr i stl = sem_instr i (state_list_to_state stl)
Proof
 rw [] >>
 Cases_on `i` >> rename1 `i_assign t c mop` >>
 `bound_names_program (str_act (state_list_to_state stl) t) =
  LIST_TO_SET (bound_names_program_list (str_act_list sem_expr stl t))`
  by METIS_TAC [str_act_list_correct,bound_names_program_list_correct] >>
 Cases_on `stl` >> rename1 `State_st_list l s cs fs` >>
 Cases_on `mop` >>
 fs [State_st_list_ok,sem_instr,sem_instr_exe,state_list_to_state] >>
 rw [] >> Cases_on `r` >> rw [sem_instr_exe] >>
 Cases_on `bound_names_program_list (str_act_list sem_expr (State_st_list l s cs fs) t)` >>
 fs [] >>
 rename1 `bound_names_program_list (str_act_list sem_expr (State_st_list l s cs fs) t) = ts::tl` >>
 Cases_on `tl` >> fs [] >>
 `bound_names_program (str_act (State_st (set l) s (set cs) (set fs)) t) = {ts}` by rw [] >>
 `bound_names_program_list (str_act_list sem_expr (State_st_list l s cs fs) t) = [ts]`
  by METIS_TAC [bound_names_program_list_str_act_sing_eq,state_list_to_state,State_st_list_ok] >>
 fs []
QED

Theorem max_bound_name_list_correct:
 !l. max_bound_name_list l = MAX_SET (bound_names_program (LIST_TO_SET l))
Proof
 INDUCT_THEN SNOC_INDUCT STRIP_ASSUME_TAC >-
 rw [max_bound_name_list, MAX_SET_DEF, bound_names_program] >>
 fs [max_bound_name_list, FOLDL_SNOC, LIST_TO_SET_SNOC,name_le] >>
 GEN_TAC >>
 Cases_on `x` >>
 `FINITE (set l)` by rw [] >>
 `FINITE (bound_names_program (set l))` by rw [finite_bound_names_program] >>
 fs [bound_name_instr, bound_names_program_insert, MAX_SET_THM, arithmeticTheory.MAX_DEF]
QED

Theorem max_name_in_state_list_correct:
 !stl.
  max_name_in_State (state_list_to_state stl) =
  max_name_in_state_list stl 
Proof
 Cases_on `stl` >>
 rw [max_name_in_State,max_name_in_state_list,state_list_to_state] >>
 rw [max_bound_name_list_correct]
QED

Theorem translate_val_list_MAX_I_list_MEM:
 !l v i i'. MEM i l ==>
  MEM i' (translate_val_list v (max_bound_name_list l)) ==>
  bound_name_instr i < bound_name_instr i'
Proof
 rw [] >>
 `i' IN translate_val v (MAX_SET (bound_names_program (LIST_TO_SET l)))`
  by METIS_TAC [translate_val_list_correct,max_bound_name_list_correct] >>
 METIS_TAC [translate_val_max_name_lt,FINITE_LIST_TO_SET]
QED

Theorem NO_DUPLICATES_APP_translate_val_list:
 !l v. NO_DUPLICATES l ==>
 NO_DUPLICATES (l ++ translate_val_list v (max_bound_name_list l))
Proof
 rw [] >>
 `NO_DUPLICATES (translate_val_list v (max_bound_name_list l))`
  by METIS_TAC [NO_DUPLICATES_translate_val_list] >>
 sg `!i i'. MEM i l ==> MEM i' (translate_val_list v (max_bound_name_list l)) ==>
  bound_name_instr i <> bound_name_instr i'` >-
  (rw [] >>
   `bound_name_instr i < bound_name_instr i'` suffices_by DECIDE_TAC >>
   METIS_TAC [translate_val_list_MAX_I_list_MEM]) >>
 METIS_TAC [NO_DUPLICATES_APPEND]
QED

Theorem instr_in_State_list_eq[local]:
 !stl i. instr_in_State_list i stl <=> instr_in_State i (state_list_to_state stl)
Proof
 Cases_on `stl` >> rw [instr_in_State_list,instr_in_State,state_list_to_state]
QED

Theorem max_name_I_is_max[local]:
  !I t.
    FINITE I ==>
    t IN bound_names_program I ==>
    t <= MAX_SET (bound_names_program I)
Proof
  rw [] >>
  Cases_on `I' = {}` >-
   fs [bound_names_program] >>
  `FINITE (bound_names_program I')` by fs [finite_bound_names_program] >>
  Cases_on `bound_names_program I' <> {}` >-
   rw [MAX_SET_DEF] >>
  fs [bound_names_program]
QED

(* FIXME: already in utils? *)
Theorem finite_str_may[local]:
  !t Fs C s I.
    FINITE I ==>
    FINITE (str_may (State_st I s C Fs) t)
Proof
  rw [] >>
  `(str_may (State_st I' s C Fs) t) SUBSET I'` by rw [str_may, SUBSET_DEF] >>
  METIS_TAC [SUBSET_FINITE]
QED

Theorem max_name_I_in_bound_names_program[local]:
  !I. FINITE I ==>
    I <> {} ==>
    MAX_SET (bound_names_program I) IN bound_names_program I
Proof
  rw [] >>
  Cases_on `bound_names_program I' = {}` >-
   fs [bound_names_program, EXTENSION] >>
  `FINITE (bound_names_program I')` by fs [finite_bound_names_program] >>
  rw [MAX_SET_DEF]
QED

Theorem in_str_may_same_r[local]:
  !I s C Fs t r ta t1 c1 r1 ta1 tv1.
    addr_of I t = SOME (r, ta) ==>
    i_assign t1 c1 (o_store r1 ta1 tv1) IN str_may (State_st I s C Fs) t ==>
    r1 = r
Proof
  rw [str_may]
QED

Theorem bn_str_may_SUBSET_bn_str_may_max_name_I:
  !I s C Fs t t' c r ta tv.
    well_formed_state (State_st I s C Fs) ==>
    t' = MAX_SET (bound_names_program (str_may (State_st I s C Fs) t)) ==>
    i_assign t c (o_store r ta tv) IN I ==>
    FLOOKUP s t <> NONE ==>
     (bound_names_program (str_may (State_st I s C Fs) t)) SUBSET
     ((bound_names_program (str_may (State_st I s C Fs) t')) UNION {t'})
Proof
  rw [SUBSET_DEF,bound_names_program] >>
  Cases_on `bound_name_instr i =
   MAX_SET {t' |(?i. i IN str_may (State_st I' s C Fs) t /\ t' = bound_name_instr i)}` >-
   rw [] >>
  `?t' c' r' ta' tv'. i = i_assign t' c' (o_store r' ta' tv')`
   by METIS_TAC [in_str_may_store] >>
  fs [bound_name_instr] >>
  `FINITE I'` by fs [well_formed_state] >>
  `FINITE (str_may (State_st I' s C Fs) t)` by fs [finite_str_may] >>
  Cases_on `t' NOTIN (bound_names_program (str_may (State_st I' s C Fs) t))` >-
   fs [bound_names_program, bound_name_instr] >>
  fs [] >>
  `{t' |(?i. i IN str_may (State_st I' s C Fs) t /\ t' = bound_name_instr i)} =
    bound_names_program (str_may (State_st I' s C Fs) t)`
   by rw [bound_names_program] >>
  `t' <= MAX_SET (bound_names_program (str_may (State_st I' s C Fs) t))`
   by fs [max_name_I_is_max] >>
  `t' < MAX_SET (bound_names_program (str_may (State_st I' s C Fs) t))`
   by fs [] >>
  Q.EXISTS_TAC `i` >>
  rw [bound_name_instr] >>
  `str_may (State_st I' s C Fs) t <> {}` by METIS_TAC [MEMBER_NOT_EMPTY] >>
  `MAX_SET (bound_names_program (str_may (State_st I' s C Fs) t)) IN
   bound_names_program (str_may (State_st I' s C Fs) t)`
   by fs [max_name_I_in_bound_names_program] >>
  fs [bound_names_program] >>
  `?t'' c'' r'' ta'' tv''. i' = i_assign t'' c'' (o_store r'' ta'' tv'')`
   by METIS_TAC [in_str_may_store, bound_names_program] >>
  fs [bound_name_instr] >>
  `i_assign t'' c'' (o_store r'' ta'' tv'') IN I'` by fs [str_may] >>
  `!i i'. i IN I' ==> i' IN I' ==> bound_name_instr i = bound_name_instr i' ==> i = i'`
   by fs [well_formed_state] >>
  `addr_of I' t'' = SOME (r'', ta'') /\ addr_of I' t = SOME (r,ta)`
   by METIS_TAC [addr_of_contains_unique_store] >>
  `r'' = r'` by METIS_TAC [in_str_may_same_r] >>
  rw[str_may] >|[
    `(str_may (State_st I' s C Fs) t) SUBSET I'` by rw [str_may, SUBSET_DEF] >>
    fs [SUBSET_DEF],
    fs [str_may],
    fs [str_may],
    Cases_on `FLOOKUP s ta''` >> rw [] >>
    Cases_on `FLOOKUP s ta'` >> rw [] >>
    Cases_on `FLOOKUP s ta` >-
    (Cases_on `FLOOKUP s t` >> fs [] >>
     `map_down s ta`by METIS_TAC [well_formed_state] >>
     fs [map_down] >> fs []) >>
    fs [str_may]]
QED

Theorem max_name_I_str_may_in_Fs_eq_SUBSET_Fs:
 !I s C Fs t c r ta tv.
   well_formed_state (State_st I s C Fs) ==>
   str_may (State_st I s C Fs) t <> {} ==>
   i_assign t c (o_store r ta tv) IN I ==>
   FLOOKUP s t <> NONE ==>
   ((MAX_SET (bound_names_program (str_may (State_st I s C Fs) t))) IN Fs <=>
    (bound_names_program (str_may (State_st I s C Fs) t)) SUBSET Fs)
Proof
  rw [] >>
  `!t. t IN C ==> bound_names_program (str_may (State_st I' s C Fs) t) SUBSET C`
   by METIS_TAC [wfs_C_str_may] >>
  `!t. t IN Fs ==> bound_names_program (str_may (State_st I' s C Fs) t) SUBSET Fs`
   by METIS_TAC [wfs_F_str_may] >>
  EQ_TAC >>
  rw [] >-
   (`bound_names_program (str_may (State_st I' s C Fs) t) SUBSET
     (bound_names_program (str_may (State_st I' s C Fs)
      (MAX_SET (bound_names_program (str_may (State_st I' s C Fs) t)))) UNION
       {MAX_SET (bound_names_program (str_may (State_st I' s C Fs) t))})`
     by METIS_TAC [bn_str_may_SUBSET_bn_str_may_max_name_I] >>
    `bound_names_program (str_may (State_st I' s C Fs)
      (MAX_SET (bound_names_program (str_may (State_st I' s C Fs) t)))) SUBSET Fs`
     by METIS_TAC [] >>
    `{MAX_SET (bound_names_program (str_may (State_st I' s C Fs) t))} SUBSET Fs` by fs [] >>
    `(bound_names_program (str_may (State_st I' s C Fs)
      (MAX_SET (bound_names_program (str_may (State_st I' s C Fs) t)))) UNION
       {MAX_SET (bound_names_program (str_may (State_st I' s C Fs) t))}) SUBSET Fs`
     by fs [UNION_SUBSET] >>
    METIS_TAC [SUBSET_TRANS]) >>
  Cases_on `bound_names_program (str_may (State_st I' s C Fs) t) = {}` >-
  fs [bound_names_program,EXTENSION] >>
  `FINITE I'` by fs [well_formed_state] >>
  `str_may (State_st I' s C Fs) t SUBSET I'` by (rw [SUBSET_DEF] >> fs [str_may]) >>
  `FINITE (str_may (State_st I' s C Fs) t)` by METIS_TAC [SUBSET_FINITE] >>
  `FINITE (bound_names_program (str_may (State_st I' s C Fs) t))` by fs [finite_bound_names_program] >>
  METIS_TAC [MAX_SET_DEF, SUBSET_DEF]
QED

Theorem max_name_I_str_may_in_C_eq_SUBSET_C:
 !I s C Fs t c r ta tv.
   well_formed_state (State_st I s C Fs) ==>
   str_may (State_st I s C Fs) t <> {} ==>
   i_assign t c (o_store r ta tv) IN I ==>
   FLOOKUP s t <> NONE ==>
   ((MAX_SET (bound_names_program (str_may (State_st I s C Fs) t))) IN C <=>
    (bound_names_program (str_may (State_st I s C Fs) t)) SUBSET C)
Proof
  rw [] >>
  `!t. t IN C ==> bound_names_program (str_may (State_st I' s C Fs) t) SUBSET C`
   by METIS_TAC [wfs_C_str_may] >>
  `!t. t IN Fs ==> bound_names_program (str_may (State_st I' s C Fs) t) SUBSET Fs`
   by METIS_TAC [wfs_F_str_may] >>
  EQ_TAC >>
  rw [] >-
   (`bound_names_program (str_may (State_st I' s C Fs) t) SUBSET
     (bound_names_program (str_may (State_st I' s C Fs)
     (MAX_SET (bound_names_program (str_may (State_st I' s C Fs) t)))) UNION
      {MAX_SET (bound_names_program (str_may (State_st I' s C Fs) t))})`
     by METIS_TAC [bn_str_may_SUBSET_bn_str_may_max_name_I] >>
    `bound_names_program (str_may (State_st I' s C Fs)
      (MAX_SET (bound_names_program (str_may (State_st I' s C Fs) t)))) SUBSET C`
      by METIS_TAC [] >>
    `{MAX_SET (bound_names_program (str_may (State_st I' s C Fs) t))} SUBSET C` by fs [] >>
    `(bound_names_program (str_may (State_st I' s C Fs)
      (MAX_SET (bound_names_program (str_may (State_st I' s C Fs) t)))) UNION
       {MAX_SET (bound_names_program (str_may (State_st I' s C Fs) t))}) SUBSET C`
     by fs [UNION_SUBSET] >>
    METIS_TAC [SUBSET_TRANS]) >>
  Cases_on `bound_names_program (str_may (State_st I' s C Fs) t) = {}` >-
   fs [bound_names_program, EXTENSION] >>
  `FINITE I'` by fs [well_formed_state] >>
  `str_may (State_st I' s C Fs) t SUBSET I'` by (rw [SUBSET_DEF] >> fs [str_may]) >>
  `FINITE (str_may (State_st I' s C Fs) t)` by METIS_TAC [SUBSET_FINITE] >>
  `FINITE (bound_names_program (str_may (State_st I' s C Fs) t))` by fs [finite_bound_names_program] >>
  METIS_TAC [MAX_SET_DEF, SUBSET_DEF]
QED

Theorem Completed_list_correct:
 !stl i.
 (Completed_list sem_expr stl i) <=>
 (Completed (state_list_to_state stl) i)
Proof
 Cases_on `stl` >>
 rename1 `State_st_list l s c fs` >>
 rw [state_list_to_state] >>
 Cases_on `i` >>
 Cases_on `o'` >>
 EQ_TAC >>
 rw [Completed, Completed_list, FLOOKUP_DEF] >>
 Cases_on `n IN FDOM s` >> fs [] >>
 Cases_on `r` >>
 fs [Completed, Completed_list, FLOOKUP_DEF]
QED

(* FIXME: add Completed_all definition? *)
Theorem Completed_list_up_to_length_all_Completed:
 !l s cs fs n.
  Completed_list_up_to sem_expr (State_st_list l s cs fs) n ==>
  LENGTH l <= n ==>
  !i. instr_in_State i (state_list_to_state (State_st_list l s cs fs)) ==>
  Completed (state_list_to_state (State_st_list l s cs fs)) i
Proof
 rw [Completed_list_up_to] >>
 `Completed_list sem_expr (State_st_list l s cs fs) i`
  suffices_by rw [Completed_list_correct] >>
 fs [instr_in_State,state_list_to_state] >>
 METIS_TAC [TAKE_LENGTH_TOO_LONG]
QED

Theorem SORTED_DROP_MEM_TAKE:
 !R. transitive R ==>
  !l l' n a. SORTED R l ==>
   DROP n l = a::l' ==>
   !b. R b a ==> ~R a b ==>
    MEM b l ==>
    MEM b (TAKE n l)
Proof
 rw [] >>
 `MEM b (TAKE n l) \/ MEM b (DROP n l)`
  by METIS_TAC [TAKE_DROP,MEM_APPEND] >>
 `MEM b (a::l')` by METIS_TAC [] >>
 `b <> a` by (strip_tac >> fs []) >>
 fs [] >> rw [] >>
 sg `SORTED R ((TAKE n l ++ [a]) ++ l')` >-
  (`(TAKE n l ++ [a]) ++ l' = l` suffices_by rw [] >>
   `l = TAKE n l ++ a::l'` by METIS_TAC [TAKE_DROP] >>
   once_rewrite_tac [GSYM APPEND_ASSOC] >>
   `[a] ++ l' = a::l'` by rw [] >>
   METIS_TAC []) >>
 `!x y. MEM x (TAKE n l ++ [a]) ==> MEM y l' ==> R x y`
  by METIS_TAC [SORTED_APPEND] >>
 `MEM a (TAKE n l ++ [a])` by rw [] >>
 METIS_TAC []
QED

Theorem Completed_list_up_to_SORTED_less_Completed_list:
 !f_sem l s cs fs n i il.
   Completed_list_up_to f_sem (State_st_list l s cs fs) n ==>
   DROP n l = i::il ==>
   SORTED bound_name_instr_le l ==>
   !i'. MEM i' l ==>
    bound_name_instr i' < bound_name_instr i ==>
    Completed_list f_sem (State_st_list l s cs fs) i'
Proof
 rw [Completed_list_up_to] >>
 `MEM i' (TAKE n l)` suffices_by METIS_TAC [] >>
 `bound_name_instr_le i' i` by rw [bound_name_instr_le,name_le] >>
 `~bound_name_instr_le i i'` by rw [bound_name_instr_le,name_le] >>
 METIS_TAC [SORTED_DROP_MEM_TAKE,transitive_bound_name_instr_le]
QED

Theorem Completed_list_up_to_SORTED_less_Completed:
 !l s cs fs n i il.
   Completed_list_up_to sem_expr (State_st_list l s cs fs) n ==>
   DROP n l = i::il ==>
   SORTED bound_name_instr_le l ==>
   !i'. instr_in_State i' (state_list_to_state (State_st_list l s cs fs)) ==>
    bound_name_instr i' < bound_name_instr i ==>
    Completed (state_list_to_state (State_st_list l s cs fs)) i'
Proof
 METIS_TAC [
  Completed_list_up_to_SORTED_less_Completed_list,
  Completed_list_correct,
  instr_in_State,
  state_list_to_state
 ]
QED

val _ = export_theory ();
