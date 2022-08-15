open HolKernel boolLib Parse bossLib ottLib;
infix THEN THENC |-> ## ;
local open arithmeticTheory stringTheory containerTheory pred_setTheory listTheory 
  finite_mapTheory in end;

val _ = new_theory "mil";

open wordsTheory;

val _ = type_abbrev("k", ``:num``); (* index variable (subscript) *)
val _ = type_abbrev("v", ``:word64``);
val _ = type_abbrev("t", ``:num``);
val _ = Hol_datatype ` 
e =  (* expression *)
   e_val of v (* value *)
 | e_name of t (* name *)
 | e_and of e => e (* and *)
 | e_or of e => e (* or *)
 | e_xor of e => e (* exclusive or *)
 | e_add of e => e (* addition *)
 | e_sub of e => e (* subtraction *)
 | e_mul of e => e (* multiplication *)
 | e_div of e => e (* division *)
 | e_sdiv of e => e (* signed division *)
 | e_mod of e => e (* modulo *)
 | e_smod of e => e (* signed modulo *)
 | e_lsl of e => e (* left shift *)
 | e_lsr of e => e (* right shift *)
 | e_asr of e => e (* signed right shift *)
 | e_eq of e => e (* equal *)
 | e_neq of e => e (* not equal *)
 | e_lt of e => e (* less than *)
 | e_slt of e => e (* signed less than *)
 | e_le of e => e (* less or equal to *)
 | e_sle of e => e (* signed less or equal to *)
 | e_comp of e (* complement *)
 | e_not of e (* logical negation *)
`;
val _ = Hol_datatype ` 
res =  (* resource *)
   res_PC (* program counter *)
 | res_REG (* register *)
 | res_MEM (* memory *)
`;
val _ = Hol_datatype ` 
op =  (* operation *)
   o_internal of e (* internal *)
 | o_load of res => t (* load *)
 | o_store of res => t => t (* store *)
`;
val _ = Hol_datatype ` 
i =  (* microinstruction *)
   i_assign of t => e => op (* guarded assignment *)
`;
val _ = type_abbrev("I", ``:i -> bool``);
val _ = type_abbrev("N", ``:num -> bool``);
val _ = type_abbrev("s", ``:(t |-> v)``);
val _ = type_abbrev("d", ``:(t |-> (t |-> v))``);
val _ = Hol_datatype ` 
obs =  (* observation *)
   obs_internal (* internal unobservable operation *)
 | obs_dl of v (* load from data cache *)
 | obs_ds of v (* store into data cache *)
 | obs_il of v (* load from instructions *)
`;
val _ = Hol_datatype ` 
act =  (* action *)
   act_exe (* execute *)
 | act_cmt of v => v (* commit *)
 | act_ftc of I (* fetch *)
`;
val _ = Hol_datatype ` 
State =  (* state *)
   State_st of I => s => N => N
`;
val _ = Hol_datatype ` 
l =  (* label *)
   l_lb of obs => act => t
`;
Definition val_false:
  val_false : v = (n2w 0)
End

Definition val_true:
  val_true : v = (n2w 1)
End

Definition val_zero:
  val_zero : v = (n2w 0)
End

Definition val_one:
  val_one : v = (n2w 1)
End

Definition val_two:
  val_two : v = (n2w 2)
End

Definition val_four:
  val_four : v = (n2w 4)
End

Definition map_down:
 map_down (f:'a |-> 'b) (x:'a) = (?v. FLOOKUP f x = SOME v)
End

Definition map_up:
 map_up (f:'a |-> 'b) (x:'a) = ~(map_down f x)
End

Definition instr_in_State:
 instr_in_State (i:i) ((State_st I s C f):State) = (i IN I)
End

Definition bound_name_instr:
 bound_name_instr ((i_assign t e opm):i) = t
End

Definition bound_names_program:
 bound_names_program (I:I) : N =
  { t | ?i. i IN I /\ t = bound_name_instr i }
End

Definition program_difference_names:
 program_difference_names (I0:I) (N0:N) : I =
  { i | i IN I0 /\ bound_name_instr i NOTIN N0 }
End

Definition names_e:
 (names_e (e_val v) = {})
 /\
 (names_e (e_name t) = {t})
 /\
 (names_e (e_and e1 e2) = names_e e1 UNION names_e e2)
 /\
 (names_e (e_or e1 e2) = names_e e1 UNION names_e e2)
 /\
 (names_e (e_xor e1 e2) = names_e e1 UNION names_e e2)
 /\
 (names_e (e_add e1 e2) = names_e e1 UNION names_e e2)
 /\
 (names_e (e_sub e1 e2) = names_e e1 UNION names_e e2)
 /\
 (names_e (e_mul e1 e2) = names_e e1 UNION names_e e2)
 /\
 (names_e (e_div e1 e2) = names_e e1 UNION names_e e2)
 /\
 (names_e (e_sdiv e1 e2) = names_e e1 UNION names_e e2)
 /\
 (names_e (e_mod e1 e2) = names_e e1 UNION names_e e2)
 /\
 (names_e (e_smod e1 e2) = names_e e1 UNION names_e e2)
 /\
 (names_e (e_lsl e1 e2) = names_e e1 UNION names_e e2)
 /\
 (names_e (e_lsr e1 e2) = names_e e1 UNION names_e e2)
 /\
 (names_e (e_asr e1 e2) = names_e e1 UNION names_e e2)
 /\
 (names_e (e_eq e1 e2) = names_e e1 UNION names_e e2)
 /\
 (names_e (e_neq e1 e2) = names_e e1 UNION names_e e2)
 /\
 (names_e (e_lt e1 e2) = names_e e1 UNION names_e e2)
 /\
 (names_e (e_slt e1 e2) = names_e e1 UNION names_e e2)
 /\
 (names_e (e_le e1 e2) = names_e e1 UNION names_e e2)
 /\
 (names_e (e_sle e1 e2) = names_e e1 UNION names_e e2)
 /\
 (names_e (e_comp e) = names_e e)
 /\
 (names_e (e_not e) = names_e e)
End

Definition names_o:
 (names_o (o_internal e) = names_e e)
 /\
 (names_o (o_load r ta) = {ta})
 /\
 (names_o (o_store r ta tv) = {ta;tv})
End

Definition free_names_instr:
 free_names_instr (i_assign t c mop) = names_e c UNION names_o mop
End

Definition names_instr:
 names_instr (i:i) : N = {bound_name_instr i} UNION free_names_instr i
End

Definition sem_expr:
 sem_expr = @(f: e -> s -> v option).
  (!e s. (?v. f e s = SOME v) <=> (names_e e SUBSET FDOM s))
  /\
  (!e s s'. (!t. t IN names_e e ==> FLOOKUP s t = FLOOKUP s' t) ==> f e s = f e s')
  /\
  (!v s. f (e_val v) s = SOME v)
End

Definition translate_val:
 translate_val = @(f: v -> t -> I). !(v:v) (t:t).
  (FINITE (f v t))
  /\
  (!i i'. i IN (f v t) ==> i' IN (f v t) ==>
    bound_name_instr i = bound_name_instr i' ==> i = i')
  /\
  (!i. i IN (f v t) ==> !t'. t' IN free_names_instr i ==>
    t' < bound_name_instr i)
  /\ (* FIXME: overly strong *)
  (!i. i IN (f v t) ==> !t'. t' IN names_instr i ==> t < t')
  /\
  (!i. i IN (f v t) ==> !t'. t' IN free_names_instr i ==>
    ?i'. i' IN (f v t) /\ bound_name_instr i' = t')
  /\
  (!t1 c1 mop1. i_assign t1 c1 mop1 IN (f v t) ==>
    !t2 c2 mop2. t2 IN names_e c1 ==>
     i_assign t2 c2 mop2 IN (f v t) ==> c2 = e_val val_true)
  /\
  (!t1 c1 mop1. i_assign t1 c1 mop1 IN (f v t) ==>
    !s v'. sem_expr c1 s = SOME v' ==> v' <> val_false ==>
     !t2 c2 mop2 v''. t2 IN names_o mop1 ==>
      i_assign t2 c2 mop2 IN (f v t) ==>
      sem_expr c2 s = SOME v'' ==> v'' <> val_false)
  /\
  (!t' c ta tv. i_assign t' c (o_store res_PC ta tv) IN (f v t) ==>
    i_assign ta (e_val val_true) (o_internal (e_val val_zero)) IN (f v t))
  /\
  (!t' c ta. i_assign t' c (o_load res_PC ta) IN (f v t) ==>
    i_assign ta (e_val val_true) (o_internal (e_val val_zero)) IN (f v t))
End

Definition Completed:
 (Completed (State_st I s C Fs) (i_assign t c (o_store res_MEM t1 t2)) =
  ((sem_expr c s = SOME val_false) \/ (t IN C))) (* discarded, or committed memory store *)
 /\
 (Completed (State_st I s C Fs) (i_assign t c (o_store res_PC t1 t2)) =
  ((sem_expr c s = SOME val_false) \/ (t IN Fs))) (* discarded, or fetched PC store *)
 /\
 (Completed (State_st I s C Fs) (i_assign t c op) =
  ((sem_expr c s = SOME val_false) \/ (t IN FDOM s))) (* discarded, or executed *)
End

Definition addr_of:
 addr_of I t =
  let rta =
   { (r,ta) | (?c. i_assign t c (o_load r ta) IN I) \/
      (?c tv. i_assign t c (o_store r ta tv) IN I) } in
  if rta = EMPTY then NONE else SOME (CHOICE rta)
End

Definition str_may:
 str_may (State_st I s C Fs) t =
  { i | i IN I /\ ?t' c' r ta' tv'. i = i_assign t' c' (o_store r ta' tv') /\
     t' < t /\ ?ta. addr_of I t = SOME (r,ta) /\
     ((?v. sem_expr c' s = SOME v /\ v <> val_false) \/ sem_expr c' s = NONE) /\
     ((?v. FLOOKUP s ta' = SOME v /\ FLOOKUP s ta = SOME v) \/
      FLOOKUP s ta' = NONE \/ FLOOKUP s ta = NONE) }
End

Definition str_act:
 str_act (State_st I s C Fs) t =
  { i | i IN str_may (State_st I s C Fs) t /\
     ?t' c' r ta' tv'. i = i_assign t' c' (o_store r ta' tv') /\
     ?ta. addr_of I t = SOME (r,ta) /\
     ~(?i''. i'' IN str_may (State_st I s C Fs) t /\
        ?t'' c'' ta'' tv''. i'' = i_assign t'' c'' (o_store r ta'' tv'') /\
         t'' > t' /\ (?v. sem_expr c'' s = SOME v /\ v <> val_false) /\
         ((?v. FLOOKUP s ta'' = SOME v /\ FLOOKUP s ta = SOME v) \/
          (?v. FLOOKUP s ta'' = SOME v /\ FLOOKUP s ta' = SOME v))) }
End

Definition sem_instr:
 (sem_instr (i_assign t c (o_internal e)) (State_st I s C Fs) =
   case sem_expr e s of
   | SOME v => SOME (v,obs_internal)
   | NONE => NONE) /\
 (sem_instr (i_assign t c (o_load r ta)) (State_st I s C Fs) =
   let tps = bound_names_program (str_act (State_st I s C Fs) t) in
   if SING tps then
     let ts = CHOICE tps in
     case FLOOKUP s ta, FLOOKUP s ts of
     | SOME a, SOME v =>
       if ts IN C /\ r = res_MEM then
         SOME (v,obs_dl a)
       else
         SOME (v,obs_internal)
     | _, _ => NONE
   else NONE) /\
 (sem_instr (i_assign t c (o_store r ta tv)) (State_st I s C Fs) =
   case FLOOKUP s tv, FLOOKUP s ta of
   | SOME v, SOME a => SOME (v,obs_internal)
   | _, _ => NONE)
End

(** definitions *)
(* defns mil_out_of_order_opsem *)

val (mil_out_of_order_opsem_rules, mil_out_of_order_opsem_ind, mil_out_of_order_opsem_cases) = Hol_reln`
(* defn out_of_order_step *)

( (* OoO_Exe *) ! (I:I) (s:s) (C:N) (F:N) (obs:obs) (t:t) (v:v) (State:State) (i:i) (c:e) (op:op) . (clause_name "OoO_Exe") /\
(( ( State  =  (State_st I s C F) ) ) /\
( ( i  =  (i_assign t c op) ) ) /\
( ( i  IN  I ) ) /\
( (sem_instr  i   State  = SOME ( v , obs )) ) /\
( (map_up  s   t ) ) /\
( (?v. sem_expr  c   s  = SOME v /\ v <> val_false) ))
 ==> 
( ( out_of_order_step (State_st I s C F) (l_lb obs act_exe t) (State_st I  (FUPDATE  s  ( t ,  v ))  C F) )))

/\ ( (* OoO_Cmt *) ! (I:I) (s:s) (C:N) (F:N) (a:v) (v:v) (t:t) (State:State) (c:e) (t1:t) (t2:t) . (clause_name "OoO_Cmt") /\
(( ( State  =  (State_st I s C F) ) ) /\
( (map_down  s   t ) ) /\
( ( (i_assign t c (o_store res_MEM t1 t2))  IN  I ) ) /\
( (~ ( t  IN  C )) ) /\
( (FLOOKUP  s   t1  = SOME  a ) ) /\
( (FLOOKUP  s   t2  = SOME  v ) ) /\
( (  (bound_names_program   (str_may  State   t )  )   SUBSET  C ) ))
 ==> 
( ( out_of_order_step (State_st I s C F) (l_lb (obs_ds a) (act_cmt a v) t) (State_st I s  ( C  UNION   { t }  )  F) )))

/\ ( (* OoO_Ftc *) ! (I:I) (s:s) (C:N) (F:N) (v:v) (I':I) (t:t) (State:State) (c:e) (t1:t) (t2:t) . (clause_name "OoO_Ftc") /\
(( ( State  =  (State_st I s C F) ) ) /\
( ( (i_assign t c (o_store res_PC t1 t2))  IN  I ) ) /\
( (FLOOKUP  s   t  = SOME  v ) ) /\
( (~ ( t  IN  F )) ) /\
( (  (bound_names_program   (str_may  State   t )  )   SUBSET  F ) ) /\
( (  (translate_val  v    (MAX_SET   (bound_names_program  I )  )  )   =  I' ) ))
 ==> 
( ( out_of_order_step (State_st I s C F) (l_lb (obs_il v) (act_ftc I') t) (State_st  ( I  UNION  I' )  s C  ( F  UNION   { t }  ) ) )))

`;
(** definitions *)
(* defns mil_in_order_opsem *)

val (mil_in_order_opsem_rules, mil_in_order_opsem_ind, mil_in_order_opsem_cases) = Hol_reln`
(* defn in_order_step *)

( (* IO_Step *) ! (State:State) (obs:obs) (act:act) (t:t) (State':State) (i:i) . (clause_name "IO_Step") /\
(( ( out_of_order_step State (l_lb obs act t) State' )) /\
( (! i . instr_in_State  i   State  ==>   (  (  (bound_name_instr  i )   <  t )   ==>   (Completed  State   i )  )  ) ))
 ==> 
( ( in_order_step State (l_lb obs act t) State' )))

`;

val _ = export_theory ();
