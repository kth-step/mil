structure bir_to_milLib :> bir_to_milLib =
struct

open HolKernel boolLib liteLib simpLib Parse bossLib;
open bir_programTheory bir_immTheory;
open numSyntax listSyntax pred_setSyntax wordsSyntax;
open bir_programSyntax bir_expSyntax bir_exp_immSyntax bir_immSyntax bir_envSyntax bir_exp_memSyntax bir_valuesSyntax bir_typing_expSyntax;
open milSyntax;

val instr_var = mk_var ("t", num);

val ERR = mk_HOL_ERR "bir_to_milLib";

val wrap_exn = Feedback.wrap_exn "bir_to_milLib";

local
  open bir_nzcv_expTheory bir_extra_expsSyntax
in
  fun bir_prog_to_mnf bir_prog =
   (snd o dest_eq o snd o dest_thm o EVAL) bir_prog
end
;

local
  open wordsSyntax
in
 fun mem_bounds_from_hex mem_base_hex mem_len_hex =
  let
    val (mem_base, mem_len) =
     (Arbnum.fromHexString mem_base_hex, Arbnum.fromHexString mem_len_hex)
    val mem_end = Arbnum.- (Arbnum.+ (mem_base, mem_len), Arbnum.fromInt 128)
  in
    pairSyntax.mk_pair (mk_wordi (mem_base, 64), mk_wordi (mem_end, 64))
 end
end
;

fun ex_f fname tm =
  let
    val tm_str = (fst o dest_strip_comb) tm
  in
    raise ERR fname (tm_str^" not supported")
  end
;

fun rem_dup l =
 case l of
   [] => []
 | h::t => h::rem_dup (List.filter (fn a => a <> h) t)
;

(* TODO: Better feedback in exceptions *)

val mil_val_ty = (el 1 o fst o strip_fun) (type_of e_val_tm);

val guard_true_tm = mk_e_val v_true_tm;

val iset_ty = i_ty --> bool;

val ilist_ty = mk_list_type i_ty;

(* check the type of a bir exp, copied from HolBA repo:
   https://github.com/kth-step/HolBA/blob/dev_symbexec_form/src/tools/symbexec/bir_exp_typecheckLib.sml
 *)
fun type_of_bir_exp_CONV term =
    let
      open bir_immTheory
      open bir_valuesTheory
      open bir_envTheory
      open bir_exp_memTheory
      open bir_bool_expTheory
      open bir_extra_expsTheory
      open bir_nzcv_expTheory
      open bir_interval_expTheory;
      open bir_typing_expTheory;
      val type_of_bir_exp_thms = [
        type_of_bir_exp_def,
        bir_var_type_def,
        bir_type_is_Imm_def,
        type_of_bir_imm_def,
        BExp_Aligned_type_of,
        BExp_unchanged_mem_interval_distinct_type_of,
        bir_number_of_mem_splits_REWRS,
        BType_Bool_def,
        bir_exp_true_def,
        bir_exp_false_def,
        BExp_MSB_type_of,
        BExp_nzcv_ADD_DEFS,
        BExp_nzcv_SUB_DEFS,
        n2bs_def,
        BExp_word_bit_def,
        BExp_Align_type_of,
        BExp_ror_type_of,
        BExp_LSB_type_of,
        BExp_word_bit_exp_type_of,
        BExp_ADD_WITH_CARRY_type_of,
        BExp_word_reverse_type_of,
        BExp_ror_exp_type_of,
        bir_immtype_of_size_def
      ]
      val conv = SIMP_CONV (srw_ss()) type_of_bir_exp_thms
    in
      conv term
    end
      handle _ => raise ERR "type_of_bir_exp_CONV" "conversion failed";

fun type_of_bir_exp_DIRECT_CONV term =
   let
     open optionSyntax;
     open bir_valuesSyntax;
     open bir_typing_expSyntax;

     val _ = if is_type_of_bir_exp term then () else
               raise ERR "type_of_bir_exp_DIRECT_CONV" "cannot handle term";

     val thm = type_of_bir_exp_CONV term;

     val result = (snd o dest_eq o concl) thm;
     val _ = if is_none result orelse
                (is_some result andalso
                 ((fn x => is_BType_Imm x orelse is_BType_Mem x) o dest_some) result) then () else
               raise ERR "type_of_bir_exp_DIRECT_CONV" "didn't reach the result";
   in dest_BType_Imm (dest_some result) end
   handle _ => raise ERR "type_of_bir_exp_DIRECT_CONV" ("ill-typed term: " ^ Parse.term_to_string term);

fun check_type_of_bir_exp exp = (type_of_bir_exp_DIRECT_CONV o mk_type_of_bir_exp) exp

(*
val bexp_term = ``BExp_BinPred BIExp_LessOrEqual
          (BExp_Den (BVar "countw" (BType_Imm Bit64)))
          (BExp_Const (Imm64 0xFFFFFFFFFFFFFFFEw))``;
          
check_type_of_bir_exp bexp_term
*)

(****************************************************************)

(* Obtains a word from a BIR immediate. *)
fun bir_imm_to_mil_v imm =
  let
    val ex_f_imm = ex_f "bir_imm_to_mil_v"
    val new_imm =
     if is_n2bs imm then
       (if is_Bit64 ((snd o dest_n2bs) imm) then
          mk_Imm_of_int 64 ((int_of_term o fst o dest_n2bs) imm)
        else imm)
     else imm
     fun make_64w imm_tm = mk_wordii ((uint_of_word o snd o gen_dest_Imm) imm_tm, 64)
  in
    if is_Imm64 new_imm then
      (snd o gen_dest_Imm) new_imm
    else if is_Imm32 new_imm then
      make_64w new_imm
    else if is_Imm16 new_imm then
      make_64w new_imm
    else if is_Imm8 new_imm then
      make_64w new_imm
    else if is_Imm1 new_imm then
      make_64w new_imm
    else
      ex_f_imm new_imm
  end
;

(* Obtains a MIL value from a BIR constant. *)
fun bir_const_to_mil_v exp =
  (bir_imm_to_mil_v o dest_BExp_Const) exp
;

(* Obtains a MIL name from a BIR variable. *)
fun bir_den_to_mil_name reg_map exp =
  let
    val (name, ity) = dest_BVar_string (dest_BExp_Den exp)
  in
    Redblackmap.find (reg_map, name)
  end
;

(* Takes a term (e.g. ``i + 1``), an SML integer (e.g. 1), and computes
 * the term where this integer was added (``i + 2`` for the above). *)
fun tm_plus_eval tm int =
  if is_plus tm then
    let
      val (stm1, stm2) = dest_plus tm
      val int' = (int_of_term stm2) + int
    in
      mk_plus (stm1, term_of_int int')
    end
  else
    mk_plus (tm, term_of_int int)
;

fun build_mil_instr guard_tm op_tm t_curr =
 (t_curr, mk_i_assign (t_curr, guard_tm, op_tm), tm_plus_eval t_curr 1)
;

(* the memory term for bir *)
val bir_mem_name = "MEM";

val BExp_Den_Mem_tm =
 (mk_BExp_Den o mk_BVar_string) (bir_mem_name, (mk_BType_Mem (Bit64_tm, Bit8_tm)))
;

fun is_BExp_Den_Mem tm = term_eq tm BExp_Den_Mem_tm;
	 
(* Creates a MIL expression and instructions from a BIR expression.
 * The reg_map is used to map BIR variable names onto the
 * MIL names holding their loaded values.  *)
fun bir_exp_to_mil_e reg_map exp t_curr =
  let
    val ex_f_exp = ex_f "bir_exp_to_mil_e"
  in
    if is_BExp_Const exp then
      (mk_e_val (bir_const_to_mil_v exp), [], t_curr)
    else if is_BExp_Den exp then
      (mk_e_name (bir_den_to_mil_name reg_map exp), [], t_curr)
    else if is_BExp_UnaryExp exp then
      bir_unaryexp_to_mil_e reg_map exp t_curr
    else if is_BExp_BinExp exp then
      bir_binexp_to_mil_e reg_map exp t_curr
    else if is_BExp_BinPred exp then
      bir_binpred_to_mil_e reg_map exp t_curr
    else if is_BExp_Load exp then
      bir_load_to_mil_e reg_map exp t_curr
    else if is_BExp_Store exp then
      bir_store_to_mil_e reg_map exp t_curr
    else if is_BExp_Cast exp then
      bir_cast_to_mil_e reg_map exp t_curr
    else
      ex_f_exp exp
  end
and bir_unaryexp_to_mil_e reg_map exp t_curr =
  let
    val (unexp_type, oper) = dest_BExp_UnaryExp exp
    val (mil_exp, il, t_curr) = bir_exp_to_mil_e reg_map oper t_curr
    val ex_f_unexp = ex_f "bir_unaryexp_to_mil_e"
  in
    if is_BIExp_Not unexp_type then
      (mk_e_comp mil_exp, il, t_curr)
    else
      ex_f_unexp exp
  end
and bir_binexp_to_mil_e_64 reg_map exp t_curr =
  let
    val (biexp_type, op1, op2) = dest_BExp_BinExp exp
    val (mil_op1, il1, t_curr) = bir_exp_to_mil_e reg_map op1 t_curr
    val (mil_op2, il2, t_curr) = bir_exp_to_mil_e reg_map op2 t_curr
    val ex_f_binexp_64 = ex_f "bir_binexp_to_mil_64"
  in
    if is_BIExp_And biexp_type then
      (mk_e_and (mil_op1, mil_op2), il1@il2, t_curr)
    else if is_BIExp_Or biexp_type then
      (mk_e_or (mil_op1, mil_op2), il1@il2, t_curr)
    else if is_BIExp_Xor biexp_type then
      (mk_e_xor (mil_op1, mil_op2), il1@il2, t_curr)
    else if is_BIExp_Plus biexp_type then
      (mk_e_add (mil_op1, mil_op2), il1@il2, t_curr)
    else if is_BIExp_Minus biexp_type then
      (mk_e_sub (mil_op1, mil_op2), il1@il2, t_curr)
    else if is_BIExp_Mult biexp_type then
      (mk_e_mul (mil_op1, mil_op2), il1@il2, t_curr)
    else if is_BIExp_Div biexp_type then
      (mk_e_div (mil_op1, mil_op2), il1@il2, t_curr)
    else if is_BIExp_SignedDiv biexp_type then
      (mk_e_sdiv (mil_op1, mil_op2), il1@il2, t_curr)
    else if is_BIExp_Mod biexp_type then
      (mk_e_mod (mil_op1, mil_op2), il1@il2, t_curr)
    else if is_BIExp_SignedMod biexp_type then
      (mk_e_smod (mil_op1, mil_op2), il1@il2, t_curr)
    else if is_BIExp_LeftShift biexp_type then
      (mk_e_lsl (mil_op1, mil_op2), il1@il2, t_curr)
    else if is_BIExp_RightShift biexp_type then
      (mk_e_lsr (mil_op1, mil_op2), il1@il2, t_curr)
    else if is_BIExp_SignedRightShift biexp_type then
      (mk_e_asr (mil_op1, mil_op2), il1@il2, t_curr)
    else
      ex_f_binexp_64 exp
  end
and bir_binexp_to_mil_e reg_map exp t_curr =
    let
	val (mil_exp_64, il, t_curr) = bir_binexp_to_mil_e_64 reg_map exp t_curr
	val bir_exp_type_tm = check_type_of_bir_exp exp
	fun resize_mil_exp mask = mk_e_and (mil_exp_64, mk_e_val mask)
	val ex_f_binexp = ex_f "bir_binexp_to_mil"
    in
	if is_Bit64 bir_exp_type_tm then
	    (mil_exp_64, il, t_curr)
	else if is_Bit32 bir_exp_type_tm then
	    (resize_mil_exp ``0xFFFFFFFFw:word64``, il, t_curr)
	else if is_Bit16 bir_exp_type_tm then
	    (resize_mil_exp ``0xFFFFw:word64``, il, t_curr)
	else if is_Bit8 bir_exp_type_tm then
	    (resize_mil_exp ``0xFFw:word64``, il, t_curr)
	else if is_Bit1 bir_exp_type_tm then
	    (resize_mil_exp ``0x1w:word64``, il, t_curr)
	else
	    ex_f_binexp exp
    end	
and bir_binpred_to_mil_e reg_map exp t_curr =
  let
    val (bipred_type, op1, op2) = dest_BExp_BinPred exp
    val (mil_op1, il1, t_curr) = bir_exp_to_mil_e reg_map op1 t_curr
    val (mil_op2, il2, t_curr) = bir_exp_to_mil_e reg_map op2 t_curr
    val ex_f_binpred = ex_f "bir_binpred_to_mil"
  in
    if is_BIExp_Equal bipred_type then
      (mk_e_eq (mil_op1, mil_op2), il1@il2, t_curr)
    else if is_BIExp_NotEqual bipred_type then
      (mk_e_neq (mil_op1, mil_op2), il1@il2, t_curr)
    else if is_BIExp_LessThan bipred_type then
      (mk_e_lt (mil_op1, mil_op2), il1@il2, t_curr)
    else if is_BIExp_SignedLessThan bipred_type then
      (mk_e_slt (mil_op1, mil_op2), il1@il2, t_curr)
    else if is_BIExp_LessOrEqual bipred_type then
      (mk_e_le (mil_op1, mil_op2), il1@il2, t_curr)
    else if is_BIExp_SignedLessOrEqual bipred_type then
      (mk_e_sle (mil_op1, mil_op2), il1@il2, t_curr)
    else
      ex_f_binpred exp
  end
and bir_load_to_mil_e reg_map exp t_curr =
  let
    val (expm, expad, expi, sz) = dest_BExp_Load exp
    val (expad_e, il1, t_curr) = bir_exp_to_mil_e reg_map expad t_curr
    val (t_eval, i_eval, t_curr) =
	build_mil_instr guard_true_tm (mk_o_internal expad_e) t_curr
    val (t_load, i_load, t_curr) =
	build_mil_instr guard_true_tm (mk_o_load (res_MEM_tm, t_eval)) t_curr
    val (t_resize32, i_resize32, t_curr32) =
	build_mil_instr guard_true_tm
	(mk_o_internal (mk_e_and (mk_e_name t_load, mk_e_val ``0xFFFFFFFFw:word64``))) t_curr
    val ex_f_load = ex_f "bir_load_to_mil"
  in
    if is_BExp_Den_Mem expm andalso
       is_BEnd_LittleEndian expi andalso
       is_Bit64 sz then
	(mk_e_name t_load, il1@[i_eval, i_load], t_curr)
    else if is_BExp_Den_Mem expm andalso
	    is_BEnd_LittleEndian expi andalso
	    is_Bit32 sz then
	(mk_e_name t_resize32, il1@[i_eval, i_load, i_resize32], t_curr32)	
    else ex_f_load exp
  end
and bir_store_to_mil_e reg_map exp t_curr =
  let
    val (expm, expad, expi, expv) = dest_BExp_Store exp
    val (expad_e, il1, t_curr) = bir_exp_to_mil_e reg_map expad t_curr
    val (expv_e, il2, t_curr) = bir_exp_to_mil_e reg_map expv t_curr
    val (t_evalad, i_evalad, t_curr) =
     build_mil_instr guard_true_tm (mk_o_internal expad_e) t_curr
    val (t_evalv, i_evalv, t_curr) =
     build_mil_instr guard_true_tm (mk_o_internal expv_e) t_curr
    val (t_store, i_store, t_curr) =
     build_mil_instr guard_true_tm (mk_o_store (res_MEM_tm, t_evalad, t_evalv)) t_curr
    val ex_f_store = ex_f "bir_store_to_mil"
  in
    if is_BExp_Den_Mem expm andalso is_BEnd_LittleEndian expi then
      (mk_e_name t_store, il1@il2@[i_evalad, i_evalv, i_store], t_curr)
    else ex_f_store exp
  end
and bir_cast_to_mil_e reg_map exp t_curr =
    let
	val (bicast_type, exp1, sz) = dest_BExp_Cast exp
	val (mil_exp1, il1, t_curr) = bir_exp_to_mil_e reg_map exp1 t_curr	
	val ex_f_cast = ex_f "bir_cast_to_mil"
    in
	if is_BIExp_LowCast bicast_type orelse is_BIExp_UnsignedCast bicast_type then
	    (if is_Bit64 sz then
		 (mil_exp1, il1, t_curr)
	     else if is_Bit32 sz then
		 (mk_e_and (mil_exp1, mk_e_val ``0xFFFFFFFFw:word64``), il1, t_curr)
	     else if is_Bit16 sz then
		 (mk_e_and (mil_exp1, mk_e_val ``0xFFFFw:word64``), il1, t_curr)
	     else if is_Bit8 sz then
		 (mk_e_and (mil_exp1, mk_e_val ``0xFFw:word64``), il1, t_curr)
             else if is_Bit1 sz then
		 (mk_e_and (mil_exp1, mk_e_val ``0x1w:word64``), il1, t_curr)
	     else ex_f_cast exp)
	else ex_f_cast exp
    end
;

(* Obtains a list with SML string names of all BIR variables of
 * a BIR expression *)
local
  fun find_bir_regnames' exp =
    if is_BExp_Den exp then
      [fst (dest_BVar_string (dest_BExp_Den exp))]
    else if (can strip_comb exp) then
      let
        val stms = snd (strip_comb exp)
        val sexps = filter (fn tm => type_of tm = bir_exp_t_ty) stms
      in
        foldl (fn (exp, it) => ((find_bir_regnames' exp)@it)) [] sexps
      end
    else []
in
  fun find_bir_regnames exp = rem_dup (find_bir_regnames' exp)
end
;

(* Constructs a SML list of terms with MIL microinstructions for loading
 * the values of all unloaded variables in a BIR expression *)
fun update_map_instr_l (reg_addr_map, reg_val_map) instr_l t_curr l =
  case l of
    [] => (reg_addr_map, reg_val_map, instr_l, t_curr)
  | reg_name::l' =>
    if reg_name = bir_mem_name then
      update_map_instr_l (reg_addr_map, reg_val_map) instr_l t_curr l'
    else
      let
        val reg_var = mk_var (reg_name, mil_val_ty)
        val (t_ass1, i_ass1, t_curr) =
         build_mil_instr guard_true_tm (mk_o_internal (mk_e_val reg_var)) t_curr
        val (t_ass2, i_ass2, t_curr) =
         build_mil_instr guard_true_tm (mk_o_load (res_REG_tm, t_ass1)) t_curr
        val reg_addr_map' =
         Redblackmap.insert (reg_addr_map, reg_name, t_ass1)
        val reg_val_map' =
         Redblackmap.insert (reg_val_map, reg_name, t_ass2)
      in
        update_map_instr_l (reg_addr_map', reg_val_map')
         (instr_l@[i_ass1, i_ass2]) t_curr l'
      end
;

(* Constructs a SML list of terms with MIL microinstructions corresponding
 * to a BIR basic statement *)
fun bir_bstmt_to_mil_instrs bstmt (reg_addr_map, reg_val_map) t_curr =
  if is_BStmt_Assign bstmt then
    let
      val (var, exp) = dest_BStmt_Assign bstmt
      (* 1. Fix MIL loads of regnames + maps of BIR variable names to 
       *    (parametrized) MIL names *)
      val regnames = find_bir_regnames exp
      (* TODO: Check so that you don't make MIL instructions for bir vars already loaded? *)
      val (reg_addr_map2, reg_val_map2, instr_l, t_curr) =
       update_map_instr_l (reg_addr_map, reg_val_map) [] t_curr regnames
      (* 2. MIL microinstruction with assignment expression + MIL store *)
      val (mil_exp, il, t_curr) = bir_exp_to_mil_e reg_val_map2 exp t_curr
      val (t_ass_exp, i_ass_exp, t_curr) =
       build_mil_instr guard_true_tm (mk_o_internal mil_exp) t_curr
      val assignee_name = (fst o dest_BVar_string) var
      val instr_l2 = instr_l@il@[i_ass_exp]
    in
      if assignee_name = bir_mem_name then
        (reg_addr_map2, reg_val_map2, t_curr, instr_l2)
      else
        let
          (* Make MIL microinstruction setting addr of assignee, if this does not
           * already exist *)
          val reg_val_map3 =
           Redblackmap.insert (reg_val_map2, assignee_name, t_ass_exp)
          val (reg_addr_map3, instr_l3, t_curr) =
           if isSome (Redblackmap.peek (reg_addr_map2, assignee_name)) then
             (reg_addr_map2, instr_l2, t_curr)
           else
             let
               val ass_var = mk_var (assignee_name, mil_val_ty)
               val (t_ass_addr, i_ass_addr, t_curr) =
                build_mil_instr guard_true_tm
                 (mk_o_internal (mk_e_val ass_var)) t_curr
               val new_reg_addr_map =
                Redblackmap.insert (reg_addr_map2, assignee_name, t_ass_addr)
              in
                (new_reg_addr_map, instr_l2@[i_ass_addr], t_curr)
              end
          (* 2. MIL microinstruction with store of assignee *)
          val (t_ass_st, i_ass_st, t_curr) =
           build_mil_instr guard_true_tm
            (mk_o_store (res_REG_tm,
              Redblackmap.find (reg_addr_map3, assignee_name),
              t_ass_exp)) t_curr
        in
	  (reg_addr_map3, reg_val_map3, t_curr, instr_l3@[i_ass_st])
        end
    end
  else if is_BStmt_Assert bstmt then (* TODO: track assertion results *)
    (reg_addr_map, reg_val_map, t_curr, [])
  else
    ex_f "bir_bstmt_to_mil_instrs" bstmt
;

(* Constructs a SML list of terms with MIL microinstructions corresponding
 * to a list of BIR basic statements *)
local
  fun bir_bstmts_to_mil_instrs' l (reg_addr_map, reg_val_map) t_curr instr_l =
    case l of
      [] => (reg_addr_map, reg_val_map, t_curr, instr_l)
    | h_bstmt::t_bstmts =>
      let
        val (reg_addr_map2, reg_val_map2, t_curr, instr_l_new) =
          bir_bstmt_to_mil_instrs h_bstmt (reg_addr_map, reg_val_map) t_curr
      in
        bir_bstmts_to_mil_instrs' t_bstmts (reg_addr_map2, reg_val_map2) t_curr (instr_l@instr_l_new)
      end
in
  fun bir_bstmts_to_mil_instrs bstmts (reg_addr_map, reg_val_map) t_curr =
    bir_bstmts_to_mil_instrs' bstmts (reg_addr_map, reg_val_map) t_curr []
end
;

(* Constructs a SML list of terms with MIL microinstructions for updating PC
 * after execution of a BIR block *)
fun bir_estmt_to_mil_instrs estmt (reg_addr_map, reg_val_map) t_curr label =
  if is_BStmt_Jmp estmt then
    (if is_BLE_Label (dest_BStmt_Jmp estmt) then
    let
      (* 1. MIL microinstruction assigning PC address to name *)
      val (t_pc_addr, i_pc_addr, t_curr) =
       build_mil_instr guard_true_tm (mk_o_internal (mk_e_val v_zero_tm)) t_curr
      (* 2. MIL microinstruction loading value of PC *)
      val (t_ld_pc, i_ld_pc, t_curr) =
       build_mil_instr guard_true_tm (mk_o_load (res_PC_tm, t_pc_addr)) t_curr
      (* 3. MIL microinstruction modifying PC according to the difference between current and next block *)
      val curr_bir_addr = (uint_of_word o bir_imm_to_mil_v o dest_BL_Address) label
      val bir_jump_target =
       (uint_of_word o bir_imm_to_mil_v o dest_BL_Address o dest_BLE_Label o dest_BStmt_Jmp) estmt
      val e_pc_val = mk_e_name t_ld_pc
      val o_inc_pc =
       mk_o_internal
        (if bir_jump_target > curr_bir_addr then
           mk_e_add (e_pc_val,
            mk_e_val (mk_wordii ((bir_jump_target - curr_bir_addr), 64)))
         else
           mk_e_sub (e_pc_val,
            mk_e_val (mk_wordii ((curr_bir_addr - bir_jump_target), 64))))
      val (t_inc_pc, i_inc_pc, t_curr) =
       build_mil_instr guard_true_tm o_inc_pc t_curr
      (* 4. MIL microinstruction storing updated value of PC *)
      val (t_st_pc, i_st_pc, t_curr) =
       build_mil_instr guard_true_tm (mk_o_store (res_PC_tm, t_pc_addr, t_inc_pc)) t_curr
    in
      [i_pc_addr, i_ld_pc, i_inc_pc, i_st_pc]
    end
    else if is_BLE_Exp (dest_BStmt_Jmp estmt) then
    let
      val jump_target_ep = dest_BLE_Exp (dest_BStmt_Jmp estmt)
      val regnames = find_bir_regnames jump_target_ep
      val (reg_addr_map2, reg_val_map2, instr_l, t_curr) =
       update_map_instr_l (reg_addr_map, reg_val_map) [] t_curr regnames
      val (t_pc_addr, i_pc_addr, t_curr) =
       build_mil_instr guard_true_tm (mk_o_internal (mk_e_val v_zero_tm)) t_curr
      val (t_ld_pc, i_ld_pc, t_curr) =
       build_mil_instr guard_true_tm (mk_o_load (res_PC_tm, t_pc_addr)) t_curr
      val v_curr_bir_addr = (mk_e_val o bir_imm_to_mil_v o dest_BL_Address) label
      val (mil_exp, il, t_curr) = bir_exp_to_mil_e reg_val_map2 jump_target_ep t_curr
      val (t_eval_target, i_eval_target, t_curr) =
       build_mil_instr guard_true_tm (mk_o_internal mil_exp) t_curr
      val e_target_val = mk_e_name t_eval_target
      val (t_comp_target, i_comp_target, t_curr) =
       build_mil_instr guard_true_tm (mk_o_internal (mk_e_lt (v_curr_bir_addr, e_target_val))) t_curr
      val e_comp_target = mk_e_name t_comp_target
      val e_pc_val = mk_e_name t_ld_pc
      val (t_jump_t, i_jump_t, t_curr) =
       build_mil_instr e_comp_target (mk_o_internal (mk_e_add (e_pc_val, mk_e_sub (e_target_val, v_curr_bir_addr)))) t_curr
      val (t_st_pc_t, i_st_pc_t, t_curr) =
       build_mil_instr e_comp_target (mk_o_store (res_PC_tm, t_pc_addr, t_jump_t)) t_curr
      val (t_jump_f, i_jump_f, t_curr) =
       build_mil_instr (mk_e_comp e_comp_target) (mk_o_internal (mk_e_sub (e_pc_val, mk_e_sub (v_curr_bir_addr, e_target_val)))) t_curr
      val (t_st_pc_f, i_st_pc_f, t_curr) =
       build_mil_instr (mk_e_comp e_comp_target) (mk_o_store (res_PC_tm, t_pc_addr, t_jump_f)) t_curr
     in
       instr_l@il@[i_pc_addr, i_ld_pc, i_eval_target, i_comp_target, i_jump_t, i_st_pc_t, i_jump_f, i_st_pc_f]
    end
    else ex_f "bir_estmt_to_mil_instrs" estmt)
  else if is_BStmt_CJmp estmt then
    let
      val (ec, l1, l2) = dest_BStmt_CJmp estmt
      val regnames = find_bir_regnames ec
      val (reg_addr_map2, reg_val_map2, instr_l, t_curr) =
       update_map_instr_l (reg_addr_map, reg_val_map) [] t_curr regnames
      (* get the PC address and load currect PC value *)
      val (t_pc_addr, i_pc_addr, t_curr) =
       build_mil_instr guard_true_tm (mk_o_internal (mk_e_val v_zero_tm)) t_curr
      val (t_ld_pc, i_ld_pc, t_curr) =
       build_mil_instr guard_true_tm (mk_o_load (res_PC_tm, t_pc_addr)) t_curr
      (* translate the condition to MIL *)
      val (mil_exp, il, t_curr) = bir_exp_to_mil_e reg_val_map2 ec t_curr
      val (t_eval_cond, i_eval_cond, t_curr) =
       build_mil_instr guard_true_tm (mk_o_internal mil_exp) t_curr
      val e_ec_val = mk_e_name t_eval_cond
      (* jump target 1 *)
      val curr_bir_addr = (uint_of_word o bir_imm_to_mil_v o dest_BL_Address) label
      val bir_jump_target_1 =
       (uint_of_word o bir_imm_to_mil_v o dest_BL_Address o dest_BLE_Label) l1
      val e_pc_val = mk_e_name t_ld_pc
      val o_inc_pc_1 =
       mk_o_internal
         (if bir_jump_target_1 > curr_bir_addr then
            mk_e_add (e_pc_val,
             mk_e_val (mk_wordii ((bir_jump_target_1 - curr_bir_addr), 64)))
          else
            mk_e_sub (e_pc_val,
             mk_e_val (mk_wordii ((curr_bir_addr - bir_jump_target_1), 64))))
      val (t_inc_pc_1, i_inc_pc_1, t_curr) =
       build_mil_instr guard_true_tm o_inc_pc_1 t_curr
      val (t_st_pc_1, i_st_pc_1, t_curr) =
       build_mil_instr e_ec_val (mk_o_store (res_PC_tm, t_pc_addr, t_inc_pc_1)) t_curr
      (* jump target 2 *)
      val bir_jump_target_2 =
       (uint_of_word o bir_imm_to_mil_v o dest_BL_Address o dest_BLE_Label) l2
      val o_inc_pc_2 =
       mk_o_internal
	 (if bir_jump_target_2 > curr_bir_addr then
	    mk_e_add (e_pc_val,
             mk_e_val (mk_wordii ((bir_jump_target_2 - curr_bir_addr), 64)))
	  else
            mk_e_sub (e_pc_val,
             mk_e_val (mk_wordii ((curr_bir_addr - bir_jump_target_2), 64))))
      val (t_inc_pc_2, i_inc_pc_2, t_curr) =
       build_mil_instr guard_true_tm o_inc_pc_2 t_curr
      val (t_st_pc_2, i_st_pc_2, t_curr) =
       build_mil_instr guard_true_tm (mk_o_store (res_PC_tm, t_pc_addr, t_inc_pc_2)) t_curr
    in
      instr_l@il@[i_pc_addr, i_ld_pc, i_eval_cond, i_inc_pc_1, i_st_pc_1, i_inc_pc_2, i_st_pc_2]
    end
  else
    ex_f "bir_estmt_to_mil_instrs" estmt
;
  
fun bir_block_to_mil_instrs block =
  let
    (* 1. Destruct BIR block. Observation type is unused. *)
    val (_, label, bstmts, estmt) = dest_bir_block_list block
    (* 3. Destruct basic block, handle statements
     *    (assume one assign - otherwise pay forward map and last param) *)
    val reg_addr_map =
     (Redblackmap.mkDict String.compare):(string, term) Redblackmap.dict
    val reg_val_map =
     (Redblackmap.mkDict String.compare):(string, term) Redblackmap.dict
    val t_initial = instr_var
    (* first instruction must be greater than initial *)
    val t_curr = tm_plus_eval t_initial 1
    val (reg_addr_map2, reg_val_map2, t_curr, instr_l_ass) =
      bir_bstmts_to_mil_instrs bstmts (reg_addr_map, reg_val_map) t_curr
    (* 4. Construct PC adjustment based on jump *)
    (* NOTE: this assumes "pc" is not manipulated by basic BIR block -
     * OK since PC is handled separately in BIR *)
    val instr_l_pc = bir_estmt_to_mil_instrs estmt (reg_addr_map2, reg_val_map2) t_curr label
    (* 5. Construct function mapping label to i_assign set *)
    (* Address of block as word *)
    val addr = (bir_imm_to_mil_v o dest_BL_Address) label
    (* NOTE: All variables of entire program must be obtained as
     *       arguments to the function defined in bir_prog_to_mil_iset.
     *       Different blocks cannot have different arguments. *)
    val bir_vars_l = map fst (Redblackmap.listItems reg_val_map2)
    (* SML list of the MIL microinstructions *)
    val instr_l = instr_l_ass@instr_l_pc
  in
    (instr_l, addr, bir_vars_l)
  end
;

local
  fun bir_blocks_to_mil_instrs' l bir_vars_l addr_instr_l =
    case l of
      [] => (bir_vars_l, addr_instr_l)
    | h_block::t_blocks =>
      let
        val (instr_l, addr, bir_vars_l_new) = bir_block_to_mil_instrs h_block
      in
        bir_blocks_to_mil_instrs' t_blocks (bir_vars_l@bir_vars_l_new) (addr_instr_l@[(addr, instr_l)])
      end
in
  fun bir_blocks_to_mil_instrs blocks =
    let
      val (bir_vars_l, addr_instr_l) = bir_blocks_to_mil_instrs' blocks [] []
    in
      (rem_dup bir_vars_l, addr_instr_l)
    end
end
;

fun make_func_conjunct func_lhs_base_tm mk_target (addr, i_target) =
  let
    val func_lhs_tm = mk_comb (mk_comb (func_lhs_base_tm, addr), instr_var)
    val func_rhs_tm = mk_target (i_target, i_ty)
  in
    mk_eq (func_lhs_tm, func_rhs_tm)
  end
;

fun make_func_conjuncts func_name bir_vars_l addr_instr_l target_ty mk_target =
  let
    val mil_val_tys_l = List.tabulate (length bir_vars_l, (fn x => mil_val_ty))
    val func_ty = list_mk_fun (mil_val_tys_l@[mil_val_ty,num], target_ty)
    val func_name_tm = mk_var (func_name, func_ty)
    val mil_vars_l = map (fn vname => mk_var (vname, mil_val_ty)) bir_vars_l
    val func_lhs_base_tm = list_mk_comb (func_name_tm, mil_vars_l)
  in
    list_mk_conj (map (make_func_conjunct func_lhs_base_tm mk_target) addr_instr_l)
  end
;

fun make_ilist_func_conjuncts func_name bir_vars_l addr_instr_l =
  make_func_conjuncts func_name bir_vars_l addr_instr_l ilist_ty mk_list;

fun make_iset_func_conjuncts func_name bir_vars_l addr_instr_l =
  make_func_conjuncts func_name bir_vars_l addr_instr_l iset_ty prim_mk_set;

(* Takes a BIR program and a string function name, then
 * defines a function in HOL with that name mapping
 * BIR block addresses (and other necessary parameters)
 * to sets of MIL microinstructions.
 * This is parametrized in terms of the function that creates the
 * term with conjuncts from every transformed instruction. *)
fun bir_prog_to_mil prog func_name make_target_func_conjuncts =
  let
    (* 1. Destruct BIR prog. Observation type is unused. *)
    val (_, blocks) = dest_BirProgram_list prog
    (* 2. Perform the action: obtain a list of BIR variables
     *    used in the blocks, as well as tuples of addresses
     *    and SML lists of MIL microinstructions resulting
     *    from translation of the blocks. *)
    (* NOTE: All variables of entire program must be obtained as
     *       arguments to the function. Different blocks cannot have
     *       different arguments. *)
    (* TODO: Try/catch printingx error/success messages *)
    val (bir_vars_l, addr_instr_l) = bir_blocks_to_mil_instrs blocks
    (* 3. Make HOL term of function mapping label to i_assign set
          func arguments are: pc, [regs], i (name parameter), addr *)
    val func_tm = make_target_func_conjuncts func_name bir_vars_l addr_instr_l
    (* 4. Perform the HOL definition *)
    val def = Defn.mk_defn func_name func_tm
    val def_thm = GEN_ALL (el 1 (Defn.eqns_of def))
    val _ = save_thm (func_name, def_thm)
    val _ = computeLib.add_thms [def_thm] computeLib.the_compset
  in
    def_thm
  end
;

(* Set wrapper for bir_prog_to_mil *)
fun bir_prog_to_mil_iset prog func_name =
  bir_prog_to_mil prog func_name make_iset_func_conjuncts
;

(* List wrapper for bir_prog_to_mil *)
fun bir_prog_to_mil_ilist prog func_name =
  bir_prog_to_mil prog func_name make_ilist_func_conjuncts
;

end
