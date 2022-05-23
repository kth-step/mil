structure milSyntax :> milSyntax =
struct

open HolKernel boolLib liteLib simpLib Parse bossLib milTheory;

(* res *)

val res_ty = mk_type ("res", []);

val res_PC_tm = prim_mk_const {Name="res_PC", Thy="mil"};
val res_REG_tm = prim_mk_const {Name="res_REG", Thy="mil"};
val res_MEM_tm = prim_mk_const {Name="res_MEM", Thy="mil"};

(* v *)

local
  fun mk_word_type ty =
    fcpSyntax.mk_cart_type (Type.bool, ty)
  val mk_int_word_type =
    mk_word_type o fcpSyntax.mk_int_numeric_type
in
  val v_ty = mk_int_word_type 64
end
;

val v_false_tm = prim_mk_const {Name="val_false", Thy="mil"};
val v_true_tm = prim_mk_const {Name="val_true", Thy="mil"};
val v_zero_tm = prim_mk_const {Name="val_zero", Thy="mil"};
val v_one_tm = prim_mk_const {Name="val_one", Thy="mil"};
val v_four_tm = prim_mk_const {Name="val_four", Thy="mil"};

(* e *)

val e_ty = mk_type ("e", []);

val (e_val_tm, mk_e_val, dest_e_val, is_e_val) =
 syntax_fns1 "mil" "e_val";
val (e_name_tm, mk_e_name, dest_e_name, is_e_name) =
 syntax_fns1 "mil" "e_name";
val (e_and_tm, mk_e_and, dest_e_and, is_e_and) =
 syntax_fns2 "mil" "e_and";
val (e_or_tm, mk_e_or, dest_e_or, is_e_or) =
 syntax_fns2 "mil" "e_or";
val (e_xor_tm, mk_e_xor, dest_e_xor, is_e_xor) =
 syntax_fns2 "mil" "e_xor";
val (e_add_tm, mk_e_add, dest_e_add, is_e_add) =
 syntax_fns2 "mil" "e_add";
val (e_sub_tm, mk_e_sub, dest_e_sub, is_e_sub) =
 syntax_fns2 "mil" "e_sub";
val (e_mul_tm, mk_e_mul, dest_e_mul, is_e_mul) =
 syntax_fns2 "mil" "e_mul";
val (e_div_tm, mk_e_div, dest_e_div, is_e_div) =
 syntax_fns2 "mil" "e_div";
val (e_sdiv_tm, mk_e_sdiv, dest_e_sdiv, is_e_sdiv) =
 syntax_fns2 "mil" "e_sdiv";
val (e_mod_tm, mk_e_mod, dest_e_mod, is_e_mod) =
 syntax_fns2 "mil" "e_mod";
val (e_smod_tm, mk_e_smod, dest_e_smod, is_e_smod) =
 syntax_fns2 "mil" "e_smod";
val (e_lsl_tm, mk_e_lsl, dest_e_lsl, is_e_lsl) =
 syntax_fns2 "mil" "e_lsl";
val (e_lsr_tm, mk_e_lsr, dest_e_lsr, is_e_lsr) =
 syntax_fns2 "mil" "e_lsr";
val (e_asr_tm, mk_e_asr, dest_e_asr, is_e_asr) =
 syntax_fns2 "mil" "e_asr";
val (e_eq_tm, mk_e_eq, dest_e_eq, is_e_eq) =
 syntax_fns2 "mil" "e_eq";
val (e_neq_tm, mk_e_neq, dest_e_neq, is_e_neq) =
 syntax_fns2 "mil" "e_neq";
val (e_lt_tm, mk_e_lt, dest_e_lt, is_e_lt) =
 syntax_fns2 "mil" "e_lt";
val (e_slt_tm, mk_e_slt, dest_e_slt, is_e_slt) =
 syntax_fns2 "mil" "e_slt";
val (e_le_tm, mk_e_le, dest_e_le, is_e_le) =
 syntax_fns2 "mil" "e_le";
val (e_sle_tm, mk_e_sle, dest_e_sle, is_e_sle) =
 syntax_fns2 "mil" "e_sle";
val (e_comp_tm, mk_e_comp, dest_e_comp, is_e_comp) =
 syntax_fns1 "mil" "e_comp";
val (e_not_tm, mk_e_not, dest_e_not, is_e_not) =
 syntax_fns1 "mil" "e_not";

(* op *)

val op_ty = mk_type ("op", []);

val (o_internal_tm, mk_o_internal, dest_o_internal, is_o_internal) =
 syntax_fns1 "mil" "o_internal";
val (o_load_tm, mk_o_load, dest_o_load, is_o_load) =
 syntax_fns2 "mil" "o_load";
val (o_store_tm, mk_o_store, dest_o_store, is_o_store) =
 syntax_fns3 "mil" "o_store";

(* i *)

val i_ty = mk_type ("i", []);

val (i_assign_tm, mk_i_assign, dest_i_assign, is_i_assign) =
  syntax_fns3 "mil"  "i_assign";

end
