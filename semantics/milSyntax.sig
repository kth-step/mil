signature milSyntax =
sig
   include Abbrev

   (*******)
   (* res *)
   (*******)

   val res_ty : hol_type
   
   val res_PC_tm  : term
   val res_REG_tm : term
   val res_MEM_tm : term

   (*****)
   (* v *)
   (*****)

   val v_ty : hol_type

   val v_false_tm : term
   val v_true_tm : term
   val v_zero_tm : term
   val v_one_tm : term
   val v_four_tm : term

   (*****)
   (* e *)
   (*****)

   val e_ty : hol_type

   val e_val_tm   : term
   val mk_e_val   : term -> term
   val dest_e_val : term -> term
   val is_e_val   : term -> bool

   val e_name_tm   : term
   val mk_e_name   : term -> term
   val dest_e_name : term -> term
   val is_e_name   : term -> bool

   val e_and_tm    : term
   val mk_e_and    : term * term -> term
   val dest_e_and  : term -> term * term
   val is_e_and    : term -> bool

   val e_or_tm    : term
   val mk_e_or    : term * term -> term
   val dest_e_or  : term -> term * term
   val is_e_or    : term -> bool

   val e_xor_tm    : term
   val mk_e_xor    : term * term -> term
   val dest_e_xor  : term -> term * term
   val is_e_xor    : term -> bool

   val e_add_tm    : term
   val mk_e_add    : term * term -> term
   val dest_e_add  : term -> term * term
   val is_e_add    : term -> bool

   val e_sub_tm    : term
   val mk_e_sub    : term * term -> term
   val dest_e_sub  : term -> term * term
   val is_e_sub    : term -> bool

   val e_mul_tm    : term
   val mk_e_mul    : term * term -> term
   val dest_e_mul  : term -> term * term
   val is_e_mul    : term -> bool

   val e_div_tm    : term
   val mk_e_div    : term * term -> term
   val dest_e_div  : term -> term * term
   val is_e_div    : term -> bool

   val e_sdiv_tm    : term
   val mk_e_sdiv    : term * term -> term
   val dest_e_sdiv  : term -> term * term
   val is_e_sdiv    : term -> bool

   val e_mod_tm    : term
   val mk_e_mod    : term * term -> term
   val dest_e_mod  : term -> term * term
   val is_e_mod    : term -> bool

   val e_smod_tm    : term
   val mk_e_smod    : term * term -> term
   val dest_e_smod  : term -> term * term
   val is_e_smod    : term -> bool

   val e_lsl_tm    : term
   val mk_e_lsl    : term * term -> term
   val dest_e_lsl  : term -> term * term
   val is_e_lsl    : term -> bool

   val e_lsr_tm    : term
   val mk_e_lsr    : term * term -> term
   val dest_e_lsr  : term -> term * term
   val is_e_lsr    : term -> bool

   val e_asr_tm    : term
   val mk_e_asr    : term * term -> term
   val dest_e_asr  : term -> term * term
   val is_e_asr    : term -> bool

   val e_eq_tm    : term
   val mk_e_eq    : term * term -> term
   val dest_e_eq  : term -> term * term
   val is_e_eq    : term -> bool

   val e_neq_tm    : term
   val mk_e_neq    : term * term -> term
   val dest_e_neq  : term -> term * term
   val is_e_neq    : term -> bool

   val e_lt_tm    : term
   val mk_e_lt    : term * term -> term
   val dest_e_lt  : term -> term * term
   val is_e_lt    : term -> bool

   val e_slt_tm    : term
   val mk_e_slt    : term * term -> term
   val dest_e_slt  : term -> term * term
   val is_e_slt    : term -> bool

   val e_le_tm    : term
   val mk_e_le    : term * term -> term
   val dest_e_le  : term -> term * term
   val is_e_le    : term -> bool

   val e_sle_tm    : term
   val mk_e_sle    : term * term -> term
   val dest_e_sle  : term -> term * term
   val is_e_sle    : term -> bool

   val e_comp_tm   : term
   val mk_e_comp   : term -> term
   val dest_e_comp : term -> term
   val is_e_comp   : term -> bool

   val e_not_tm   : term
   val mk_e_not   : term -> term
   val dest_e_not : term -> term
   val is_e_not   : term -> bool

   (******)
   (* op *)
   (******)   

   val op_ty : hol_type

   val o_internal_tm   : term
   val dest_o_internal : term -> term
   val is_o_internal   : term -> bool
   val mk_o_internal   : term -> term

   val o_load_tm   : term
   val dest_o_load : term -> term * term
   val is_o_load   : term -> bool
   val mk_o_load   : term * term -> term

   val o_store_tm   : term
   val dest_o_store : term -> term * term * term
   val is_o_store   : term -> bool
   val mk_o_store   : term * term * term -> term


   (*****)
   (* i *)
   (*****)

   val i_ty : hol_type

   val i_assign_tm   : term
   val dest_i_assign : term -> term * term * term
   val is_i_assign   : term -> bool
   val mk_i_assign   : term * term * term -> term

end
