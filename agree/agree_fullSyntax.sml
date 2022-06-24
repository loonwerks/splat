structure agree_fullSyntax :> agree_fullSyntax =
struct

local open agree_fullTheory in end

open HolKernel boolLib;

val expr_ty = mk_thy_type{Thy="agree_full", Tyop = "expr", Args = []};
val component_ty = mk_thy_type{Thy="agree_full", Tyop="component", Args=[]};

(*---------------------------------------------------------------------------*)
(* Expressions                                                               *)
(*---------------------------------------------------------------------------*)

fun agree_const s = prim_mk_const{Thy = "agree_full", Name = s};

val Var_const = agree_const "VarExpr"
val IntLit_const = agree_const "IntLit";
val BoolLit_const = agree_const "BoolLit";
val Not_const = agree_const "NotExpr";
val Pre_const = agree_const "PreExpr";
val Hist_const = agree_const "HistExpr";
val Add_const = agree_const "AddExpr";
val Sub_const = agree_const "SubExpr";
val Mult_const = agree_const "MultExpr";
val Div_const = agree_const "DivExpr";
val Mod_const = agree_const "ModExpr";
val Or_const = agree_const "OrExpr";
val And_const = agree_const "AndExpr";
val Imp_const = agree_const "ImpExpr";
val Iff_const = agree_const "IffExpr";
val Eq_const = agree_const "EqExpr";
val Leq_const = agree_const "LeqExpr";
val Lt_const = agree_const "LtExpr";
val Recd_const = agree_const "RecdExpr";
val RecdProj_const = agree_const "RecdProj";
val Array_const = agree_const "ArrayExpr";
val ArraySub_const = agree_const "ArraySub";
val PortEvent_const = agree_const "PortEvent";
val PortData_const = agree_const "PortData";
val Fby_const = agree_const "FbyExpr";
val Cond_const = agree_const "CondExpr";
val eventOf_const = agree_const "eventOf";
val dataOf_const = agree_const "dataOf";
val component_const = agree_const "recordtype.component";
val Stmt_const = agree_const "Stmt";
val Output_Data_const = agree_const "Output_Data";
val Output_Event_const = agree_const "Output_Event";
val Output_Event_Data_const = agree_const "Output_Event_Data";


val mk_Var = mk_monop Var_const
val mk_IntLit = mk_monop IntLit_const
val mk_BoolLit = mk_monop BoolLit_const
val mk_Not = mk_monop Not_const
val mk_Pre = mk_monop Pre_const
val mk_Hist = mk_monop Hist_const
val mk_Add = mk_binop Add_const
val mk_Sub = mk_binop Sub_const
val mk_Mult = mk_binop Mult_const
val mk_Div = mk_binop Div_const
val mk_Mod = mk_binop Mod_const
val mk_Or = mk_binop Or_const
val mk_And = mk_binop And_const
val mk_Imp = mk_binop Imp_const
val mk_Iff = mk_binop Iff_const
val mk_Eq = mk_binop Eq_const
val mk_Leq = mk_binop Leq_const
val mk_Lt = mk_binop Lt_const

val mk_RecdProj = mk_binop RecdProj_const
val mk_ArraySub = mk_binop ArraySub_const
val mk_PortEvent = mk_monop PortEvent_const
val mk_PortData  = mk_monop PortData_const
val mk_Fby = mk_binop Fby_const
val mk_Cond = mk_triop Cond_const;

val mk_Recd = mk_monop Recd_const
val mk_Array = mk_monop Array_const;

val mk_stmt = mk_binop Stmt_const;
val mk_output_data = mk_binop Output_Data_const;
val mk_output_event = mk_binop Output_Event_const;
val mk_output_event_data = mk_triop Output_Event_Data_const;

fun mk_component fields = TypeBase.mk_record(component_ty, fields)

end
