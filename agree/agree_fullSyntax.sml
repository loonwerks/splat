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

val AERR = C (mk_HOL_ERR "agree_fullSyntax") "";

val dest_Var = dest_monop Var_const (AERR "dest_Var")
val dest_IntLit = dest_monop IntLit_const (AERR "dest_IntLit")
val dest_BoolLit = dest_monop BoolLit_const (AERR "dest_BoolLit")
val dest_Not = dest_monop Not_const (AERR "dest_Not")
val dest_Pre = dest_monop Pre_const (AERR "dest_Pre")
val dest_Hist = dest_monop Hist_const (AERR "dest_Hist")
val dest_Add = dest_binop Add_const (AERR "dest_Add")
val dest_Sub = dest_binop Sub_const (AERR "dest_Sub")
val dest_Mult = dest_binop Mult_const (AERR "dest_Mult")
val dest_Div = dest_binop Div_const (AERR "dest_Div")
val dest_Mod = dest_binop Mod_const (AERR "dest_Mod")
val dest_Or = dest_binop Or_const (AERR "dest_Or")
val dest_And = dest_binop And_const (AERR "dest_And")
val dest_Imp = dest_binop Imp_const (AERR "dest_Imp")
val dest_Iff = dest_binop Iff_const (AERR "dest_Iff")
val dest_Eq = dest_binop Eq_const (AERR "dest_Eq")
val dest_Leq = dest_binop Leq_const (AERR "dest_Leq")
val dest_Lt = dest_binop Lt_const (AERR "dest_Lt")
val dest_RecdProj = dest_binop RecdProj_const (AERR "dest_RecdProj")
val dest_ArraySub = dest_binop ArraySub_const (AERR "dest_ArraySub")
val dest_PortEvent = dest_monop PortEvent_const (AERR "dest_PortEvent")
val dest_PortData  = dest_monop PortData_const (AERR "dest_PortData")
val dest_Fby = dest_binop Fby_const (AERR "dest_Fby")
val dest_Cond = dest_triop Cond_const (AERR "dest_Cond")
val dest_Recd = dest_monop Recd_const (AERR "dest_Recd")
val dest_Array = dest_monop Array_const (AERR "dest_Array")
val dest_stmt = dest_binop Stmt_const (AERR "dest_stmt")
val dest_output_data = dest_binop Output_Data_const (AERR "dest_output_data")
val dest_output_event = dest_binop Output_Event_const (AERR "dest_output_event")
val dest_output_event_data = dest_triop Output_Event_Data_const (AERR "dest_output_event_data")

datatype port
  = Data of term
  | Event_Only of term
  | Event_Data of term * term

fun dest_component tm =
 let open listSyntax stringSyntax
     fun dest_strings tm = map fromHOLstring (fst(dest_list tm))
     fun dest_var_def tm =
       let val (t1,t2) = dest_stmt tm
       in (fromHOLstring t1, t2)
       end
     fun dest_var_defs tm = map dest_var_def (fst(dest_list tm))
     fun dest_out_def tm =
       case total dest_output_data tm
         of SOME (oport,e) => (fromHOLstring oport, Data e)
          | NONE =>
       case total dest_output_event tm
         of SOME (oport,e) => (fromHOLstring oport,Event_Only e)
          | NONE =>
       case total dest_output_event_data tm
        of SOME (oport,e1,e2) => (fromHOLstring oport, Event_Data (e1,e2))
         | NONE => raise AERR "dest_component(dest_out_def)"
     fun dest_out_defs tm = map dest_out_def (fst(dest_list tm))
 in case Lib.total TypeBase.dest_record tm
     of NONE => raise AERR "dest_component"
      | SOME (ty,
          [("inports", inports),
           ("var_defs",var_defs),
	   ("out_defs", out_defs),
	   ("assumptions", assums),
	   ("guarantees", guars)]) =>
        if ty = component_ty
        then (("inports", dest_strings inports),
	      ("var_defs",dest_var_defs var_defs),
              ("out_defs", dest_out_defs out_defs),
              ("assumptions", fst(dest_list assums)),
              ("guarantees", fst (dest_list guars)))
        else raise AERR "dest_component"
  end

end
