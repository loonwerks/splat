signature agree_fullSyntax =
sig

  include Abbrev

  val expr_ty : hol_type
  val component_ty : hol_type

  val mk_Var : term -> term
  val mk_IntLit : term -> term
  val mk_BoolLit : term -> term
  val mk_Add : term * term -> term
  val mk_And : term * term -> term
  val mk_ArraySub : term * term -> term
  val mk_Cond : term * term * term -> term
  val mk_Div : term * term -> term
  val mk_Eq : term * term -> term
  val mk_Fby : term * term -> term
  val mk_Hist : term -> term
  val mk_Iff : term * term -> term
  val mk_Imp : term * term -> term
  val mk_Leq : term * term -> term
  val mk_Lt : term * term -> term
  val mk_Mod : term * term -> term
  val mk_Mult : term * term -> term
  val mk_Not : term -> term
  val mk_Or : term * term -> term
  val mk_PortData : term -> term
  val mk_PortEvent : term -> term
  val mk_Pre : term -> term
  val mk_RecdProj : term * term -> term
  val mk_Sub : term * term -> term
  val mk_Array : term -> term
  val mk_Recd : term -> term

  val mk_stmt : term * term -> term

  val mk_output_data : term * term -> term
  val mk_output_event : term * term -> term
  val mk_output_event_data : term * term * term -> term

  val mk_component : (string * term) list -> term
end