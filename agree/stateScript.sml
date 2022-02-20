open HolKernel Parse boolLib bossLib BasicProvers
     pred_setLib stringLib intLib finite_mapTheory
     arithmeticTheory listTheory pred_setTheory
     agreeTheory;

val _ = intLib.prefer_int();

val _ = new_theory "state";

(*---------------------------------------------------------------------------*)
(* Conventional notion of state, mapping from name to value. NB: since we    *)
(* are defining step-wise computation, the temporal operators Pre, Fby, and  *)
(* Hist are treated differently. Pre is treated as the identity function,    *)
(* and Fby is treated as a test on an implicit "_initStep" boolean stream,   *)
(* while Hist is not allowed in the syntax.                                  *)
(*---------------------------------------------------------------------------*)

Type value_env = “:string |-> value”

Definition updateState_def :
 updateState (fmap:value_env) name value = fmap |+ (name,value)
End

(*---------------------------------------------------------------------------*)
(* Map stream env to state                                                   *)
(*---------------------------------------------------------------------------*)

Definition strmIndex_def:
  strmIndex (E:string |-> (num -> value)) t = FMAP_MAP2 (\(s,strm). strm t) E
End

(*---------------------------------------------------------------------------*)
(* Custom size for expressions used in termination proof of evalue/bvalue    *)
(*---------------------------------------------------------------------------*)

Definition expr_sizeA_def :
  expr_sizeA (IntVar s) = 0n /\
  expr_sizeA (IntLit i) = 0  /\
  expr_sizeA (AddExpr e1 e2)  = 1 + expr_sizeA e1 + expr_sizeA e2 /\
  expr_sizeA (SubExpr e1 e2)  = 1 + expr_sizeA e1 + expr_sizeA e2 /\
  expr_sizeA (MultExpr e1 e2) = 1 + expr_sizeA e1 + expr_sizeA e2 /\
  expr_sizeA (DivExpr e1 e2)  = 1 + expr_sizeA e1 + expr_sizeA e2 /\
  expr_sizeA (ModExpr e1 e2)  = 1 + expr_sizeA e1 + expr_sizeA e2 /\
  expr_sizeA (CondExpr b x y) = 1 + bexpr_sizeA b + expr_sizeA x + expr_sizeA y   /\
  expr_sizeA (FbyExpr e1 e2)  = 1 + expr_sizeA e1 + expr_sizeA e2 /\
  expr_sizeA (PreExpr e)      = 1 + expr_sizeA e
  ∧
  bexpr_sizeA (BoolVar s)     = 0n /\
  bexpr_sizeA (BoolLit b)     = 0  /\
  bexpr_sizeA (NotExpr b)     = 1 + bexpr_sizeA b /\
  bexpr_sizeA (OrExpr b1 b2)  = 1 + bexpr_sizeA b1 + bexpr_sizeA b2 /\
  bexpr_sizeA (AndExpr b1 b2) = 1 + bexpr_sizeA b1 + bexpr_sizeA b2 /\
  bexpr_sizeA (ImpExpr b1 b2) = 1 + bexpr_sizeA b1 + bexpr_sizeA b2 /\
  bexpr_sizeA (IffExpr b1 b2) = 1 + bexpr_sizeA b1 + bexpr_sizeA b2 /\
  bexpr_sizeA (EqExpr e1 e2)  = 1 + expr_sizeA e1 + expr_sizeA e2 /\
  bexpr_sizeA (LtExpr e1 e2)  = 1 + expr_sizeA e1 + expr_sizeA e2 /\
  bexpr_sizeA (LeqExpr e1 e2) = 1 + expr_sizeA e1 + expr_sizeA e2 /\
  bexpr_sizeA (BoolCondExpr b b1 b2) = 1 + bexpr_sizeA b + bexpr_sizeA b1 + bexpr_sizeA b2 /\
  bexpr_sizeA (BoolFbyExpr b1 b2)    = 1 + bexpr_sizeA b1 + bexpr_sizeA b2 /\
  bexpr_sizeA (BoolPreExpr b) = 1 + bexpr_sizeA b /\
  bexpr_sizeA (HistExpr b)    = 0
End

Definition evalue_def :
  evalue E (IntVar s) = int_of (E ' s) /\
  evalue E (IntLit i) = i /\
  evalue E (AddExpr e1 e2)  = evalue E e1 + evalue E e2  /\
  evalue E (SubExpr e1 e2)  = evalue E e1 - evalue E e2  /\
  evalue E (MultExpr e1 e2) = evalue E e1 * evalue E e2 /\
  evalue E (DivExpr e1 e2)  = evalue E e1 / evalue E e2  /\
  evalue E (ModExpr e1 e2)  = evalue E e1 % evalue E e2  /\
  evalue E (CondExpr b e1 e2) = (if bvalue E b then evalue E e1 else evalue E e2) ∧
  evalue E (PreExpr e)      = evalue E e /\
  evalue E (FbyExpr e1 e2)  =
      (if bvalue E (BoolVar "isInit") then evalue E e1 else evalue E e2)
  /\
  bvalue E (BoolVar s)     = bool_of (E ' s) /\
  bvalue E (BoolLit b)     = b /\
  bvalue E (NotExpr b)     = (~bvalue E b) /\
  bvalue E (OrExpr b1 b2)  = (bvalue E b1 \/ bvalue E b2) /\
  bvalue E (AndExpr b1 b2) = (bvalue E b1 /\ bvalue E b2) /\
  bvalue E (ImpExpr b1 b2) = (bvalue E b1 ⇒ bvalue E b2) /\
  bvalue E (IffExpr b1 b2) = (bvalue E b1 = bvalue E b2) /\
  bvalue E (EqExpr e1 e2)  = (evalue E e1 = evalue E e2)   /\
  bvalue E (LtExpr e1 e2)  = (evalue E e1 < evalue E e2)   /\
  bvalue E (LeqExpr e1 e2) = (evalue E e1 <= evalue E e2)  /\
  bvalue E (BoolCondExpr b b1 b2) = (if bvalue E b then bvalue E b1 else bvalue E b2) ∧
  bvalue E (BoolPreExpr b) = bvalue E b /\
  bvalue E (BoolFbyExpr b1 b2) =
      (if bvalue E (BoolVar "isInit") then bvalue E b1 else bvalue E b2) ∧
  bvalue E (HistExpr b)    = ARB
Termination
  WF_REL_TAC ‘measure (sum_size (expr_sizeA o SND) (bexpr_sizeA o SND))’
  >> rw [expr_sizeA_def]
End

(*---------------------------------------------------------------------------*)
(* Meaning of variable definitions                                           *)
(*---------------------------------------------------------------------------*)

Definition defFn_def :
  defFn E (IntStmt s exp)   = updateState E s (IntValue(evalue E exp)) ∧
  defFn E (BoolStmt s bexp) = updateState E s (BoolValue(bvalue E bexp))
End

(*---------------------------------------------------------------------------*)
(* Sequential accumulation of variable updates.                              *)
(*---------------------------------------------------------------------------*)

Definition defListFn_def :
  defListFn E defs = FOLDL defFn E defs
End

(*---------------------------------------------------------------------------*)
(* Given inputs and a state, produce the new state and outputs               *)
(*                                                                           *)
(*   stateStep: component -> inputs # state -> state # outputs               *)
(*                                                                           *)
(* where inputs, state, and outputs are value environments (string |-> value)*)
(*---------------------------------------------------------------------------*)

Definition stateStep_def :
  stateStep comp (inE,stateE) =
  let E' = defListFn (FUNION inE stateE) (comp.var_defs ++ comp.out_defs) ;
  in (state_of comp E', output_of comp E')
End

Definition stateSteps_def :
  stateSteps inputs init comp 0 = stateStep comp (strmIndex inputs 0,init) ∧
  stateSteps inputs init comp (SUC t) =
     let (stateE,outE) = stateSteps inputs init comp t
     in stateStep comp (strmIndex inputs (SUC t),stateE)
End


(*---------------------------------------------------------------------------*)
(* Running the state stepper for t steps gives the same answers as running   *)
(* the stream stepper for t steps and looking at the (state,output) just at  *)
(* time t.                                                                   *)
(*                                                                           *)
(* This statement is only true if comp is in a form where it looks back at   *)
(* most one step in its history. Also, comp has to be wellformed and env has *)
(* to support it, as in agreeTheory.                                         *)
(*---------------------------------------------------------------------------*)

Theorem stepper_equiv :
  ∀E init comp t result.
     Wellformed comp ∧ Supports E comp ∧
     result = strmIndex (strmSteps E comp t) t
     ⇒
     stateSteps (input_of comp E) init comp t =
     (state_of comp result,output_of comp result)
Proof
  cheat
(*
  Induct_on ‘t’
  >- rw[stateSteps_def,strmSteps_def,stateStep_def,strmStep_def]
*)
QED

Definition fmap_map_def:
 fmap_map f = FMAP_MAP2 (\(d,r). f r)
End

(*---------------------------------------------------------------------------*)
(* Given inputs and a state, produce the new state and outputs               *)
(*                                                                           *)
(*  bufStep: component -> inputs # state -> state # outputs                  *)
(*                                                                           *)
(* where state is a (string |-> value) environment and inputs/outputs are    *)
(* (string |-> string) environments. This models the use of byte buffers for *)
(* component input and output. For now assume the existence of suitable      *)
(* encoders and decoders (enc,dec).                                          *)
(*---------------------------------------------------------------------------*)

Type buf_env = “:string |-> string”

Definition bufStep_def:
  bufStep (enc:value->string,dec:string->value) comp (inE,stateE) =
    let inputs = fmap_map dec inE;
        (stateE',outE) = stateStep comp (inputs,stateE);
        outE' = fmap_map enc outE;
    in (stateE',outE')
End

(*---------------------------------------------------------------------------*)
(* Latex support                                                             *)
(*---------------------------------------------------------------------------*)

val _ = TeX_notation {hol = "FUNION",        TeX = ("\\HOLTokenFmapUnion", 1)};
val _ = TeX_notation {hol = UTF8.chr 0x228C, TeX = ("\\HOLTokenFmapUnion", 1)};
val _ = TeX_notation {hol = "fmap_map", TeX = ("fmap\\_map", 8)};

val _ = export_theory();
