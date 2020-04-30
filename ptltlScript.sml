open HolKernel Parse boolLib bossLib lcsymtacs;
open combinTheory pairTheory listTheory stringLib;

val _ = new_theory "ptltl";

Datatype:
 formula
   = Eid string
   | Prim bool
   | Imp formula formula
   | Equiv formula formula
   | Or formula formula
   | Xor formula formula
   | And formula formula
   | Since formula formula
   | Histor formula
   | Once formula
   | Prev formula
   | Start formula
   | End formula
   | Not formula
End

Definition Trigger_def :
  Trigger A B <=> Not(Since (Not A) (Not B))
End

(*---------------------------------------------------------------------------*)
(* These have to be revisited in light of the R&H semantics below for Prev.  *)
(*---------------------------------------------------------------------------*)

Definition Yester_def :
 Yester P <=> Prev P
End

Definition Zyester_def :
 Zyester P <=> Prev P
End

Definition other_elm_def :
 other_elm : string list = []
End


(*---------------------------------------------------------------------------*)
(* Start and End clauses are expanded versions of the original. Need an      *)
(* extra congruence rule to extract the right termination conditions         *)
(*---------------------------------------------------------------------------*)

val _ = DefnBase.add_cong LEFT_AND_CONG;

Definition bigstep_def :
 bigstep form trace <=>
   let (elm,trace_prev) =
         (if NULL trace then (other_elm,[])
          else (HD trace, TL trace))
   in
    case form
     of Eid eid     => MEM eid elm
      | Prim b      => b
      | Not f       => ~bigstep f trace
      | Imp f1 f2   => (bigstep f1 trace ==> bigstep f2 trace)
      | Equiv f1 f2 => (bigstep f1 trace <=> bigstep f2 trace)
      | Or f1 f2    => (bigstep f1 trace \/ bigstep f2 trace)
      | Xor f1 f2   => (bigstep f1 trace <> bigstep f2 trace)
      | And f1 f2   => (bigstep f1 trace /\ bigstep f2 trace)
      | Since f1 f2 => (bigstep f2 trace \/
                        (~NULL trace_prev /\ bigstep f1 trace /\
                         bigstep (Since f1 f2) trace_prev))
      | Histor f    => (bigstep f trace /\
                        (NULL trace_prev \/
                         (~NULL trace_prev /\ bigstep (Histor f) trace_prev)))
      | Once f      => (bigstep f trace \/
                        (~NULL trace_prev /\ bigstep (Once f) trace_prev))

      | Prev f      => ((NULL trace_prev /\ bigstep f trace) \/ bigstep f trace_prev)
      | Start f     => bigstep f trace /\
                       ~((NULL trace_prev /\ bigstep f trace) \/ bigstep f trace_prev)
      | End f       => ((NULL trace_prev /\ bigstep f trace) \/ bigstep f trace_prev)
                        /\ ~bigstep f trace
Termination
WF_REL_TAC `inv_image ($< LEX $<) (\(x,y). (formula_size x, LENGTH y))`
 >> rw_tac list_ss [NULL_EQ,other_elm_def,combinTheory.K_DEF]
 >> TRY (Cases_on `trace` >> fs[])
 >> metis_tac[]
End


(* state machine *)

Definition empty_state_def :
 empty_state = []
End

Definition mk_subforms_def :
  mk_subforms form = (case form
  of Eid eid => [Eid eid]
   | Prim b => [Prim b]
   | Imp f1 f2 =>
       Imp f1 f2 :: (mk_subforms f1) ++ (mk_subforms f2)
   | Equiv f1 f2 =>
       Equiv f1 f2 :: (mk_subforms f1) ++ (mk_subforms f2)
   | Or f1 f2 =>
       Or f1 f2 :: (mk_subforms f1) ++ (mk_subforms f2)
   | Xor f1 f2 =>
       Xor f1 f2 :: (mk_subforms f1) ++ (mk_subforms f2)
   | And f1 f2 =>
       And f1 f2 :: (mk_subforms f1) ++ (mk_subforms f2)
   | Since f1 f2 =>
       Since f1 f2 :: (mk_subforms f1) ++ (mk_subforms f2)
   | Histor f =>
       Histor f :: (mk_subforms f)
   | Once f =>
       Once f :: (mk_subforms f)
   | Prev f =>
       Prev f :: (mk_subforms f)
   | Start f =>
       Start f :: (mk_subforms f)
   | End f =>
       End f :: (mk_subforms f)
   | Not f =>
       Not f :: (mk_subforms f)
  )

End


Definition decide_formula_start_def :
 decide_formula_start fm st elm =
  (case fm of
      Eid eid     => MEM eid elm
    | Prim b      => b
    | Not f       => ~MEM f st
    | Imp f1 f2   => (~MEM f1 st) \/ MEM f2 st
    | Equiv f1 f2 => (MEM f1 st = MEM f2 st)
    | Or f1 f2    => (MEM f1 st \/ MEM f2 st)
    | Xor f1 f2   => ~(MEM f1 st = MEM f2 st)
    | And f1 f2   => (MEM f1 st /\ MEM f2 st)
    | Since f1 f2 => (MEM f1 st /\ MEM f2 st)
    | Histor f    => MEM f st
    | Once f      => MEM f st
    | Prev f      => MEM f st
    | Start f     => F
    | End f       => F
  )
End

Definition decide_formula_def :
 decide_formula fm st st_acc elm =
  (case fm of
     Eid eid => MEM eid elm
   | Prim b => b
   | Not f  => ~MEM f st_acc
   | Imp f1 f2   => (~MEM f1 st_acc) \/ MEM f2 st_acc
   | Equiv f1 f2 => (MEM f1 st_acc = MEM f2 st_acc)
   | Or f1 f2    => (MEM f1 st_acc \/ MEM f2 st_acc)
   | Xor f1 f2   => ~(MEM f1 st_acc = MEM f2 st_acc)
   | And f1 f2   => (MEM f1 st_acc /\ MEM f2 st_acc)
   | Since f1 f2 => (MEM f2 st_acc \/ (MEM f1 st_acc /\ MEM (Since f1 f2) st))
   | Histor f    => (MEM f st_acc /\ MEM (Histor f) st)
   | Once f      => (MEM f st_acc \/ MEM (Once f) st)
   | Prev f      => MEM f st
   | Start f     => (MEM f st_acc /\ ~MEM f st)
   | End f       => (~MEM f st_acc /\ MEM f st)
 )
End


Definition transition_start_def :
 transition_start sforms elm =
   FOLDL
     (\st_acc fm.
         let decision = decide_formula_start fm st_acc elm
         in (if decision then
           fm :: st_acc
         else
           st_acc
         )
     )
     empty_state
     sforms
End

Definition transition_def:
 transition sforms st elm =
   FOLDL
     (\st_acc fm.
         let decision = decide_formula fm st st_acc elm
         in (if decision then
           fm :: st_acc
         else
           st_acc
         )
     )
     empty_state
     sforms
End

Definition dfa_loop_def :
 dfa_loop delta form elms st =
   case elms
     of [] => MEM form st
      | elm :: elms' => dfa_loop delta form elms' (delta st elm)
End


Definition smallstep_def :
 smallstep form =
   let
      subforms = REVERSE (nub (mk_subforms form));
      delta_start = transition_start subforms;
      delta = transition subforms;
   in \elms. case elms
              of [] => MEM form (delta_start other_elm)
               | elm :: elms' => dfa_loop delta form elms' (delta_start elm)
End

Definition  mk_power_list_def :
 mk_power_list [] = [[]] /\
 mk_power_list (x :: xs') =
   let
     rm = mk_power_list xs';
   in
     MAP (\l. x :: l) rm ++ rm

End

Definition extract_ids_def :
  extract_ids form = nub (case form of
    Eid eid => [eid] |
    Prim b => [] |
    Imp f1 f2 => extract_ids f1 ++ extract_ids f2 |
    Equiv  f1 f2 => extract_ids f1 ++ extract_ids f2 |
    Or f1 f2 => extract_ids f1 ++ extract_ids f2 |
    Xor f1 f2 => extract_ids f1 ++ extract_ids f2 |
    And f1 f2 => extract_ids f1 ++ extract_ids f2 |
    Since  f1 f2 => extract_ids f1 ++ extract_ids f2 |
    Histor f => extract_ids f |
    Once f => extract_ids f |
    Prev f => extract_ids f |
    Start f => extract_ids f |
    End f => extract_ids f |
    Not f => extract_ids f
  )
End


Definition find_reachable_edges_def :
  find_reachable_edges max_state_num elms delta states expl_states edges =
  if (max_state_num <= LENGTH expl_states) then
    (expl_states, edges)
  else (case states of
    [] => (expl_states, edges) |
    st :: tl_states => (let
      new_edges = (MAP (\ elm . (st, elm, delta st elm)) elms);
      edges' = new_edges ++ edges;

      expl_states' = st :: expl_states;

      new_states = (FILTER (\ st' .
        ~ (MEM st' expl_states') /\
        ~ (MEM st' tl_states)
      ) (MAP (\ (st, elm, st') . st') new_edges));

      states' = new_states ++ tl_states;

    in
      (find_reachable_edges
        max_state_num elms delta
        states'
        expl_states'
        edges'
      )
    )
  )
Termination
WF_REL_TAC `measure (
  \(max_state_num, elms, delta, states, expl_states, edges). max_state_num - LENGTH expl_states)`
>> rw []
End

Definition mk_relational_data_def :
  mk_relational_data form has_par_evts = let
    ids = extract_ids form;
    par_elms = mk_power_list ids;
    elms = (if has_par_evts then
               par_elms
            else FILTER (\elm. LENGTH elm = 1) par_elms);
    subforms = REVERSE (nub (mk_subforms form));
    delta_start = transition_start subforms;
    delta = transition subforms;
    total_states = mk_power_list subforms;
    max_state_num = LENGTH total_states;
    start_edges = MAP (\elm. (elm, delta_start elm)) elms;
    start_states = nub (MAP SND start_edges);
    (expl_states, edges) = find_reachable_edges max_state_num elms delta start_states [] [];
    accept_states = FILTER (\st. MEM form st) expl_states;
  in
    (expl_states, elms, accept_states, start_edges, edges)
End

Definition mk_table_data_def :
  mk_table_data (expl_states, elms, accept_states, start_edges, edges) = let
    reject_idx = LENGTH expl_states;
    start_idx = reject_idx + 1;
    finals = (MAP (\st. MEM st accept_states) expl_states) ++ [F; F];

    elm_contains = (* elm1 contains elm2 *)
           (\elm1 elm2. EVERY (\id. MEM id elm1) elm2);

    empty_index = LENGTH elms - 1;
    elm_to_index = (\elm. case INDEX_FIND 0 (elm_contains elm) elms
                           of SOME (i, _ ) => i
                            | NONE => empty_index);

    state_to_index = (\st. case INDEX_OF st expl_states
                            of SOME i => i
                             | NONE => reject_idx);

    mk_row = (\ st .
      MAP (\ elm . case (FIND (\ (st_x, elm_x, st') . st_x = st /\ elm_x = elm) edges) of
        SOME (_, _, st') => state_to_index st' |
        NONE => reject_idx
      ) elms
    );

    rows = MAP mk_row expl_states;

    reject_row = MAP (\ _ . reject_idx) elms;

    start_row = (MAP (\ elm . case (FIND (\ (elm_x, _) . elm_x = elm) start_edges) of
      SOME (_, st') => state_to_index st' |
      NONE => reject_idx
    ) elms);

    table = rows ++ [reject_row; start_row];

  in
    (state_to_index, elm_to_index, finals, table, start_idx)
End

Definition table_transition_def:
  table_transition table state_idx elm_idx = EL elm_idx (EL state_idx table)
End


(* This should stay at the SML level
Definition to_dotgraph_def :
  to_dotgraph (expl_states, elms, accept_states, start_edges, edges) = (let

    error_state_str = "error";
    start_state_str = "start";

    concat_with = (\ join_str str_list . case str_list of
      [] => "" |
      x :: xs =>
        (FOLDL (\ str_acc str .
          str_acc ++ join_str ++ str
        ) x xs)
    );

    mk_label = (\ (st : formula list) . case (INDEX_OF st expl_states) of
      SOME i => toString i |
      NONE => error_state_str
    );

    accept_state_labels = (MAP mk_label accept_states);

    start_edge_labels = (MAP (\ (elm, st') .
      ("start", concat_with "." elm, mk_label st')
    ) start_edges);

    edge_labels = start_edge_labels ++ (MAP (\ (st, elm, st') .
      (
        mk_label st,
        (if (elm = []) then
          "_"
        else
          (concat_with "." elm)
        ),
        mk_label st'
      )
    ) edges);

    graph_str = (
      "digraph finite_state_machine {\n" ++
      "  rankdir = LR;\n" ++
      "  node [shape = circle]; \"" ++ start_state_str ++ "\";\n" ++
      (if (NULL accept_states) then "" else
      "  node [shape = doublecircle]; " ++
           (concat_with "; " accept_state_labels) ++ ";\n"
      ) ++
      "  node [shape = plaintext];\n" ++
      "  \"\" -> \"" ++ start_state_str ++ "\" [label = \"\"];\n" ++
      "  node [shape = circle];\n" ++
      (concat_with "" (MAP (\ (st, elm, st') .
        st ++ "->" ++ st' ++ "[label = \"" ++ elm ++ "\"];\n"
      ) edge_labels)) ++
      "}"
    );
  in
    graph_str
  )
End
*)

Definition Event_def :
    Event (x) = IS_SOME x
End

val _ = export_theory();
