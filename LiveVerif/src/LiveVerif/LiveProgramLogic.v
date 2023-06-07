Require Import Coq.ZArith.ZArith. Local Open Scope Z_scope.
Require Import Coq.micromega.Lia.
Require Import coqutil.Z.Lia.
Require Import Coq.Strings.String.
Require Import coqutil.Tactics.rdelta.
Require Import coqutil.Tactics.Tactics.
Require Import coqutil.Map.Interface.
Require Import coqutil.Word.Interface coqutil.Word.Properties.
Require Import coqutil.Tactics.syntactic_unify.
Require Import coqutil.Tactics.destr.
Require Import coqutil.Tactics.fwd.
Require Import coqutil.Tactics.ltac_list_ops.
Require Import coqutil.Tactics.foreach_hyp.
Require Import coqutil.Datatypes.RecordSetters.
Require Import bedrock2.Syntax bedrock2.Semantics.
Require Import bedrock2.Lift1Prop.
Require Import bedrock2.Map.Separation bedrock2.Map.SeparationLogic bedrock2.Array.
Require Import bedrock2.unzify.
Require Import bedrock2.ptsto_bytes bedrock2.Scalars.
Require Import bedrock2.TacticError. Local Open Scope Z_scope.
Require Import LiveVerif.string_to_ident.
Require Import bedrock2.find_hyp.
Require Import bedrock2.ident_to_string.
Require Import bedrock2.HeapletwiseHyps.
Require Import bedrock2.HeapletwiseAutoSplitMerge.
Require Import bedrock2.SepLib.
Require Import bedrock2.PurifySep.
Require Import bedrock2.PurifyHeapletwise.
Require Import bedrock2.bottom_up_simpl.
Require Import bedrock2.safe_f_equal.
Require Import coqutil.Tactics.ident_ops.
Require Import bedrock2.Logging.
Require Import LiveVerif.LiveRules.
Require Import LiveVerif.PackageContext.
Require Import LiveVerif.LiveSnippet.

Definition functions_correct
  (* universally quantified abstract function list containing all functions: *)
  (qfs: list (string * func)):
  (* specs of a subset of functions for which to assert correctness *)
  list (list (string * func) -> Prop (* spec_of mentioning function name *)) -> Prop :=
  List.Forall (fun spec => spec qfs).

Definition function_with_callees: Type :=
  func * list (list (string * func) -> Prop (* spec_of mentioning function name *)).

Definition program_logic_goal_for(name: string)(f: function_with_callees)
  {spec: bedrock2.ProgramLogic.spec_of name}: Prop :=
  match f with
  | (impl, callees) => forall functions,
      functions_correct functions callees -> spec (cons (name, impl) functions)
  end.

Definition nth_spec(specs: list (list (string * func) -> Prop))(n: nat) :=
  Eval unfold List.nth in (List.nth n specs (fun _ => True)).

Lemma nth_function_correct: forall fs n specs spec,
    nth_spec specs n = spec ->
    functions_correct fs specs ->
    spec fs.
Proof.
  unfold functions_correct. intros. subst spec.
  eapply (proj1 (List.Forall_nth_default' _ _ _ I)) in H0.
  exact H0.
Qed.

(* State container, defined in such a way that updating the state doesn't affect or grow
   the proof term: *)

Definition currently(contents: Type) := unit.

Ltac pose_state s :=
  let n := fresh "state" in
  pose proof (tt : currently s) as n;
  move n at top.

Ltac get_state :=
  lazymatch reverse goal with
  | state: currently ?s |- _ => s
  end.

Ltac set_state s :=
  lazymatch reverse goal with
  | state: currently _ |- _ => change (currently s) in state
  end.

Inductive displaying: Type :=.
Inductive stepping: Type :=.

Definition ready{P: Prop} := P.

(* heapletwise- and word-aware lia, successor of ZnWords *)
Ltac hwlia := zify_hyps; puri_simpli_zify_hyps accept_always; zify_goal; xlia zchecker.

Ltac2 Set bottom_up_simpl_sidecond_hook := fun _ => ltac1:(zify_goal; xlia zchecker).

Ltac intros_until_trace :=
  repeat lazymatch goal with
    | |- forall (_: trace), _ => fail (* done *)
    | |- forall _, _ => intros ?
    end.

Ltac start :=
  lazymatch goal with
  | |- @program_logic_goal_for ?fname ?evar ?spec =>
      lazymatch open_constr:((_, _): function_with_callees) with
      | ?p => unify evar p
      end;
      subst evar;
      unfold program_logic_goal_for, spec;
      let fs := fresh "fs" in
      let fs_ok := fresh "fs_ok" in
      intros fs fs_ok;
      let nP := fresh "Scope0" in pose proof (mk_scope_marker FunctionParams) as nP;
      intros_until_trace;
      let nB := fresh "Scope0" in pose proof (mk_scope_marker FunctionBody) as nB;
      lazymatch goal with
      | |- forall (t : trace) (m : @map.rep (@word.rep _ _) Init.Byte.byte _), _ => intros
      end;
      WeakestPrecondition.unfold1_call_goal;
      cbv match beta delta [WeakestPrecondition.call_body];
      lazymatch goal with
      | |- if ?test then ?T else _ =>
        replace test with true by reflexivity; change T
      end;
      eapply prove_func;
      [ lazymatch goal with
        | |- map.of_list_zip ?argnames_evar ?argvalues = Some ?locals_evar =>
             let argnames := map_with_ltac varconstr_to_string argvalues in
             unify argnames_evar argnames;
             let kvs := eval unfold List.combine in (List.combine argnames argvalues) in
             unify locals_evar (map.of_list kvs);
             reflexivity
        end
      | ];
      pose_state stepping
  | |- _ => fail "goal needs to be of shape (@program_logic_goal_for ?fname ?evar ?spec)"
  end.

Ltac is_function_param x :=
  lazymatch goal with
  | p: scope_marker FunctionParams, b: scope_marker FunctionBody |- _ =>
      ident_is_above p x; ident_is_above x b
  | _ => fail 1000 "could not find FunctionParams and FunctionBody scope_marker"
  end.

Ltac is_in_snd x ps :=
  lazymatch ps with
  | (_, x) :: _ => idtac
  | _ :: ?rest => is_in_snd x rest
  | nil => fail "not found"
  | _ => fail 1000 ps "is not a concrete enough list"
  end.

Ltac put_into_current_locals :=
  lazymatch goal with
  | |- update_locals ?ks ?vs _ _ => try subst vs
  end;
  lazymatch goal with
  | |- update_locals nil nil ?l ?post => unfold update_locals
  | |- update_locals (cons ?x nil) (cons ?v nil) ?l ?post =>
      let i := string_to_ident x in
      make_fresh i;
      (* match again because there might have been a renaming *)
      lazymatch goal with
      | |- update_locals (cons ?x nil) (cons ?v nil) ?l ?post =>
          let tuples := lazymatch l with map.of_list ?ts => ts end in
          tryif (
              is_var v;
              assert_fails (idtac; is_function_param v); (* not a ghost or non-ghost arg *)
              assert_fails (idtac; is_in_snd v tuples) (* not a local program variable *))
          then (* we can rename v into i instead of creating a new variable & equation *)
            (rename v into i; unfold update_locals)
          else
            (eapply update_one_local_eq; intro_word i; let h := fresh "Def0" in intro h)
      end;
      normalize_locals_wp
  | |- update_locals ?ks ?vs _ _ => fail 1000 "update_locals for" ks "and" vs "not supported"
  end.

Ltac clear_until_LoopInvariant_marker :=
  repeat match goal with
         | x: ?T |- _ => lazymatch T with
                         | scope_marker LoopInvariant => fail 1
                         | _ => clear x
                         end
         end;
  match goal with
  | x: ?T |- _ => lazymatch T with
                  | scope_marker LoopInvariant => clear x
                  | _ => fail "call 'loop invariant above my_var.' before the loop"
                  end
  end.

Ltac expect_and_clear_last_marker expected :=
  lazymatch goal with
  | H: scope_marker ?sk |- _ =>
      tryif constr_eq sk expected then
        clear H
      else
        fail "Assertion failure: Expected last marker to be" expected "but got" sk
  end.

Ltac destruct_ifs :=
  repeat match goal with
         | H: context[if ?b then _ else _] |- _ =>
             let t := type of b in constr_eq t bool; destr b
         | |- context[if ?b then _ else _] =>
             let t := type of b in constr_eq t bool; destr b
         end.

Import Ltac2.Ltac2. Set Default Proof Mode "Classic".

Ltac2 default_simpl_in_hyps () :=
  repeat (foreach_hyp (fun h t =>
                         if Ident.starts_with @__ h then ()
                         else bottom_up_simpl_in_hyp_of_type silent_if_no_progress h t));
  try record.simp_hyps ().

Ltac default_simpl_in_hyps := ltac2:(default_simpl_in_hyps ()).

Ltac default_simpl_in_all :=
  default_simpl_in_hyps; bottom_up_simpl_in_goal_nop_ok; try record.simp_goal.

Ltac after_command_simpl_hook := default_simpl_in_hyps.

(* Some ingredients for proving postconditions at end of blocks,
   too expensive in general, but useful when applied carefully. *)

Ltac destruct_lists_of_concrete_nat_length :=
  repeat match goal with
           | H: List.length ?l = S _ |- _ =>
               is_var l; destruct l;
               [ discriminate H
               | cbn [List.length] in H; eapply Nat.succ_inj in H ]
           | H: List.length ?l = O |- _ =>
               is_var l; destruct l;
               [ clear H
               | discriminate H ]
           end.

Ltac subst_all_let_bound_vars :=
  repeat match goal with
    | x := _ |- _ => subst x
    end.

Ltac destruct_ands_list :=
    repeat match goal with
           | H: ands (_ :: _) |- _ => destruct H
           | H: ands nil |- _ => clear H
           end.

Ltac destruct_ors :=
  repeat match goal with
    | H: ?P \/ ?Q |- _ => tryif (is_lia P; is_lia Q) then fail else destruct H
    end.

Create HintDb prove_post.

Ltac ret_generic c post retnames :=
  lazymatch goal with
  | B: scope_marker ?sk |- _ =>
      lazymatch sk with
      | FunctionBody => idtac
      | ThenBranch => fail "return inside a then-branch is not supported"
      | ElseBranch => fail "return inside an else-branch is not supported"
      | LoopBody => fail "return inside a loop body is not supported"
      end
  | |- _ => fail "block structure lost (could not find a scope_marker)"
  end;
  unify c cmd.skip;
  lazymatch post with
  | (fun t' m' l' => exists rets, map.getmany_of_list l' ?eretnames = Some rets /\ _) =>
      unify eretnames retnames
  end.

Ltac strip_conss l :=
  lazymatch l with
  | cons _ ?t => strip_conss t
  | _ => l
  end.

Ltac package_heapletwise_context :=
  let H := fresh "M" in collect_heaplets_into_one_sepclause H;
  package_context.

Ltac unset_loop_body_vars :=
  lazymatch goal with
  | |- wp_cmd _ _ _ _ (map.of_list ?l) ?post =>
      let newvars := list_map_ignoring_failures ltac:(key_of_pair_if_not_in post) l in
      eapply (wp_unset_many newvars);
      normalize_locals_wp
  end.

Ltac close_function :=
  lazymatch goal with
  | H: functions_correct ?fs ?l |- _ =>
      let T := lazymatch type of l with list ?T => T end in
      let e := strip_conss l in
      unify e (@nil T)
  end;
  lazymatch goal with
  | |- exists _, map.getmany_of_list _ ?retnames = Some _ /\ _ =>
      (tryif is_evar retnames then unify retnames (@nil string) else idtac);
      eexists; split; [ reflexivity | ]
  end.

Ltac close_block :=
  lazymatch goal with
  | B: scope_marker ?sk |- _ =>
      lazymatch sk with
      | ElseBranch =>
          eapply wp_skip
      | LoopBody =>
          unset_loop_body_vars;
          eapply wp_skip;
          autounfold with heapletwise_always_unfold
      | FunctionBody =>
          eapply wp_skip;
          close_function;
          autounfold with heapletwise_always_unfold
      | _ => fail "Can't end a block here"
      end
  | _ => fail "no scope marker found"
  end.

(* Given a list l and an element e,
   returns a suffix of l starting with e and e's index in l,
   or if not found, returns l with all cons stripped, and the number of stripped cons *)
Ltac suffix_and_index_of e l :=
  lazymatch l with
  | cons e _ => constr:((l, O))
  | cons _ ?rest =>
      lazymatch suffix_and_index_of e rest with
      | (?s, ?n) => constr:((s, S n))
      end
  | _ => constr:((l, O))
  end.

Ltac is_evar_b x :=
  match constr:(Set) with
  | _ => let __ := match constr:(Set) with
                   | _ => is_evar x
                   end in
         constr:(true)
  | _ => constr:(false)
  end.

(* Given an element e and a list l ending in an evar, if e is in the list,
   return its index, else instantiate the evar with the cons of e and a new evar
   for the new tail, and also return the index of e *)
Ltac index_of_or_else_add e l :=
  lazymatch suffix_and_index_of e l with
  | (?suffix, ?n) =>
      lazymatch is_evar_b suffix with
      | true =>
          let new_tail := open_constr:(cons e _) in
          let __ := match constr:(Set) with
                    | _ => unify suffix new_tail
                    end in n
      | false => n
      end
  end.

Goal exists x y, cons x (cons 22 y) = cons 33 (cons 22 (cons 11 nil)).
  do 2 eexists.
  lazymatch goal with
  | |- ?xs = _ => lazymatch index_of_or_else_add 22 xs with 1%nat => idtac end
  end.
  lazymatch goal with
  | |- ?xs = _ => lazymatch index_of_or_else_add 11 xs with 2%nat => idtac end
  end.
  lazymatch goal with
  | |- ?xs = _ => lazymatch index_of_or_else_add 11 xs with 2%nat => idtac end
  end.
  reflexivity.
Abort.

(* lhs:    option (bool (* is_decl *) * string (* varname *))
   fname:  string
   arges:  list expr *)
Ltac call lhs fname arges :=
  let resnames := lazymatch lhs with
                  | Some (_, ?resname) => constr:(cons resname nil)
                  | None => constr:(@nil String.string)
                  end in
  eapply (wp_call _ _ _ _ resnames arges);
  [ let s := lazymatch constr:(_ : ProgramLogic.spec_of fname) with ?sp => sp end in
    lazymatch goal with
    | H: functions_correct ?fs ?l |- _ =>
        let n := index_of_or_else_add s l in
        eapply (nth_function_correct _ n) in H; [ | cbv [nth_spec]; reflexivity ];
        let h := head s in
        unfold h in H;
        eapply H
    end
  | (* one dexprs1 goal containing argument evaluation, precondition, and continuation
       after the call *) ].

(* Assigns default well_founded relations to types.
   Use lower costs to override existing entries. *)
Create HintDb wf_of_type.

#[export] Hint Resolve word.well_founded_lt_unsigned | 4 : wf_of_type.

Lemma Z_lt_downto_0_wf: well_founded (fun n m : Z => 0 <= n < m).
Proof. exact (Z.lt_wf 0). Qed.

#[export] Hint Resolve Z_lt_downto_0_wf | 4 : wf_of_type.

Tactic Notation "loop" "invariant" "above" ident(i) :=
  let n := fresh "Scope0" in pose proof (mk_scope_marker LoopInvariant) as n;
  move n after i.

Ltac while cond measure0 :=
  eapply (wp_while measure0 cond);
  [ package_heapletwise_context
  | eauto with wf_of_type
  | repeat match goal with
      | H: sep _ _ ?M |- _ => clear M H
      end;
    clear_until_LoopInvariant_marker;
    (* Note: will also appear after loop, where we'll have to clear it,
       but we have to pose it here because the foralls are shared between
       loop body and after the loop *)
    (let n := fresh "Scope0" in pose proof (mk_scope_marker LoopBody) as n);
    cbv beta;
    intros;
    unpackage_context;
    lazymatch goal with
    | |- exists b, dexpr_bool3 _ _ _ b _ _ _ => eexists
    | |- _ => fail "assertion failure: hypothesis of wp_while has unexpected shape"
    end ].

Ltac is_local_var name :=
  lazymatch goal with
  | |- wp_cmd _ _ _ _ (map.of_list ?l) _ =>
      lazymatch l with
      | context[(name, _)] => idtac
      | _ => fail 0 name "needs to be declared first"
      end
  end.

Ltac isnt_local_var name :=
  lazymatch goal with
  | |- wp_cmd _ _ _ _ (map.of_list ?l) _ =>
      lazymatch l with
      | context[(name, _)] => fail 0 name "has already been declared"
      | _ => idtac
      end
  end.

Ltac add_regular_snippet s :=
  lazymatch s with
  | SAssign ?is_decl ?name ?rhs =>
      lazymatch is_decl with
      | true => isnt_local_var name
      | false => is_local_var name
      end;
      lazymatch rhs with
      | RCall ?fname ?arges => call (Some (is_decl, name)) fname arges
      | RExpr ?e => eapply (wp_set _ name e)
      end
  | SVoidCall ?fname ?arges => call (@None (prod bool string)) fname arges
  | SStore access_size.word ?addr ?val => eapply (wp_store_uintptr _ addr val)
  | SStore ?sz ?addr ?val => eapply (wp_store_uint _ sz addr val)
  | SIf ?c => eapply (wp_if_bool_dexpr _ c);
              let n := fresh "Scope0" in
              pose proof (mk_scope_marker IfCondition) as n
  | SElse =>
      assert_scope_kind ThenBranch;
      eapply wp_skip (* leaves a branch_post marker to be taken care of by step *)
  | SWhile ?cond ?measure0 => while cond measure0
  | SStart => fail "SStart can only be used to start a function"
  | SEnd => close_block
  | SRet ?retnames =>
      lazymatch goal with
      | |- wp_cmd ?fs ?c ?t ?m ?l ?post => ret_generic c post retnames
      end
  | SEmpty => idtac
  end.

Ltac after_if_cleanup :=
  lazymatch goal with
  | |- after_if _ _ ?Q1 ?Q2 _ _ =>
      tryif is_evar Q1 then
        fail "can't end if yet because" Q1 "not yet instantiated"
      else
        tryif is_evar Q2 then
          fail "can't end if yet because" Q2 "not yet instantiated"
        else
          after_if
  | _ => fail "expected after_if goal"
  end.

Lemma BoolSpec_expr_branches{Bt Bf: Prop}{b: bool}{H: BoolSpec Bt Bf b}(Pt Pf Pa: Prop):
  (Bt -> Pt) ->
  (Bf -> Pf) ->
  Pa ->
  bool_expr_branches b Pt Pf Pa.
Proof.
  intros. unfold bool_expr_branches. destruct H; auto.
Qed.

Ltac subst_unless_local_var x :=
  lazymatch goal with
  | |- wp_cmd _ _ _ _ (map.of_list ?l) _ =>
      lazymatch l with
      | context[(_, x)] => fail (* don't subst local variables *)
      | _ => subst x
      end
  end.

(* Can be customized with ::= *)
Ltac is_substitutable_rhs_cleanup rhs :=
  first [ is_var rhs
        | is_const rhs
        | lazymatch isZcst rhs with true => idtac end
        | lazymatch rhs with
          | word.of_Z ?x => is_substitutable_rhs_cleanup x
          | word.unsigned ?x => is_substitutable_rhs_cleanup x
          end ].

Ltac cleanup_step :=
  match goal with
  | x := ?rhs |- _ => is_substitutable_rhs_cleanup rhs; subst_unless_local_var x
  | x := _ |- _ => clear x
  | _: ?x = ?y |- _ =>
      first [ is_var x; is_substitutable_rhs_cleanup y; subst_unless_local_var x
            | is_var y; is_substitutable_rhs_cleanup x; subst_unless_local_var y ]
  | |- _ => progress fwd
  end.

Definition don't_know_how_to_prove_equal{A: Type} := @eq A.
Notation "'don't_know_how_to_prove_equal' x y" :=
  (don't_know_how_to_prove_equal x y)
  (only printing, at level 10, x at level 0, y at level 0,
   format "don't_know_how_to_prove_equal '//' x '//' y").

Ltac default_eq_prover_step :=
  match goal with
  | |- ?l = ?r => is_evar l; reflexivity
  | |- ?l = ?r => is_evar r; reflexivity
  | |- ?l = ?r => constr_eq l r; reflexivity
  | |- _ => bottom_up_simpl_in_goal (* fails if nothing to simplify *)
  | |- _ => safe_f_equal_step
  | |- ?l = ?r => subst l
  | |- ?l = ?r => subst r
  | |- ?l = ?r => change (don't_know_how_to_prove_equal l r)
  end.

Ltac eq_prover_step_hook := default_eq_prover_step.

Ltac eval_dexpr_bool3_step e :=
  lazymatch e with
  | expr.lazy_and _ _       => eapply dexpr_bool3_lazy_and
  | expr.lazy_or _ _        => eapply dexpr_bool3_lazy_or
  | expr.not _              => eapply dexpr_bool3_not
  | expr.op bopname.eq _ _  => eapply dexpr_bool3_eq
  | expr.op bopname.ltu _ _ => eapply dexpr_bool3_ltu
  | _ => fail 1000 "expression" e "not yet supported"
  end.

Ltac eval_dexpr1_step e :=
  lazymatch e with
  | expr.var _ => eapply dexpr1_var; [reflexivity| ]
  | expr.literal _ => eapply dexpr1_literal
  | expr.op _ _ _ => eapply dexpr1_binop_unf
  | expr.load access_size.word _ => eapply dexpr1_load_uintptr
  | expr.load _ _ => eapply dexpr1_load_uint
  end.

Lemma eq_if_same{A: Type}(c: bool)(lhs rhs: A)(H: lhs = if c then rhs else rhs): lhs = rhs.
Proof. intros. destruct c; exact H. Qed.

Ltac clear_mem_split_eqs :=
  repeat match goal with
    | H: _ = DisjointUnion.mmap.Def _ |- _ => clear H
    end.

Ltac clear_heaplets :=
  repeat match goal with
    | m: @map.rep (@word.rep _ _) Coq.Init.Byte.byte _ |- _ => clear m
    end.

Ltac conclusion_shape_based_step logger :=
  lazymatch goal with
  | |- dexpr_bool3 _ _ ?e _ _ _ _ =>
      logger ltac:(fun _ => idtac "Evaluating expression" e);
      eval_dexpr_bool3_step e
  | |- dexpr1 _ _ ?e _ _ =>
      logger ltac:(fun _ => idtac "Evaluating expression" e);
      eval_dexpr1_step e
  | |- dexprs1 _ _ (cons _ _) _ _ =>
      logger ltac:(fun _ => idtac "Evaluating expression list");
      eapply dexprs1_cons
  | |- dexprs1 _ _ nil _ _ =>
      logger ltac:(fun _ => idtac "Done evaluating expression list");
      eapply dexprs1_nil
  | |- bool_expr_branches _ _ _ _ =>
      logger ltac:(fun _ => idtac "Splitting bool_expr_branches into three subgoals");
      eapply BoolSpec_expr_branches; [ intro | intro | ]
  | |- then_branch_marker ?G =>
      logger ltac:(fun _ => idtac "Starting `then` branch");
      let n := fresh "Scope0" in
      pose proof (mk_scope_marker ThenBranch) as n;
      change G
  | |- else_branch_marker ?G =>
      logger ltac:(fun _ => idtac "Starting `else` branch");
      let n := fresh "Scope0" in
      pose proof (mk_scope_marker ElseBranch) as n;
      change G
  | |- branch_post ?l0 ?new_vars ?Q ?t ?m ?l =>
      split; [ reflexivity | ];
      normalize_locals_post;
      package_heapletwise_context
  | |- loop_body_marker ?G =>
      logger ltac:(fun _ => idtac "Starting loop body");
      (* (mk_scope_marker LoopBody) is already posed by while tactic,
         nothing to do here at the moment *)
      change G
  | |- pop_scope_marker (after_loop ?fs ?rest ?t ?m ?l ?post) =>
      logger ltac:(fun _ => idtac "after_loop cleanup");
      lazymatch goal with
      | H: scope_marker LoopBody |- pop_scope_marker ?g => clear H; change g
      end;
      unfold after_loop
  | |- pop_scope_marker (after_if _ _ _ _ _ _) =>
      logger ltac:(fun _ => idtac
         "Removing IfCondition marker after if and clearing outdated memory");
      lazymatch goal with
      | H: scope_marker IfCondition |- pop_scope_marker ?g => clear H; change g
      end;
      clear_heapletwise_hyps;
      clear_mem_split_eqs;
      clear_heaplets
  | |- True =>
      logger ltac:(fun _ => idtac "constructor");
      constructor
  | |- dlet _ (fun x => _) =>
      logger ltac:(fun _ => idtac "introducing dlet");
      eapply let_to_dlet; make_fresh x; intro x
  | |- merge_locals _ (cons (?x, ?v1) _) (cons (?x, ?v2) _) _ =>
      tryif constr_eq v1 v2; is_var v1 then (
        logger ltac:(fun _ => idtac "merge_locals with equal key/value on both sides");
        eapply merge_locals_same
      ) else (
        logger ltac:(fun _ => idtac "introducing local of merge_locals");
        let i := string_to_ident x in
        make_fresh i;
        intro_word i;
        let h := fresh "Def0" in
        intro h;
        repeat first [ rewrite push_if_into_arg1 in h | rewrite push_if_into_arg2 in h ]
      )
  | |- merge_locals _ nil nil _ =>
      logger ltac:(fun _ => idtac "merge_locals done");
      unfold merge_locals
  | |- forall t' m' (retvs: list ?word), _ -> update_locals _ retvs ?l _ =>
      logger ltac:(fun _ => idtac "intro new state after function call");
      intros
  | |- @eq (@map.rep string (@word.rep _ _) _) (map.of_list _) (map.of_list _) =>
      logger ltac:(fun _ => idtac "proving equality between two locals maps");
      (* doesn't make the goal unprovable because we keep tuple lists passed
         to map.of_list sorted by key, and all values in the key-value tuples
         are variables or evars *)
      repeat f_equal
  | |- ands _ =>
      logger ltac:(fun _ => idtac "cbn [ands]");
      cbn [ands]
  end.

Lemma prove_if {Bt Bf b} {_: BoolSpec Bt Bf b} (Pt Pf: Prop):
  (Bt -> Pt) -> (Bf -> Pf) -> if b then Pt else Pf.
Proof. intros. destruct H; auto. Qed.

Ltac final_program_logic_step logger :=
  (* Note: Here, the logger has to be invoked *after* the tactic, because we only
     find out whether it's the right one by running it.
     To make sure that the logger is run exactly once, the thunk should only contain
     and idtac taking a string. *)
  first
      [ cleanup_step;
        logger ltac:(fun _ => idtac "cleanup_step")
      | (* Note: only invoked here because we first need to destruct /\ (done by
           cleanup_step) in hyps so that (retvs = [| ... |]) gets exposed *)
        put_into_current_locals;
        logger ltac:(fun _ => idtac "put_into_current_locals")
      | lazymatch goal with
        | |- exists _, _ => eexists
        | |- elet _ _ => refine (mk_elet _ _ _ eq_refl _)
        end;
        logger ltac:(fun _ => idtac "eexists")
      | (* tried first because it also solves some goals of shape (_ = _) and (_ /\ _) *)
        zify_goal; xlia zchecker;
        logger ltac:(fun _ => idtac "xlia zchecker")
      | lazymatch goal with
        | |- ?P /\ ?Q =>
            split;
            logger ltac:(fun _ => idtac "split")
        | |- _ = _ =>
            eq_prover_step_hook;
            logger ltac:(fun _ => idtac "eq_prover_step_hook")
        | |- if _ then _ else _ =>
            logger ltac:(fun _ => idtac "split if");
            eapply prove_if; intros; after_command_simpl_hook
        | |- wp_cmd _ _ _ _ _ _ =>
              lazymatch goal with
              | |- ?G => change (@ready G)
              end;
              after_command_simpl_hook;
              unzify;
              unpurify;
              set_state displaying;
              logger ltac:(fun _ => idtac "after_command_simpl_hook; unzify; unpurify")
        end ].

Ltac new_heapletwise_hyp_hook h t ::=
  puri_simpli_zify_hyp accept_unless_follows_by_xlia h t.

Ltac heapletwise_hyp_pre_clear_hook H ::=
  let T := type of H in puri_simpli_zify_hyp accept_unless_follows_by_xlia H T.

(* TODO maybe only do fwd_subst in inv_rec, or for only var vars created by fwd,
   or not at all?
Ltac fwd_subst H ::= idtac. *)

Ltac heapletwise_step' logger :=
  heapletwise_step;
  logger ltac:(fun _ => idtac "heapletwise_step").

Ltac split_step' logger :=
  split_step;
  logger ltac:(fun _ => idtac "split_step").

Ltac merge_step' logger :=
  (* match to make sure we don't merge too early, but only once the wp_cmd
     of the remainder of the program shows up *)
  lazymatch goal with
  | |- wp_cmd ?fs ?rest ?t ?m ?l ?post =>
      merge_step;
      logger ltac:(fun _ => idtac "merge_step")
  end.

Ltac undisplay logger :=
  lazymatch reverse goal with
  | _: currently ?s |- _ =>
      constr_eq s displaying;
      zify_hyps;
      puri_simpli_zify_hyps accept_unless_follows_by_xlia;
      set_state stepping;
      logger ltac:(fun _ => idtac "purify & zify")
  end.

Ltac step0 logger :=
  first [ heapletwise_step' logger
        | conclusion_shape_based_step logger
        | undisplay logger
        | split_step' logger
        | merge_step' logger
        | final_program_logic_step logger ].

Ltac step :=
  assert_no_error; (* <-- useful when debugging with `step. step. step. ...` *)
  step0 run_logger_thunk.

Ltac step_silent := step0 ignore_logger_thunk.

Ltac step_is_done :=
  lazymatch goal with
  | |- @ready _ => idtac
  | |- don't_know_how_to_prove_equal _ _ => idtac
  | |- after_if _ _ _ _ _ _ => idtac
  end.

Ltac steps :=
  lazymatch goal with
  | _: tactic_error _ |- _ => idtac
  | |- _ => tryif step_is_done then idtac
            else tryif step_silent then steps
            else pose_err Error:("The 'step' tactic should not fail here")
  end.

(* If really needed, this hook can be overridden with idtac for debugging,
   but the preferred way is to use /*?. instead of /**. *)
Ltac run_steps_internal_hook := steps.

Ltac add_snippet s :=
  lazymatch goal with
  | |- @ready _ => unfold ready; add_regular_snippet s
  | |- program_logic_goal_for _ _ =>
      lazymatch s with
      | SStart => start
      | _ => fail "expected {, but got" s
      end
  | |- after_if ?fs ?b ?PThen ?PElse ?c ?Post =>
      lazymatch s with
      | SEnd =>
          autounfold with heapletwise_always_unfold;
          eapply after_if_skip;
          intros;
          unpackage_context;
          close_function (* TODO what if we're not in the outermost block? *)
      | SRet ?retnames => ret_generic c Post retnames
      | _ => after_if_cleanup; run_steps_internal_hook
      end
  | |- _ => fail "can't add snippet in non-ready goal"
  end.

Ltac next_snippet s :=
  assert_no_error;
  add_snippet s.

(* Standard usage:   .**/ snippet /**.    *)
Tactic Notation ".*" constr(s) "*" := next_snippet s; run_steps_internal_hook.

(* Debug mode (doesn't run verification steps):   .**/ snippet /*?.   *)
Tactic Notation ".*" constr(s) "?" := next_snippet s.

(* optional comment after closing brace, triggers merging of then/else postcondition *)
Ltac merge := after_if_cleanup; run_steps_internal_hook.

(* for situations where we want to avoid repeating the function name *)
Notation fnspec := (ProgramLogic.spec_of _) (only parsing).

(* To work around https://github.com/coq/coq/issues/7903
   Notations with binders and inline ltac:() don't work, so if the RHS of
   a notation is b and contains binders as well as an occurrence of `ident_to_string x`
   (which expands to ltac:()), we get errors that the binders are not found.
   So instead of writing b, we can write (fun x: string => b) and replace
   `ident_to_string x` by x in b, and then pass (fun x: string => b) to
   with_ident_as_string, which reverts that replacement, ie it turns
   (fun x: string => b) back into `b["x"/x]`. *)
Ltac with_ident_as_string f :=
  lazymatch f with
  | fun x => _ => beta1 f (ident_to_string x)
  end.

(* same as above, but without beta1, beta1 removes casts *)
Ltac with_ident_as_string_no_beta f :=
  lazymatch f with
  | fun x => _ => constr:(f (ident_to_string x))
  end.

(* Notations have (almost) the same RHS as the `fnspec!` notations in
   bedrock2.WeakestPrecondition, but only allow 0 or 1 return value
   (for C compatibility) and use a different syntax in the LHS (to match
   C syntax and live verif comment markers) *)

Declare Custom Entry funspec.

(* One return value: *)
Notation "'uintptr_t' fname ( 'uintptr_t' a1 , 'uintptr_t' .. , 'uintptr_t' an ) /* *# 'ghost_args' := g1 .. gn ; 'requires' t1 m1 := pre ; 'ensures' t2 m2 r := post #* */ /* *" :=
  (fun fname: String.string =>
     (fun fs =>
        (forall a1, .. (forall an, (forall g1, .. (forall gn,
           (forall t1 m1, pre ->
              WeakestPrecondition.call fs fname t1 m1
                (@cons (@word.rep _ _) a1 .. (@cons (@word.rep _ _) an nil) ..)
                (fun t2 m2 retvs => exists r, retvs = cons r nil /\ post))) .. )) .. ))
     : ProgramLogic.spec_of fname)
(in custom funspec at level 1,
 fname name,
 a1 closed binder, an closed binder,
 g1 closed binder, gn closed binder,
 t1 name, t2 name, m1 name, m2 name, r name,
 pre constr at level 200,
 post constr at level 200,
 only parsing).

(* No return value: *)
Notation "'void' fname ( 'uintptr_t' a1 , 'uintptr_t' .. , 'uintptr_t' an ) /* *# 'ghost_args' := g1 .. gn ; 'requires' t1 m1 := pre ; 'ensures' t2 m2 := post #* */ /* *" :=
  (fun fname: String.string =>
     (fun fs =>
        (forall a1, .. (forall an, (forall g1, .. (forall gn,
           (forall t1 m1, pre ->
              WeakestPrecondition.call fs fname t1 m1
                (@cons (@word.rep _ _) a1 .. (@cons (@word.rep _ _) an nil) ..)
                (fun t2 m2 retvs => retvs = nil /\ post))) .. )) .. ))
     : ProgramLogic.spec_of fname)
(in custom funspec at level 1,
 fname name,
 a1 closed binder, an closed binder,
 g1 closed binder, gn closed binder,
 t1 name, t2 name, m1 name, m2 name,
 pre constr at level 200,
 post constr at level 200,
 only parsing).

Notation ".* */ x" :=
  (match x with (* <-- typecheck x before passing it to Ltac, to get better error messages *)
   | _ => ltac:(let r := with_ident_as_string_no_beta x in exact r)
   end)
  (at level 200, x custom funspec at level 1, only parsing).

Notation "'fun_correct!' f" := (program_logic_goal_for (ident_to_string f) f)
  (at level 10, f name, only parsing).

Notation ".* */ //" := True (only parsing).
