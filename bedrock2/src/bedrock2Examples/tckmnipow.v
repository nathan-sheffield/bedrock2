Require Import Coq.ZArith.ZArith coqutil.Z.div_mod_to_equations.
Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.MetricLogging.
Import Syntax BinInt String List.ListNotations ZArith.
Require Import coqutil.Z.Lia.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.
Local Coercion literal (z : Z) : Syntax.expr := Syntax.expr.literal z.

Require Import bedrock2.Syntax.
Require Import bedrock2.WeakestPrecondition.
Require Import bedrock2.WeakestPreconditionProperties.
Require Import bedrock2.Loops.
Require Import bedrock2.Map.SeparationLogic.
Module Import Coercions.
  Import Map.Interface Word.Interface BinInt.
  Coercion Z.of_nat : nat >-> Z.
  Coercion word.unsigned : word.rep >-> Z.
Require Import coqutil.Tactics.eplace coqutil.Tactics.eabstract Coq.setoid_ring.Ring_tac.
From coqutil.Tactics Require Import Tactics letexists eabstract rdelta reference_to_string ident_of_string.


Definition ipow := func! (x, e) ~> ret {
  ret = $1;
  while (e) {
    if (e & $1) { ret = ret * x };
    e = e >> $1;
    x = x * x
  }
                     }.

From bedrock2 Require Import Semantics BasicC64Semantics WeakestPrecondition ProgramLogic.
From coqutil Require Import Word.Properties Word.Interface Tactics.letexists.
Import Interface.word.

Definition initCost := {| instructions := 9; stores := 0; loads := 9; jumps := 0 |}.
Definition iterCost := {| instructions := 38; stores := 0; loads := 45; jumps := 2 |}.
Definition endCost :=  {| instructions := 2; stores := 0; loads := 3; jumps := 1 |}.

Definition msb z := match z with
                    | Zpos _ => Z.log2 z + 1
                    | _ => 0
                    end.

#[export] Instance spec_of_ipow : spec_of "ipow" :=
  fnspec! "ipow" x e ~> v,
  { requires t m mc := True;
    ensures t' m' mc' := unsigned v = unsigned x ^ unsigned e mod 2^64 /\
    (mc' - mc <= initCost + (msb (word.unsigned e)) * iterCost + endCost)%metricsH}.

Module Z.
  Lemma pow_mod x n m (Hnz: m <> 0) : (x mod m)^n mod m = x^n mod m.
  Proof.
    revert n.
    eapply Z.order_induction_0; intros.
    { intros ???; subst; split; auto. }
    { rewrite 2Z.pow_0_r; trivial. }
    { rewrite 2Z.pow_succ_r by trivial.
      rewrite <-Z.mul_mod_idemp_r by trivial.
      multimatch goal with H: _ |- _ => rewrite H end;
      rewrite Z.mul_mod_idemp_l, Z.mul_mod_idemp_r; solve[trivial]. }
    { rewrite 2Z.pow_neg_r; trivial. }
  Qed.

  Lemma mod2_nonzero x : x mod 2 <> 0 -> x mod 2 = 1.
  Proof. Z.div_mod_to_equations. blia. Qed.

  Lemma land_1_r x : Z.land x 1 = x mod 2.
  Proof.
    change 1 with (Z.ones 1) in *.
    rewrite Z.land_ones in * by discriminate.
    exact eq_refl.
  Qed.
End Z.

Require Import bedrock2.AbsintWordToZ coqutil.Z.Lia.

Ltac t :=
  repeat match goal with x := _ |- _ => subst x end;
  repeat match goal with |- context [word.unsigned ?e] => progress (idtac; let H := rbounded (word.unsigned e) in idtac) end;
  repeat match goal with G: context [word.unsigned ?e] |- _ => progress (idtac; let H := rbounded (word.unsigned e) in idtac) end;
  repeat match goal with |- context [word.unsigned ?e] => progress (idtac; let H := unsigned.zify_expr e in try rewrite H) end;
  repeat match goal with G: context [word.unsigned ?e] |- _ => progress (idtac; let H := unsigned.zify_expr e in try rewrite H in G) end;
  repeat match goal with H: absint_eq ?x ?x |- _ => clear H end;
  cbv [absint_eq] in *.

Lemma msb_shift z : 0 < z -> msb (z / 2) = msb z - 1.
Proof.
  intro.
  case (z / 2) eqn:Hdiv.
  - enough (H1 : z = 1) by (rewrite H1; easy).
    enough (z = z mod 2) by (Z.div_mod_to_equations; blia).
    rewrite (Z.div_mod z 2) by blia.
    rewrite Hdiv.
    cbn.
    rewrite Zmod_mod.
    reflexivity.
  - rewrite <- Z.div2_div in Hdiv.
    rewrite (Zdiv2_odd_eqn z).
    rewrite Hdiv.
    rewrite <- Pos2Z.inj_mul.
    case (Z.odd z);
    [rewrite <- Pos2Z.inj_add | rewrite Z.add_0_r];
    unfold msb;
    rewrite Z.add_simpl_r;
    [rewrite Pos2Z.inj_add |]; rewrite Pos2Z.inj_mul;
    [rewrite Z.log2_succ_double | rewrite Z.log2_double];
    blia.
  - pose proof (Zlt_neg_0 p) as Hneg.
    rewrite <- Hdiv in Hneg.
    Z.div_mod_to_equations.
    blia.
Qed.

Lemma ipow_ok : program_logic_goal_for_function! ipow.
Proof.
  repeat straightline.
       
 refine ((Loops.tailrec
    (* types of ghost variables*) HList.polymorphic_list.nil
    (* program variables *) (["e";"ret";"x"] : list String.string))
    (fun v t m e ret x mc => PrimitivePair.pair.mk (v = word.unsigned e) (* precondition *)
    (fun   T M E RET X MC=> T = t /\ M = m /\ (* postcondition *)
        word.unsigned RET = word.unsigned ret * word.unsigned x ^ word.unsigned e mod 2^64 /\
        (MC - mc <= msb (word.unsigned e) * iterCost + endCost)%metricsH))
    (fun n m => 0 <= n < m) (* well_founded relation *)
    _ _ _ _ _) ;
    (* TODO wrap this into a tactic with the previous refine *)
    cbn [HList.hlist.foralls HList.tuple.foralls
         HList.hlist.existss HList.tuple.existss
         HList.hlist.apply  HList.tuple.apply
         HList.hlist
         List.repeat Datatypes.length
         HList.polymorphic_list.repeat HList.polymorphic_list.length
         PrimitivePair.pair._1 PrimitivePair.pair._2] in *.

  { repeat straightline. }
  { exact (Z.lt_wf _). }
  { repeat straightline. } (* init precondition *)
{ (* loop test *)
    repeat straightline; try show_program.
    { (* loop body *)
      eexists; eexists; split; [repeat straightline|]. (* if condition evaluation *)
      split. (* if cases, path-blasting *)
      {
        repeat (straightline || (split; trivial; [])). 2: split. all:t.
        { (* measure decreases *)
          set (word.unsigned x0) in *. (* WHY does blia need this? *)
          Z.div_mod_to_equations. blia. }
        { (* invariant preserved *)
          rewrite H4; clear H4. rename H1 into Hbit.
          change (1+1) with 2 in *.
          eapply Z.mod2_nonzero in Hbit.
          epose proof (Z.div_mod _ 2 ltac:(discriminate)) as Heq; rewrite Hbit in Heq.
          rewrite Heq at 2; clear Hbit Heq.
          (* rewriting with equivalence modulo ... *)
          rewrite !word.unsigned_mul.
          unfold word.wrap.
          rewrite ?Z.mul_mod_idemp_l by discriminate.
          rewrite <-(Z.mul_mod_idemp_r _ (_^_)), Z.pow_mod by discriminate.
          rewrite ?Z.pow_add_r by (pose proof word.unsigned_range x0; Z.div_mod_to_equations; blia).
          rewrite ?Z.pow_twice_r, ?Z.pow_1_r, ?Z.pow_mul_l.
          rewrite Z.mul_mod_idemp_r by discriminate.
          f_equal; ring. }
        { 
          destruct MC; destruct mc0; applyAddMetrics H5.
          rewrite msb_shift in H5 by blia.
          rewrite MetricArith.mul_sub_distr_r in H5.
          rewrite <- MetricArith.add_sub_swap in H5.
          rewrite <- MetricArith.le_add_le_sub_r in H5.
          eapply MetricArith.le_trans.
          2: exact H5.
          unfold iterCost.
          solve_MetricLog.
        }
      }
      {
        repeat (straightline || (split; trivial; [])). 2: split. all: t.
        { (* measure decreases *)
          set (word.unsigned x0) in *. (* WHY does blia need this? *)
          Z.div_mod_to_equations; blia. }
        { (* invariant preserved *)
          rewrite H4; clear H4. rename H1 into Hbit.
          change (1+1) with 2 in *.
          epose proof (Z.div_mod _ 2 ltac:(discriminate)) as Heq; rewrite Hbit in Heq.
          rewrite Heq at 2; clear Hbit Heq.
          (* rewriting with equivalence modulo ... *)
          rewrite !word.unsigned_mul, ?Z.mul_mod_idemp_l by discriminate.
          cbv [word.wrap].
          rewrite <-(Z.mul_mod_idemp_r _ (_^_)), Z.pow_mod by discriminate.
          rewrite ?Z.add_0_r, Z.pow_twice_r, ?Z.pow_1_r, ?Z.pow_mul_l.
          rewrite Z.mul_mod_idemp_r by discriminate.
          f_equal; ring. }
        { (* metrics correct *)
          destruct MC; destruct mc0; applyAddMetrics H5.
          rewrite msb_shift in H5 by blia.
          rewrite MetricArith.mul_sub_distr_r in H5.
          rewrite <- MetricArith.add_sub_swap in H5.
          rewrite <- MetricArith.le_add_le_sub_r in H5.
          eapply MetricArith.le_trans.
          2: exact H5.
          unfold iterCost.
          solve_MetricLog.
        }
      }
    }
    { (* postcondition *)
      rewrite H0, Z.pow_0_r, Z.mul_1_r, word.wrap_unsigned.
      repeat match goal with
             | |- _ /\ _ => split
             | |- _ = _ => reflexivity
             end.
      unfold msb, iterCost, endCost.
      subst mc'. solve_MetricLog.
    }
}

  repeat straightline.
  repeat match goal with
         | |- _ /\ _ => split
         | |- _ = _ => reflexivity
         | |- exists _, _ => letexists
         | _ => t
         end.

  1: { setoid_rewrite H2; setoid_rewrite Z.mul_1_l; trivial. }

  unfold initCost, iterCost, endCost in *.
  solve_MetricLog.
Qed.
