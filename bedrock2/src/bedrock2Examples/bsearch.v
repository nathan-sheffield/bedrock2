Require Import Coq.Strings.String Coq.ZArith.ZArith.
Require Import coqutil.Z.Lia.
From bedrock2 Require Import NotationsCustomEntry ProgramLogic Map.Separation Array Scalars Loops.

Require bedrock2Examples.Demos.
Definition bsearch := Demos.bsearch.

From coqutil Require Import Datatypes.List Word.Interface Map.Interface. (* coercions word and rep *)
From bedrock2 Require Import Semantics BasicC64Semantics.

From coqutil.Tactics Require Import syntactic_unify.
From coqutil.Tactics Require Import rdelta.

Require Import bedrock2.AbsintWordToZ.
Strategy -1000 [word]. (* TODO where should this go? *)

Declare Scope word_scope.

Local Infix "^+" := word.add  (at level 50, left associativity) : word_scope.
Local Infix "^-" := word.sub  (at level 50, left associativity) : word_scope.
Local Infix "^<<" := word.slu  (at level 37, left associativity) : word_scope.
Local Infix "^>>" := word.sru  (at level 37, left associativity) : word_scope.
Local Notation "/_" := word.of_Z       (* smaller angle: squeeze a Z into a word *)
 : word_scope.
Local Notation "\_" := word.unsigned   (* supposed to be a denotation bracket;
                                          or bigger angle: let a word fly into the large Z space *)
 : word_scope.

Local Open Scope Z_scope.
Local Open Scope word_scope.

From bedrock2 Require Import Semantics BasicC64Semantics.

Import HList List. Require Import bedrock2.MetricLogging.

Definition iterCost := {| instructions := 53; stores := 0; loads := 62; jumps := 2 |}.
Definition endCost :=  {| instructions := 5; stores := 0; loads := 7; jumps := 1 |}.

 Definition msb (n : nat) := match n with
                    | O => O
                    | n => S (Nat.log2 n)
 end.
 
#[export] Instance spec_of_bsearch : spec_of "bsearch"%string := fun functions =>
  forall left right target xs R t m mc,
    sep (array scalar (word.of_Z 8) left xs) R m ->
    \_ (right ^- left) = 8*Z.of_nat (Datatypes.length xs) ->
    WeakestPrecondition.call functions
      "bsearch"%string t m (left::right::target::nil)%list mc
      (fun t' m' rets mc' => t=t' /\ sep (array scalar (word.of_Z 8) left xs) R m' /\ 
       (mc' - mc <= Z.of_nat (msb (Datatypes.length xs)) * iterCost + endCost)%metricsH                               
      ).


From coqutil.Tactics Require Import eabstract letexists rdelta.
From coqutil.Macros Require Import symmetry.
Import PrimitivePair.
Require Import bedrock2.ZnWords.

Lemma halvemod_by_shifts (n : word) (i : Z) : i >= 0 -> \_ n = 8 * i -> n ^>> /_ 4 ^<< /_ 3 = /_ (8*(i / 2)) .
Proof.
  intros. ZnWords.
 Qed.

Lemma div2_sub (n : nat) : (n - S (Z.to_nat (Z.of_nat n / 2)) <= n / 2)%nat.
Proof.
  replace (Z.to_nat (Z.of_nat n / 2)) with (n / 2)%nat by ((replace 2 with (Z.of_nat 2); try reflexivity); rewrite <- Nat2Z.inj_div; rewrite Nat2Z.id; trivial).
  assert (n <= n/2 + S(n/2))%nat; try blia.
  remember (Nat.even n) as ev; destruct ev.
  - symmetry in Heqev; apply Nat.even_EvenT in Heqev; apply Nat.EvenT_Even in Heqev;
    apply Nat.Even_double in Heqev; cbv [Nat.double] in *; rewrite Nat.div2_div in *; blia.
  - rewrite <- Nat.negb_odd in Heqev; symmetry in Heqev; apply Bool.negb_false_iff in Heqev; assert (Hodd := Heqev);
    rewrite <- Nat.even_succ in Heqev; apply Nat.even_EvenT in Heqev; apply Nat.EvenT_Even in Heqev;
    apply Nat.Even_double in Heqev; cbv [Nat.double] in *; apply Nat.odd_OddT in Hodd; apply Nat.OddT_Odd in Hodd. 
    assert (S (n / 2) + S (n / 2) = S n)%nat by (apply Nat.Odd_div2 in Hodd; repeat (rewrite Nat.div2_div in *); blia); blia.
Qed.

Lemma div2_log (x y : nat) : (y > 0)%nat -> (x <= y / 2)%nat -> Z.of_nat (msb x) <= Z.of_nat (msb y) - 1.
Proof.
  intros; case (y / 2)%nat eqn:Hdiv.
  - assert (x = 0)%nat by blia; destruct y; try blia; subst x; cbv [msb]; blia.
  - destruct x; destruct y; cbv [msb]; try blia.
    assert ( S (Nat.log2 (S x)) <= Nat.log2 (S y))%nat; try blia.
    rewrite <- Nat.log2_double; try blia.
    apply Nat.log2_le_mono; rewrite <- Nat.div2_div in Hdiv. 
    assert (2 * S n <= S y)%nat; try blia; rewrite <- Hdiv; clear.
    rewrite Nat.div2_odd; blia.
Qed.

Lemma bsearch_ok : program_logic_goal_for_function! bsearch.
Proof.
  repeat straightline.

  refine (
    tailrec (HList.polymorphic_list.cons _ (HList.polymorphic_list.cons _ HList.polymorphic_list.nil)) ("left"::"right"::"target"::nil)%list%string
        (fun l xs R t m left right target mc => PrimitivePair.pair.mk
                                               (sep (array scalar (word.of_Z 8) left xs) R m /\
                                                \_ (right ^- left) = 8*Z.of_nat (Datatypes.length xs) /\
                                                List.length xs = l)
                                               (fun T M LEFT RIGHT TARGET MC => T = t /\
                                                sep (array scalar (word.of_Z 8) left xs) R M /\
                                                (MC - mc <= (Z.of_nat (msb (List.length xs))) * iterCost + endCost)%metricsH     
                                               )
                                               
        ) 
        lt _ _ _ _ _ _ _);
    cbn [reconstruct map.putmany_of_list HList.tuple.to_list
         HList.hlist.foralls HList.tuple.foralls
         HList.hlist.existss HList.tuple.existss
         HList.hlist.apply  HList.tuple.apply
         HList.hlist
         List.repeat Datatypes.length
         HList.polymorphic_list.repeat HList.polymorphic_list.length
         PrimitivePair.pair._1 PrimitivePair.pair._2] in *.

  { repeat straightline. }
  { exact lt_wf. }
  { eauto. }
  { repeat straightline.

    2: { split. 1: solve[auto]. cbv [endCost iterCost]. subst mc'.
         destruct mc0. applyAddMetricsGoal. solve_MetricLog. } (* exiting loop *)
    (* loop body *)
    rename H2 into length_rep. subst br.
    
    seprewrite @array_address_inbounds;
       [ ..|(* if expression *) exact eq_refl|letexists; letexists; split; [repeat straightline|]]. (* determines element *)
    { ZnWords. }
    { ZnWords. }
    (* split if cases *) split; repeat straightline. (* code is processed, loop-go-again goals left behind *)
    { repeat letexists. split; [repeat straightline|].
      1:split.
      2:split.
      { SeparationLogic.ecancel_assumption. }
      { ZnWordsL. }
      { cleanup_for_ZModArith. reflexivity. }
      split; repeat straightline.
      2: SeparationLogic.seprewrite_in (symmetry! @array_address_inbounds) H6.
      { ZnWordsL. }
      { ZnWords. }
      { ZnWords. }
      { trivial. }
      split.
      { SeparationLogic.ecancel_assumption. }
      { subst.
        subst metrics mc'0 metrics'0 mc'.
        apply halvemod_by_shifts in length_rep as len_div2; try ZnWords.
        subst mid.  clear v0 H H0 H1 H2 x0 x3 x5 x6 x7 x8 H6 left R m m0 M mc left'0 right target xs. 
        subst x4. rewrite len_div2 in *; clear len_div2.
        rewrite length_skipn in H7.
        replace (Z.div (@word.unsigned 64 word (@word.sub 64 word (@word.add 64 word x1 (@word.of_Z 64 word
        (Z.mul 8 (Z.div (Z.of_nat (@Datatypes.length (@word.rep 64 word) x)) 2)))) x1)) (@word.unsigned 64 word (@word.of_Z 64 word 8))) with
          (Z.of_nat (Datatypes.length x) / 2) in H7.
        2: {
          replace (@word.sub 64 word (@word.add 64 word x1 (@word.of_Z 64 word
          (Z.mul 8 (Z.div (Z.of_nat (@Datatypes.length (@word.rep 64 word) x)) 2)))) x1) with
          ((@word.of_Z 64 word (Z.mul 8 (Z.div (Z.of_nat (@Datatypes.length (@word.rep 64 word) x)) 2)))) by ZnWords.
          replace (\_ (/_ (8 * (Z.of_nat (Datatypes.length x) / 2)))) with (8 * (Z.of_nat (Datatypes.length x) / 2)) by ZnWords.
          rewrite Z.mul_comm; rewrite Z_div_mult; ZnWords.
        }
        assert (H:= div2_sub (Datatypes.length x)); apply div2_log in H; try ZnWords.
        destruct mc0; applyAddMetrics H7; cbv [iterCost endCost] in *; solve_MetricLog.                                                                                                     
      }
    }
    (* second branch of the if, very similar goals... *)
    { repeat letexists. split.
      1:split.
      2:split.
      { SeparationLogic.ecancel_assumption. }
      { ZnWordsL. }
      { cleanup_for_ZModArith. reflexivity. }
      split.
      { ZnWordsL. }
      repeat straightline.
      subst x5. SeparationLogic.seprewrite_in (symmetry! @array_address_inbounds) H6.
      { ZnWords. }
      { ZnWords. }
      { ZnWords. }
      split.
      { SeparationLogic.ecancel_assumption. }
      { subst.
        subst metrics mc'0 metrics'0 mc'.
        apply halvemod_by_shifts in length_rep as len_div2; try ZnWords.
        subst mid.  
        subst x4. rewrite len_div2 in *; clear len_div2.
        clear v0 H H0 H1 H2 x0 x3 x6 x7 x8 H6 left R m m0 M mc right target xs.
        rewrite List.firstn_length_le in H7.
        2: {
          replace (@word.sub 64 word (@word.add 64 word x1 (@word.of_Z 64 word
          (Z.mul 8 (Z.div (Z.of_nat (@Datatypes.length (@word.rep 64 word) x)) 2)))) x1) with
          ((@word.of_Z 64 word (Z.mul 8 (Z.div (Z.of_nat (@Datatypes.length (@word.rep 64 word) x)) 2)))) by ZnWords.
          replace (\_ (/_ (8 * (Z.of_nat (Datatypes.length x) / 2)))) with (8 * (Z.of_nat (Datatypes.length x) / 2)) by ZnWords.
          rewrite Z.mul_comm; rewrite Z_div_mult; ZnWords.
        }
        replace (Z.div (@word.unsigned 64 word (@word.sub 64 word (@word.add 64 word x1 (@word.of_Z 64 word
        (Z.mul 8 (Z.div (Z.of_nat (@Datatypes.length (@word.rep 64 word) x)) 2)))) x1)) (@word.unsigned 64 word (@word.of_Z 64 word 8))) with
          (Z.of_nat (Datatypes.length x) / 2) in H7.
        2: {
          replace (@word.sub 64 word (@word.add 64 word x1 (@word.of_Z 64 word
          (Z.mul 8 (Z.div (Z.of_nat (@Datatypes.length (@word.rep 64 word) x)) 2)))) x1) with
          ((@word.of_Z 64 word (Z.mul 8 (Z.div (Z.of_nat (@Datatypes.length (@word.rep 64 word) x)) 2)))) by ZnWords.
          replace (\_ (/_ (8 * (Z.of_nat (Datatypes.length x) / 2)))) with (8 * (Z.of_nat (Datatypes.length x) / 2)) by ZnWords.
          rewrite Z.mul_comm; rewrite Z_div_mult; ZnWords.
        }
        assert (H := div2_log (Z.to_nat (Z.of_nat (Datatypes.length x) / 2)) (Datatypes.length x)).
        destruct mc0; applyAddMetrics H7; cbv [iterCost endCost] in *.
        assert (Z.to_nat (Z.of_nat (Datatypes.length x) / 2) <= Datatypes.length x / 2)%nat by
        (replace 2 with (Z.of_nat 2); try reflexivity; rewrite Nat2Z.inj_le; rewrite Z2Nat.id; try rewrite Nat2Z.inj_div; ZnWords).                              
        solve_MetricLog.
      }
      Unshelve. exact (word.of_Z 5). } }
  repeat straightline. split; auto. (* postcondition *)

Qed.
