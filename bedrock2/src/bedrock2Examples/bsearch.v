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

Definition nth(l: list word)(n: nat): word := List.nth n l (word.of_Z 0).

Fixpoint In {A: Type} (a:A) (l:list A) : Prop :=
    match l with
      | nil => False
      | cons b m => b = a \/ In a m
end.

 Definition Sorted(l: list word): Prop :=
    forall i j: nat, (i < j < List.length l)%nat ->
                     word.unsigned (nth l i) <= word.unsigned (nth l j).

 Lemma sorted_in_window (l : list word) (target : word) (lower_indx : nat) (upper_indx : nat) :
   In target l -> word.unsigned (nth l lower_indx) <= word.unsigned target <= word.unsigned (nth l lower_indx) -> exists target_indx,
       Z.of_nat lower_indx <= Z.of_nat target_indx <= Z.of_nat upper_indx /\ nth l target_indx = target
 .
   Proof. Admitted.

#[export] Instance spec_of_bsearch : spec_of "bsearch"%string := fun functions =>
  forall left right target xs R t m mc,
    sep (array scalar (word.of_Z 8) left xs) R m ->
    \_ (right ^- left) = 8*Z.of_nat (Datatypes.length xs) ->
    WeakestPrecondition.call functions
      "bsearch"%string t m (left::right::target::nil)%list mc
      (fun t' m' rets mc' => t=t' /\ sep (array scalar (word.of_Z 8) left xs) R m' /\ 
       (mc' - mc <= Z.of_nat (Nat.log2 (Datatypes.length xs)) * iterCost + endCost)%metricsH                               
      ).


From coqutil.Tactics Require Import eabstract letexists rdelta.
From coqutil.Macros Require Import symmetry.
Import PrimitivePair.
Require Import bedrock2.ZnWords.

Lemma halvemod_by_shifts (n : word) (i : Z) : \_ n = 8 * i -> n ^>> /_ 4 ^<< /_ 3 = /_ (8*(i / 2)) .
Proof.
  intros.
  assert (n = /_ (8 * i)) by ZnWords; subst n.

  Admitted.

Lemma div2_sub (n : nat) : (n - S (Z.to_nat (Z.of_nat n / 2)) <= n / 2)%nat.
Proof.
Admitted.

Lemma div2_sub_lies (n : nat) : (n - (Z.to_nat (Z.of_nat n / 2)) <= n / 2)%nat.
Proof.
Admitted.


Lemma div2_log (x y : nat) : (x <= y / 2)%nat -> Z.of_nat (Nat.log2 x) <= Z.of_nat (Nat.log2 y) - 1.
Proof. Admitted.


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
                                                (MC - mc <= (Z.of_nat (Nat.log2 (List.length xs))) * iterCost + endCost)%metricsH     
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
        apply halvemod_by_shifts in length_rep as len_div2.
        subst mid.  clear v0 H H0 H1 H2 H4 x0 x3 x5 x6 x7 x8 H6 left R m m0 M mc left'0 right target xs. 
        subst x4. rewrite len_div2 in *; clear len_div2.
        rewrite length_skipn in H7.
        replace (Z.div
                                 (@word.unsigned 64 word
                                    (@word.sub 64 word
                                       (@word.add 64 word x1
                                          (@word.of_Z 64 word
                                             (Z.mul 8 (Z.div (Z.of_nat (@Datatypes.length (@word.rep 64 word) x)) 2)))) x1))
                                 (@word.unsigned 64 word (@word.of_Z 64 word 8))) with
          (Z.of_nat (Datatypes.length x) / 2)
          in H7.
        2: {
          replace (@word.sub 64 word
                                       (@word.add 64 word x1
                                          (@word.of_Z 64 word
                                             (Z.mul 8 (Z.div (Z.of_nat (@Datatypes.length (@word.rep 64 word) x)) 2)))) x1) with ((@word.of_Z 64 word
                                             (Z.mul 8 (Z.div (Z.of_nat (@Datatypes.length (@word.rep 64 word) x)) 2)))) by ZnWords.
          replace (\_ (/_ (8 * (Z.of_nat (Datatypes.length x) / 2)))) with (8 * (Z.of_nat (Datatypes.length x) / 2)) by ZnWords.
          rewrite Z.mul_comm; rewrite Z_div_mult; ZnWords.
        }
        
        assert (H:= div2_sub (Datatypes.length x)).
        apply div2_log in H.

        destruct mc0.
        
        applyAddMetrics H7. cbv [iterCost endCost] in *.
        solve_MetricLog.
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
        apply halvemod_by_shifts in length_rep as len_div2.
        subst mid.  
        subst x4. rewrite len_div2 in *; clear len_div2.
        clear v0 H H0 H1 H2 H4 x0 x3 x6 x7 x8 H6 left R m m0 M mc right target xs.

        rewrite List.firstn_length_le in H7.
        2: {
          replace (@word.sub 64 word
                                       (@word.add 64 word x1
                                          (@word.of_Z 64 word
                                             (Z.mul 8 (Z.div (Z.of_nat (@Datatypes.length (@word.rep 64 word) x)) 2)))) x1) with ((@word.of_Z 64 word
                                             (Z.mul 8 (Z.div (Z.of_nat (@Datatypes.length (@word.rep 64 word) x)) 2)))) by ZnWords.
          replace (\_ (/_ (8 * (Z.of_nat (Datatypes.length x) / 2)))) with (8 * (Z.of_nat (Datatypes.length x) / 2)) by ZnWords.
          rewrite Z.mul_comm; rewrite Z_div_mult; ZnWords.
        }
        

        replace (Z.div
                                 (@word.unsigned 64 word
                                    (@word.sub 64 word
                                       (@word.add 64 word x1
                                          (@word.of_Z 64 word
                                             (Z.mul 8 (Z.div (Z.of_nat (@Datatypes.length (@word.rep 64 word) x)) 2)))) x1))
                                 (@word.unsigned 64 word (@word.of_Z 64 word 8))) with
          (Z.of_nat (Datatypes.length x) / 2)
          in H7.
        2: {
          replace (@word.sub 64 word
                                       (@word.add 64 word x1
                                          (@word.of_Z 64 word
                                             (Z.mul 8 (Z.div (Z.of_nat (@Datatypes.length (@word.rep 64 word) x)) 2)))) x1) with ((@word.of_Z 64 word
                                             (Z.mul 8 (Z.div (Z.of_nat (@Datatypes.length (@word.rep 64 word) x)) 2)))) by ZnWords.
          replace (\_ (/_ (8 * (Z.of_nat (Datatypes.length x) / 2)))) with (8 * (Z.of_nat (Datatypes.length x) / 2)) by ZnWords.
          rewrite Z.mul_comm; rewrite Z_div_mult; ZnWords.
        }

        assert (H := div2_log (Z.to_nat (Z.of_nat (Datatypes.length x) / 2)) (Datatypes.length x)).
   

        destruct mc0.
        
        applyAddMetrics H7. cbv [iterCost endCost] in *.
        assert (Z.to_nat (Z.of_nat (Datatypes.length x) / 2) <= Datatypes.length x / 2)%nat by
        (replace 2 with (Z.of_nat 2); try reflexivity; rewrite Nat2Z.inj_le; rewrite Z2Nat.id; try rewrite Nat2Z.inj_div; ZnWords).                              
        solve_MetricLog.
      }
      Unshelve. exact (word.of_Z 5). } }

  repeat straightline. split; auto. (* postcondition *)
 
Qed.

 (*
#[export] Instance spec_of_bsearch : spec_of "bsearch"%string := fun functions =>
  forall left right target xs R t m mc,
    sep (array scalar (word.of_Z 8) left xs) R m ->
    \_ (right ^- left) = 8*Z.of_nat (Datatypes.length xs) ->
    WeakestPrecondition.call functions
      "bsearch"%string t m (left::right::target::nil)%list mc
      (fun t' m' rets mc' => t=t' /\ sep (array scalar (word.of_Z 8) left xs) R m' /\ exists i, rets = (i::nil)%list /\
      (Sorted xs -> List.In target xs -> nth xs (Z.to_nat (( \_ i -  \_ left) / 8)) = target) /\
       (mc' - mc <= initCost + Z.of_nat (Nat.log2 (Datatypes.length xs)) * iterCost + endCost)%metricsH                               
      ).


From coqutil.Tactics Require Import eabstract letexists rdelta.
From coqutil.Macros Require Import symmetry.
Import PrimitivePair.
Require Import bedrock2.ZnWords.

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
                                                Sorted xs -> List.In target xs -> exists target_index,
                                                ( \_ LEFT <= (Z.of_nat target_index) *  8 + \_ left <= \_ RIGHT /\ nth xs target_index = target) /\
                                                (MC - mc <= (Z.of_nat (Nat.log2 l)) * iterCost + endCost)%metricsH     
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
    2: {  }

    
    2: solve [auto].  (* exiting loop *)
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
      { SeparationLogic.ecancel_assumption. } }
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
      { SeparationLogic.ecancel_assumption. } } }
  repeat straightline.
  repeat apply conj; auto; []. (* postcondition *)
  letexists. split.
  { exact eq_refl. }
  repeat(split).
  { auto. }
  { eauto. }

  Unshelve.
  all: exact (word.of_Z 0).

  all:fail "remaining subgoals".
Qed.
*)

(*

#[export] Instance spec_of_bsearch : spec_of "bsearch"%string := fun functions =>
  forall left right target xs R t m mc,
    sep (array scalar (word.of_Z 8) left xs) R m ->
    \_ (right ^- left) = 8*Z.of_nat (Datatypes.length xs) ->
    WeakestPrecondition.call functions
      "bsearch"%string t m (left::right::target::nil)%list mc
      (fun t' m' rets mc' => t=t' /\ sep (array scalar (word.of_Z 8) left xs) R m' /\ exists i, rets = (i::nil)%list /\
      ((*sorted*)False -> True)                                      
      ).


From coqutil.Tactics Require Import eabstract letexists rdelta.
From coqutil.Macros Require Import symmetry.
Import PrimitivePair.
Require Import bedrock2.ZnWords.

Lemma bsearch_ok : program_logic_goal_for_function! bsearch.
Proof.
  repeat straightline.

  refine (
    tailrec (HList.polymorphic_list.cons _ (HList.polymorphic_list.cons _ HList.polymorphic_list.nil)) ("left"::"right"::"target"::nil)%list%string
        (fun l xs R t m left right target mc => PrimitivePair.pair.mk
                                               (sep (array scalar (word.of_Z 8) left xs) R m /\
                                                \_ (right ^- left) = 8*Z.of_nat (Datatypes.length xs) /\
                                                List.length xs = l)
                                               (fun T M LEFT RIGHT TARGET MC => T = t /\ sep (array scalar (word.of_Z 8) left xs) R M
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
    2: solve [auto].  (* exiting loop *)
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
      { SeparationLogic.ecancel_assumption. } }
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
      { SeparationLogic.ecancel_assumption. } } }
  repeat straightline.
  repeat apply conj; auto; []. (* postcondition *)
  letexists. split.
  { exact eq_refl. }
  repeat(split).
  { auto. }
  { eauto. }

  Unshelve.
  all: exact (word.of_Z 0).

  all:fail "remaining subgoals".
Qed.
(* Print Assumptions bsearch_ok. *)
(* Closed under the global context *)
*)
