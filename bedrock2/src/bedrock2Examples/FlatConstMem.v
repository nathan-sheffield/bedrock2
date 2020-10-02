Require Import bedrock2.Syntax bedrock2.NotationsCustomEntry.
Require Import bedrock2.FE310CSemantics.

Import Syntax BinInt String Datatypes List List.ListNotations ZArith.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.
Local Coercion expr.literal : Z >-> expr.
Local Coercion expr.var : String.string >-> expr.
Local Coercion name_of_func (f : func) : String.string := fst f.

Definition silly1 : func :=
    let a := "a" in
    let b := "b" in
    let c := "c" in
  ("silly1", ([a], [c], bedrock_func_body:(
      b = load4(a + constr:(16));
      c = load4(a + constr:(14))
  ))).

Require Import coqutil.Word.Interface coqutil.Word.Properties.
Require Import bedrock2.Semantics bedrock2.ProgramLogic bedrock2.Array.
Require Import bedrock2.Map.Separation bedrock2.Map.SeparationLogic.
Require Import Coq.Lists.List coqutil.Map.OfListWord.
Import Map.Interface Interface.map OfFunc.map OfListWord.map.
Section WithParameters.
  Context {p : FE310CSemantics.parameters}.
  Add Ring wring : (Properties.word.ring_theory (word := Semantics.word))
        (preprocess [autorewrite with rew_word_morphism],
         morphism (Properties.word.ring_morph (word := Semantics.word)),
         constants [Properties.word_cst]).

  Local Instance spec_of_silly1 : spec_of "silly1" := fun functions => 
      forall t m a bs R, Z.of_nat (length bs) = 32 ->
      (sep (eq (map.of_list_word_at a bs)) R) m ->
      WeakestPrecondition.call functions silly1 t m [a]
      (fun T M rets => True).
  Require Import coqutil.Tactics.letexists.
  Require Import coqutil.Tactics.rdelta.

  Ltac ring_simplify_unsigned_goal :=
    match goal with
    |- context [word.unsigned ?x] =>
      let Hrw := fresh in
      eassert (let y := _ in x = y) as Hrw by (
        let y := fresh in
        intros y; ring_simplify;
        subst y; trivial);
      rewrite !Hrw; clear Hrw
    end.
  Ltac ring_simplify_unsigned_in H :=
    match type of H with context [word.unsigned ?x] =>
      let Hrw := fresh in
      eassert (let y := _ in x = y) as Hrw by (
        let y := fresh in
        intros y; ring_simplify;
        subst y; trivial);
      rewrite !Hrw in H; clear Hrw
    end.
  Ltac ring_simplify_unsigned :=
    try ring_simplify_unsigned_goal;
    repeat match goal with
           | H: context [word.unsigned ?x] |- _ => ring_simplify_unsigned_in H
           end.

  Ltac unify_and_change lhs rhs :=
    let rhs := match rhs with ?x => x end in
    let __ := constr:(eq_refl : lhs = rhs) in
    change lhs with rhs in *.

  Require Import bedrock2.AbsintWordToZ.

  Ltac change_with_Z_literal W :=
    first [ let e := open_constr:(BinInt.Zpos _) in
            unify_and_change W e;
            requireZcst e
          | unify_and_change W open_constr:(BinInt.Z0)
          | let e := open_constr:(BinInt.Zneg _) in
            unify_and_change W e;
            requireZcst e].

  Ltac simplify_ZcstExpr_goal :=
    match goal with
    |- context [?e] =>
        requireZcstExpr e;
        let Hrw := fresh in
        time eassert (e = _) by (vm_compute; reflexivity);
        idtac "simplified" e "in GOAL";
        progress rewrite Hrw; clear Hrw
    end.

  Ltac simplify_ZcstExpr_in H :=
    match type of H with context [?e] =>
        requireZcstExpr e;
        let Hrw := fresh in
        eassert (e = _) by (vm_compute; reflexivity);
        idtac "simplified" e "in" H;
        progress rewrite Hrw in H; clear Hrw
    end.

  Ltac simplify_ZcstExpr_hyps :=
    repeat match goal with H : _ |- _ => simplify_ZcstExpr_in H end.

  Ltac simplify_ZcstExpr :=
    simplify_ZcstExpr_hyps; try simplify_ZcstExpr_goal.

  Ltac rewrite_unsigned_of_Z_goal :=
    match goal with
    |- context [@word.unsigned ?w ?W ?X] =>
      let E := constr:(@word.unsigned w W X) in
      let x := rdelta X in
      let z := match x with word.of_Z ?z => z end in
      rewrite ((@word.unsigned_of_Z w W _ z) : E = z mod 2^w)
    end.

  Ltac wordcstexpr_tac := (* hacky *)
    repeat first
          [ progress ring_simplify_unsigned
          | rewrite !word.unsigned_add; cbv [word.wrap]
          | rewrite_unsigned_of_Z_goal ];
    try change_with_Z_literal width; repeat simplify_ZcstExpr_goal; trivial.

  Lemma List__splitZ_spec [A] (xsys : list A) i (H : 0 <= i < Z.of_nat (length xsys)) :
    let xs := firstn (Z.to_nat i) xsys in
    let ys := skipn (Z.to_nat i) xsys in
    xsys = xs ++ ys /\
    Z.of_nat (length xs) = i /\
    Z.of_nat (length ys) = Z.of_nat (length xsys) - i.
  Proof.
    pose proof eq_sym (firstn_skipn (Z.to_nat i) xsys).
    split; trivial.
    rewrite length_firstn_inbounds, length_skipn; Lia.lia.
  Qed.

  Ltac flatten_hyps :=
    repeat match goal with
           | H : let x := ?v in ?C |- _ =>
               let X := fresh x in
               pose v as X;
               let C := constr:(match X with x => C end) in
               change C in H
           | H : _ /\ _ |- _ => destruct H
           | H : exists _, _ |- _ => destruct H
           end.

  Lemma List__splitZ_spec_n [A] (xsys : list A) i n
    (Hn : Z.of_nat (length xsys) = n) (H : 0 <= i < n) :
    let xs := firstn (Z.to_nat i) xsys in
    let ys := skipn (Z.to_nat i) xsys in
    xsys = xs ++ ys /\
    Z.of_nat (length xs) = i /\
    Z.of_nat (length ys) = n - i.
  Proof.
    pose proof eq_sym (firstn_skipn (Z.to_nat i) xsys).
    split; trivial.
    rewrite length_firstn_inbounds, length_skipn; Lia.lia.
  Qed.


  Require Import coqutil.Tactics.rewr.
  Ltac List__splitZ bs n :=
      match goal with H: Z.of_nat (length bs) = _ |- _ =>
          pose proof List__splitZ_spec_n bs n _ H ltac:(Lia.lia);
          clear H; flatten_hyps; simplify_ZcstExpr;
          let Hrw := lazymatch goal with H : bs = _ ++ _ |- _ => H end in
          let eqn := type of Hrw in
          rewr ltac:(fun t => match t with
                              | eqn => fail 1
                              | _ => constr:(Hrw) end) in *
      end.

  Lemma map__of_list_word_at_app_n  [value] [map : map.map word value] {ok : map.ok map}
    (a : word) (xs ys : list value)
    lxs (Hlxs : Z.of_nat (length xs) = lxs)
    : map.of_list_word_at a (xs ++ ys)
    = putmany (map.of_list_word_at (word.add a (word.of_Z lxs)) ys) (map.of_list_word_at a xs).
  Proof. subst lxs; apply map.of_list_word_at_app. Qed.

  Lemma map__adjacent_arrays_disjoint_n [value] [map : map.map word value] {ok : map.ok map}
    (a : word) (xs ys : list value)
    lxs (Hlxs : Z.of_nat (length xs) = lxs)
    (H :Z.of_nat (length xs) + Z.of_nat (length ys) <= 2 ^ width)
    : disjoint (map.of_list_word_at (word.add a (word.of_Z lxs)) ys) (map.of_list_word_at a xs).
  Proof. subst lxs. auto using map.adjacent_arrays_disjoint. Qed.

      Declare Scope word_scope.
      Bind Scope word_scope with word.
      Delimit Scope word_scope with word.
      Local Notation "a + b" := (word.add a b) (at level 50, left associativity, format "a + b") : word_scope.
      Local Infix "-" := word.sub : word_scope.
      Local Coercion Z.of_nat : nat >-> Z.
      Local Infix "$+" := putmany (at level 70).
      Local Notation "xs $@ a" := (map.of_list_word_at a%word xs) (at level 10, format "xs $@ a").
      Local Notation "! x" := (word.of_Z x) (at level 10, format "! x").
      Local Notation "a * b" := (sep a%type b%type) : type_scope.
      Local Open Scope word_scope.

  Lemma sep_eq_putmany [key value] [map : map.map key value] (a b : map) (H : disjoint a b) : Lift1Prop.iff1 (eq (a $+ b)) (sep (eq a) (eq b)).
  Proof.
    split.
    { intros; subst. eexists _, _; eauto using Properties.map.split_disjoint_putmany. }
    { intros (?&?&(?&?)&?&?); subst; trivial. }
  Qed.

  Lemma sep_eq_of_list_word_at_app [value] [map : map.map word value] {ok : map.ok map}
    (a : word) (xs ys : list value)
    lxs (Hlxs : Z.of_nat (length xs) = lxs) (Htotal : length xs + length ys <= 2^width)
    : Lift1Prop.iff1 (eq (map.of_list_word_at a (xs ++ ys)))
      (sep (eq (map.of_list_word_at a xs)) (eq (map.of_list_word_at (word.add a (word.of_Z lxs)) ys))).
  Proof.
    etransitivity.
    2: eapply sep_comm.
    etransitivity.
    2: eapply sep_eq_putmany, map__adjacent_arrays_disjoint_n; trivial.
    erewrite map__of_list_word_at_app_n by eauto; reflexivity.
  Qed.

  Lemma list_word_at_app_of_adjacent_eq [value] [map : map.map word value] {ok : map.ok map}
    (a b : word) (xs ys : list value)
    (Hl: word.unsigned (word.sub b a) = Z.of_nat (length xs))
    (Htotal : length xs + length ys <= 2^width)
    : Lift1Prop.iff1
        (sep (eq (map.of_list_word_at a xs)) (eq (map.of_list_word_at b ys)) )
        (eq (map.of_list_word_at a (xs ++ ys))).
  Proof.
    etransitivity.
    2:symmetry; eapply sep_eq_of_list_word_at_app; trivial.
    do 3 Morphisms.f_equiv. rewrite <-Hl, word.of_Z_unsigned. ring.
  Qed.

  Lemma of_list_word_nil k : []$@k = empty.
  Proof. apply Properties.map.fold_empty. Qed.
  Lemma of_list_word_singleton k v : [v]$@k = put empty k v.
  Proof.
    cbv [of_list_word_at of_list_word seq length List.map of_func update].
    rewrite word.unsigned_of_Z_0, Z2Nat.inj_0; cbv [MapKeys.map.map_keys nth_error].
    rewrite Properties.map.fold_singleton.
    f_equal; cbn [Z.of_nat].
    eapply word.unsigned_inj; rewrite word.unsigned_add; cbv [word.wrap]; rewrite word.unsigned_of_Z_0, Z.add_0_r, Z.mod_small; trivial; eapply word.unsigned_range.
  Qed.
    
  Import ptsto_bytes Lift1Prop Morphisms.
  Lemma eq_of_list_word_iff_array1 a bs
    (H : length bs <= 2 ^ 32) :
    iff1 (eq(bs$@a)) (array ptsto (word.of_Z 1) a bs).
  Proof.
    revert H; revert a; induction bs; cbn [array]; intros.
    { rewrite of_list_word_nil; cbv [emp iff1]; intuition auto. }
    { etransitivity.
      2: eapply Proper_sep_iff1.
      3: eapply IHbs.
      2: reflexivity.
      2: cbn [length] in H; Lia.lia.
      change (a::bs) with ([a]++bs).
      rewrite of_list_word_at_app.
      etransitivity.
      1: eapply sep_eq_putmany, adjacent_arrays_disjoint; cbn [length] in *; Lia.lia.
      etransitivity.
      2:eapply sep_comm.
      f_equiv.
      rewrite of_list_word_singleton.
      cbv [ptsto iff1]; intuition auto. }
  Qed.

  Ltac ring_simplify_address_in H :=
    match type of H with context [_ $@ ?x] =>
      let Hrw := fresh in
      eassert (let y := _ in x = y) as Hrw by (
        let y := fresh in
        intros y; ring_simplify;
        subst y; trivial);
      rewrite !Hrw in H; clear Hrw
    end.

  Lemma silly1_ok : program_logic_goal_for_function! silly1.
  Proof.
    repeat straightline.
    assert (0 <= 32 < 2^32) by Lia.lia.

    letexists. split.
    { repeat straightline.
      eexists; split; trivial.
      assert (word.unsigned (word.sub (word.add a v0) a) <= Z.of_nat 32) by wordcstexpr_tac.
      assert (word.unsigned (word.sub (word.add (word.add a v0) (word.of_Z 4)) a) <= Z.of_nat 32) by wordcstexpr_tac.

      Time List__splitZ bs 16.
      seprewrite_in sep_eq_of_list_word_at_app H0;
        try eassumption; try (change_with_Z_literal width; Lia.lia).

      Time List__splitZ ys 4.
      seprewrite_in sep_eq_of_list_word_at_app H6;
        try eassumption; try (change_with_Z_literal width; Lia.lia).
        
      ring_simplify_address_in H8.

      (* paramrecords... probably resolved by properly generalizing the lemma
      Set Printing Implicit.
      seprewrite_in open_constr:(eq_of_list_word_iff_array1 _ _ _) H8.
      *)

      seprewrite_in_by list_word_at_app_of_adjacent_eq H8 ltac:(
        rewrite ?app_length; wordcstexpr_tac; change_with_Z_literal width; simplify_ZcstExpr; Lia.lia).

      seprewrite_in_by (list_word_at_app_of_adjacent_eq a) H7 ltac:(
        rewrite ?app_length; wordcstexpr_tac; change_with_Z_literal width; simplify_ZcstExpr; Lia.lia).

      rewrite <-H in H8.

  Abort.
End WithParameters.
