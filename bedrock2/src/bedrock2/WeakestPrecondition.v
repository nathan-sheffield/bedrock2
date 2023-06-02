Require Import coqutil.Macros.subst coqutil.Macros.unique bedrock2.Notations coqutil.Map.Interface coqutil.Map.OfListWord.
Require Import Coq.ZArith.BinIntDef coqutil.Word.Interface coqutil.Word.Bitwidth.
Require Import coqutil.dlet bedrock2.Syntax bedrock2.Semantics.
Require Import bedrock2.MetricLogging.

Section WeakestPrecondition.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}.
  Context {locals: map.map String.string word}.
  Context {env: map.map String.string (list String.string * list String.string * cmd)}.
  Context {ext_spec: ExtSpec}.
  Implicit Types (t : trace) (m : mem) (l : locals).

Local Notation metrics := MetricLog.

  Definition literal v mc (post : (word * metrics) -> Prop) : Prop :=
    dlet! v := word.of_Z v in post (v, addMetricInstructions 8 (addMetricLoads 8 mc)).
  Definition get (l : locals) (x : String.string) mc (post : (word * metrics) -> Prop) : Prop :=
    bind_ex_Some v <- map.get l x; post (v, addMetricInstructions 1 (addMetricLoads 2 mc)).
  Definition load s m a mc (post : (word * metrics) -> Prop) : Prop :=
    bind_ex_Some v <- load s m a; post (v, addMetricInstructions 1 (addMetricLoads 2 mc)).
  Definition store sz m a v post :=
    bind_ex_Some m <- store sz m a v; post m.

  Section WithMemAndLocals.
    Context (m : mem) (l : locals).
    Definition expr_body (rec : _->_->(word*metrics->Prop)->Prop) (e : Syntax.expr) (mc : metrics) (post : word * metrics -> Prop) : Prop :=
      match e with
      | expr.literal v =>
        literal v mc post
      | expr.var x =>
        get l x mc post
      | expr.op op e1 e2 =>
        rec e1 mc (fun '(v1, mc') =>
        rec e2 mc' (fun '(v2, mc'') =>
        post (interp_binop op v1 v2, addMetricInstructions 2 (addMetricLoads 2 mc''))))
      | expr.load s e =>
       rec e mc (fun '(a, mc') =>
        load s m a mc' post)
      | expr.inlinetable s t e =>
         rec e mc (fun '(a, mc') =>
        load s (map.of_list_word t) a (addMetricInstructions 2
                                      (addMetricLoads 2
                                      (addMetricJumps 1 mc'))) post)
      | expr.ite c e1 e2 =>
        rec c mc (fun '(b, mc') => rec (if word.eqb b (word.of_Z 0) then e2 else e1) (addMetricInstructions 2 (addMetricLoads 2 (addMetricJumps 1 mc'))) post) 
    end.
    Fixpoint expr e := expr_body expr e.
  End WithMemAndLocals.

  Section WithF.
    Context {A B} (f: A -> metrics -> (B * metrics -> Prop) -> Prop).
    Definition list_map_body rec (xs : list A) (mc : metrics) (post : list B * metrics -> Prop) : Prop :=
      match xs with
      | nil => post (nil, mc)
      | cons x xs' =>
        f x mc (fun '(y, mc') =>
        rec xs' mc' (fun '(ys', mc'') =>
        post (cons y ys', mc'')))
      end.
    Fixpoint list_map xs := list_map_body list_map xs.
  End WithF.

  Section WithFunctions.
    Context (call : String.string -> trace -> mem -> list word -> metrics -> (trace -> mem -> list word -> metrics -> Prop) -> Prop).
    Definition dexpr m l e mc vmc := expr m l e mc (eq vmc).
    Definition dexprs m l es mc vmcs := list_map (expr m l) es mc (eq vmcs).
    Definition cmd_body (rec:_->_->_->_->_->_->Prop) (c : cmd) (t : trace) (m : mem) (l : locals) (mc : metrics)
             (post : trace -> mem -> locals -> metrics -> Prop) : Prop :=
      (* give value of each pure expression when stating its subproof *)
      match c with
      | cmd.skip => post t m l mc
      | cmd.set x ev =>
        bind_ex_pair (v, mc') <- dexpr m l ev mc;
        dlet! l := map.put l x v in
        post t m l (addMetricInstructions 1 (addMetricLoads 1 mc'))
      | cmd.unset x =>
        dlet! l := map.remove l x in
        post t m l mc
      | cmd.store sz ea ev =>
        bind_ex_pair (a, mc') <- dexpr m l ea mc;
        bind_ex_pair (v, mc'') <- dexpr m l ev mc';
        store sz m a v (fun m =>
        post t m l (addMetricInstructions 1 (addMetricLoads 1 (addMetricStores 1 mc''))))
      | cmd.stackalloc x n c =>
        Z.modulo n (bytes_per_word width) = 0 /\
        forall a mStack mCombined,
          anybytes a n mStack -> map.split mCombined m mStack ->
          dlet! l := map.put l x a in
          rec c t mCombined l (addMetricInstructions 1 (addMetricLoads 1 mc))
          (fun t' mCombined' l' mc' =>
          exists m' mStack',
          anybytes a n mStack' /\ map.split mCombined' m' mStack' /\
          post t' m' l' mc')
      | cmd.cond br ct cf =>
        bind_ex_pair (v, mc') <- dexpr m l br mc;
        dlet! mc'' := addMetricInstructions 2 (addMetricLoads 2 (addMetricJumps 1 mc')) in
        (word.unsigned v <> 0%Z -> rec ct t m l mc'' post) /\
        (word.unsigned v = 0%Z -> rec cf t m l mc'' post)
      | cmd.seq c1 c2 =>
        rec c1 t m l mc (fun t m l mc => rec c2 t m l mc post)
      | cmd.while e c =>
        exists measure (lt:measure->measure->Prop) (inv:measure->trace->mem->locals->metrics->Prop),
        Coq.Init.Wf.well_founded lt /\
        (exists v, inv v t m l mc) /\
        (forall v t m l mc, inv v t m l mc ->
          bind_ex_pair (b, mc') <- dexpr m l e mc;
          (word.unsigned b <> 0%Z -> rec c t m l mc' (fun t' m' l' mc'' =>
            exists v', inv v' t' m' l' (addMetricInstructions 2
                                       (addMetricLoads 2
                                       (addMetricJumps 1 mc''))) /\ lt v' v)) /\
          (word.unsigned b = 0%Z -> post t m l (addMetricInstructions 1
                                               (addMetricLoads 1
                                               (addMetricJumps 1 mc')))))
      | cmd.call binds fname arges =>
        bind_ex_pair (args, mc') <- dexprs m l arges mc;
        call fname t m args mc' (fun t m rets mc'' =>
          bind_ex_Some l <- map.putmany_of_list_zip binds rets l;
          post t m l (addMetricInstructions 100 (addMetricJumps 100 (addMetricLoads 100 (addMetricStores 100 mc'')))))
      | cmd.interact binds action arges =>
        bind_ex_pair (args, mc') <- dexprs m l arges mc;
        exists mKeep mGive, map.split m mKeep mGive /\
        ext_spec t mGive action args (fun mReceive rets =>
          bind_ex_Some l' <- map.putmany_of_list_zip binds rets l;
          forall m', map.split m' mKeep mReceive ->
          post (cons ((mGive, action, args), (mReceive, rets)) t) m' l' (addMetricInstructions 1
                                                                        (addMetricStores 1
                                                                        (addMetricLoads 2 mc'))))
      end.
    Fixpoint cmd c := cmd_body cmd c.
  End WithFunctions.

Definition func call '(innames, outnames, c) (t : trace) (m : mem) (args : list word) (mc : metrics) (post : trace -> mem -> list word -> metrics -> Prop) :=
      bind_ex_Some l <- map.of_list_zip innames args;
      cmd call c t m l mc (fun t m l mc =>
        (* this list_map is only used proof-side and not actually executed in the program, so ignore the new metrics *)
        list_map (get l) outnames mc (fun '(rets, _) =>
                                        post t m rets mc

        )).


  Definition call_body rec (functions : list (String.string * (list String.string * list String.string * cmd.cmd)))
                (fname : String.string) (t : trace) (m : mem) (args : list word) (mc: metrics)
                (post : trace -> mem -> list word -> metrics -> Prop) : Prop :=
    match functions with
    | nil => False
    | cons (f, decl) functions =>
      if String.eqb f fname
      then func (rec functions) decl t m args mc post
      else rec functions fname t m args mc post
    end.
  Fixpoint call functions := call_body call functions.

  Definition program funcs main t m l mc post : Prop := cmd (call funcs) main t m l mc post.
End WeakestPrecondition.

Ltac unfold1_cmd e :=
  lazymatch e with
    @cmd ?width ?BW ?word ?mem ?locals ?ext_spec ?CA ?c ?t ?m ?l ?mc ?post =>
    let c := eval hnf in c in
    constr:(@cmd_body width BW word mem locals ext_spec CA
                      (@cmd width BW word mem locals ext_spec CA) c t m l mc post)
  end.
Ltac unfold1_cmd_goal :=
  let G := lazymatch goal with |- ?G => G end in
  let G := unfold1_cmd G in
  change G.

Ltac unfold1_expr e :=
  lazymatch e with
    @expr ?width ?word ?mem ?locals ?m ?l ?arg ?mc ?post =>
    let arg := eval hnf in arg in
    constr:(@expr_body width word mem locals m l (@expr width word mem locals m l) arg mc post)
  end.
Ltac unfold1_expr_goal :=
  let G := lazymatch goal with |- ?G => G end in
  let G := unfold1_expr G in
  change G.

Ltac unfold1_list_map e :=
  lazymatch e with
    @list_map ?A ?B ?P ?arg ?mc ?post =>
    let arg := eval hnf in arg in
    constr:(@list_map_body A B P (@list_map A B P) arg mc post)
  end.
Ltac unfold1_list_map_goal :=
  let G := lazymatch goal with |- ?G => G end in
  let G := unfold1_list_map G in
  change G.

Ltac unfold1_call e :=
  lazymatch e with
    @call ?width ?BW ?word ?mem ?locals ?ext_spec ?fs ?fname ?t ?m ?l ?mc ?post =>
    let fs := eval hnf in fs in
    constr:(@call_body width BW word mem locals ext_spec
                       (@call width BW word mem locals ext_spec) fs fname t m l mc post)
  end.
Ltac unfold1_call_goal :=
  let G := lazymatch goal with |- ?G => G end in
  let G := unfold1_call G in
  change G.

Import Coq.ZArith.ZArith.

Notation "'fnspec!' name a0 .. an '/' g0 .. gn '~>' r0 .. rn ',' '{' 'requires' tr mem mc := pre ';' 'ensures' tr' mem' mc' ':=' post '}'" :=
  (fun functions =>
     (forall a0,
        .. (forall an,
              (forall g0,
                  .. (forall gn,
                         (forall tr mem mc,
                             pre ->
                             WeakestPrecondition.call
                               functions name tr mem (cons a0 .. (cons an nil) ..) mc
                               (fun tr' mem' rets mc' =>
                                  (exists r0,
                                      .. (exists rn,
                                             rets = (cons r0 .. (cons rn nil) ..) /\
                                             post) ..)))) ..)) ..))
    (at level 200,
     name at level 0,
     a0 binder, an binder,
     g0 binder, gn binder,
     r0 closed binder, rn closed binder,
     tr name, tr' name, mem name, mem' name, mc name, mc' name,
     pre at level 200,
     post at level 200).

Notation "'fnspec!' name a0 .. an '/' g0 .. gn ',' '{' 'requires' tr mem mc := pre ';' 'ensures' tr' mem' mc' ':=' post '}'" :=
  (fun functions =>
     (forall a0,
        .. (forall an,
              (forall g0,
                  .. (forall gn,
                         (forall tr mem mc,
                             pre ->
                             WeakestPrecondition.call
                               functions name tr mem (cons a0 .. (cons an nil) ..) mc
                               (fun tr' mem' rets mc' =>
                                  rets = nil /\ post))) ..)) ..))
    (at level 200,
     name at level 0,
     a0 binder, an binder,
     g0 binder, gn binder,
     tr name, tr' name, mem name, mem' name, mc name, mc' name,
     pre at level 200,
     post at level 200).

Notation "'fnspec!' name a0 .. an '~>' r0 .. rn ',' '{' 'requires' tr mem mc := pre ';' 'ensures' tr' mem' mc' ':=' post '}'" :=
  (fun functions =>
     (forall a0,
        .. (forall an,
               (forall tr mem mc,
                   pre ->
                   WeakestPrecondition.call
                     functions name tr mem (cons a0 .. (cons an nil) ..) mc
                     (fun tr' mem' rets mc' =>
                        (exists r0,
                            .. (exists rn,
                                   rets = (cons r0 .. (cons rn nil) ..) /\
                                   post) ..)))) ..))
    (at level 200,
     name at level 0,
     a0 binder, an binder,
     r0 closed binder, rn closed binder,
     tr name, tr' name, mem name, mem' name, mc name, mc' name,
     pre at level 200,
     post at level 200).

Notation "'fnspec!' name '/' g0 .. gn '~>' r0 .. rn ',' '{' 'requires' tr mem mc := pre ';' 'ensures' tr' mem' mc' ':=' post '}'" :=
  (fun functions =>
        (forall an,
              (forall g0,
                  .. (forall gn,
                         (forall tr mem mc,
                             pre ->
                             WeakestPrecondition.call
                               functions name tr mem nil mc
                               (fun tr' mem' rets mc' =>
                                  (exists r0,
                                      .. (exists rn,
                                             rets = (cons r0 .. (cons rn nil) ..) /\
                                             post) ..)))) ..)))
    (at level 200,
     name at level 0,
     g0 binder, gn binder,
     r0 closed binder, rn closed binder,
     tr name, tr' name, mem name, mem' name, mc name, mc' name,
     pre at level 200,
     post at level 200).

Notation "'fnspec!' name a0 .. an ',' '{' 'requires' tr mem mc := pre ';' 'ensures' tr' mem' mc' ':=' post '}'" :=
  (fun functions =>
     (forall a0,
        .. (forall an,
               (forall tr mem mc,
                   pre ->
                   WeakestPrecondition.call
                     functions name tr mem (cons a0 .. (cons an nil) ..) mc
                     (fun tr' mem' rets mc' =>
                        rets = nil /\ post))) ..))
    (at level 200,
     name at level 0,
     a0 binder, an binder,
     tr name, tr' name, mem name, mem' name, mc name, mc' name,
     pre at level 200,
     post at level 200).

Notation "'fnspec!' name '/' g0 .. gn ',' '{' 'requires' tr mem mc := pre ';' 'ensures' tr' mem' mc' ':=' post '}'" :=
  (fun functions =>
              (forall g0,
                  .. (forall gn,
                         (forall tr mem mc,
                             pre ->
                             WeakestPrecondition.call
                               functions name tr mem nil mc
                               (fun tr' mem' rets mc' =>
                                  rets = nil /\ post))) ..))
    (at level 200,
     name at level 0,
     g0 binder, gn binder,
     tr name, tr' name, mem name, mem' name, mc name, mc' name,
     pre at level 200,
     post at level 200).

Notation "'fnspec!' name '~>' r0 .. rn ',' '{' 'requires' tr mem mc := pre ';' 'ensures' tr' mem' mc' ':=' post '}'" :=
  (fun functions =>
     (forall tr mem mc,
         pre ->
         WeakestPrecondition.call
           functions name tr mem nil mc
           (fun tr' mem' rets mc' =>
              (exists r0,
                  .. (exists rn,
                         rets = (cons r0 .. (cons rn nil) ..) /\
                         post) ..))))
    (at level 200,
     name at level 0,
     r0 closed binder, rn closed binder,
     tr name, tr' name, mem name, mem' name, mc name, mc' name,
     pre at level 200,
     post at level 200).
