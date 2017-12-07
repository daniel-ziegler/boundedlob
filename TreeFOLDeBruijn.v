Require Import PeanoNat.
Require List.
Require Import Relations.
Import List.ListNotations.
Open Scope list.
Require Import Equality.
Require Import Eqdep_dec.
Require Import FunctionalExtensionality.

Set Implicit Arguments.

Inductive type :=
  | tree : type
  | arrow : type -> type -> type.

Definition type_dec : forall (t1 t2: type), {t1=t2} + {t1<>t2}.
Proof.
  decide equality.
Defined.

Definition mapping := list type.

Implicit Types (Gamma: mapping) (t: type).

Inductive variable : mapping -> type -> Type :=
| var_here : forall Gamma t, variable (t :: Gamma) t
| var_outer : forall Gamma t t', variable Gamma t -> variable (t' :: Gamma) t.

Theorem variable_to_in : forall Gamma t,
    variable Gamma t -> List.In t Gamma.
Proof.
  induction 1; simpl; intros; eauto.
Qed.

Inductive expr (Gamma: mapping) : type -> Type :=
| var : forall t (v: variable Gamma t), expr Gamma t
| nil : expr Gamma tree
| eats : expr Gamma tree -> expr Gamma tree -> expr Gamma tree
| abs : forall t1 t2,
    forall (e: expr (t1 :: Gamma) t2),
      expr Gamma (arrow t1 t2)
| app : forall t1 t2,
    forall (e1: expr Gamma (arrow t1 t2))
      (e2: expr Gamma t1),
      expr Gamma t2
| recur : forall t,
    forall (eleaf: expr Gamma t)
      (enode: expr (t :: t :: Gamma) t)
      (e: expr Gamma tree),
      expr Gamma t.
Arguments nil {Gamma}.
Infix "◁" := eats (at level 15, left associativity).

Definition renaming Gamma Gamma' :=
  forall t (v: variable Gamma t), variable Gamma' t.

Program Definition renaming_shift
        Gamma Gamma' t
        (gamma: renaming Gamma Gamma') :
  renaming (t :: Gamma) (t :: Gamma') :=
  fun t' v =>
    match v with
      | var_here _ _ => var_here _ _
      | var_outer _ v' => var_outer _ (gamma _ v')
    end.

Definition apply_renaming Gamma Gamma' (gamma: renaming Gamma Gamma')
           t (e: expr Gamma t) : expr Gamma' t.
  intros.
  generalize dependent Gamma'.
  generalize dependent Gamma.
  induction 1; intros; subst.
  - exact (var (gamma _ v)).
  - exact nil.
  - now apply eats; [ apply IHe1 | apply IHe2 ].
  - eapply abs.
    eapply IHe; trivial.
    now apply renaming_shift.
  - now eapply app; [ apply IHe1 | apply IHe2 ].
  - eapply recur.
    now apply IHe1.
    apply IHe2; trivial.
    apply renaming_shift.
    now apply renaming_shift.
    now apply IHe3.
Defined.

Definition var_shift Gamma t' : renaming _ _ := fun t (v: variable Gamma t) => var_outer t' v.

Definition expr_shift Gamma t t' (e: expr Gamma t) : expr (t' :: Gamma) t.
  eapply apply_renaming; eauto.
  exact (var_shift _).
Defined.

Definition substitution Gamma Gamma' :=
  forall t (v: variable Gamma t), expr Gamma' t.

Program Definition substitution_shift
        Gamma Gamma' t
        (gamma: substitution Gamma Gamma') :
  substitution (t :: Gamma) (t :: Gamma') := fun t' v =>
  match v with
    | var_here _ _ => var (var_here _ _)
    | var_outer _ v' => expr_shift t (gamma _ v')
  end.

Program Definition substitution_shift_expr
        Gamma Gamma' t
        (e': expr Gamma' t)
        (gamma: substitution Gamma Gamma') :
  substitution (t :: Gamma) Gamma' :=
  fun t' (v: variable (t :: Gamma) t') =>
    match v with
      | var_here _ _ => e'
      | var_outer _ v' => gamma _ v'
    end.

Definition apply_substitution Gamma Gamma' (gamma: substitution Gamma Gamma')
           t (e: expr Gamma t) : expr Gamma' t.
  intros.
  generalize dependent Gamma'.
  generalize dependent Gamma.
  induction 1; intros; subst.
  - exact (gamma _ v).
  - exact nil.
  - now apply eats; [ apply IHe1 | apply IHe2 ].
  - eapply abs.
    eapply IHe; trivial.
    now apply substitution_shift.
  - now eapply app; [ apply IHe1 | apply IHe2 ].
  - eapply recur.
    now apply IHe1.
    apply IHe2; trivial.
    apply substitution_shift.
    now apply substitution_shift.
    now apply IHe3.
Defined.

Definition compose_ren_ren Gamma Gamma' Gamma''
           (r: renaming Gamma Gamma')
           (r': renaming Gamma' Gamma'') : renaming Gamma Gamma'' :=
  fun t v => r' _ (r t v).

Definition compose_ren_sub Gamma Gamma' Gamma''
           (r: renaming Gamma Gamma')
           (s: substitution Gamma' Gamma'') : substitution Gamma Gamma'' :=
  fun t v => s _ (r t v).

Definition compose_sub_ren Gamma Gamma' Gamma''
           (s: substitution Gamma Gamma')
           (r: renaming Gamma' Gamma'') : substitution Gamma Gamma'' :=
  fun t v => apply_renaming r (s t v).

Definition compose_substitutions Gamma Gamma' Gamma''
           (s: substitution Gamma Gamma')
           (s': substitution Gamma' Gamma'') : substitution Gamma Gamma'' :=
  fun t v => apply_substitution s' (s t v).

Ltac subst_ext :=
  intros;
  let ext := (let t := fresh "t" in
             let v := fresh "v" in
             extensionality t; extensionality v;
             dependent destruction v;
             eauto) in
  match goal with
  | [ |- @eq (renaming _ _) _ _ ] =>
    ext
  | [ |- @eq (substitution _ _) _ _ ] =>
    ext
  end.

Ltac do_rewrites E :=
  intros; simpl; rewrite ?E;
  repeat match goal with [H: context[_=_] |- _] => rewrite H end;
  auto.

Definition noop_substitution : forall {Gamma}, substitution Gamma Gamma.
  intros Gamma t v.
  eapply var; eauto.
Defined.

Lemma noop_substitution_shift : forall Gamma t,
    substitution_shift (t := t) (noop_substitution (Gamma := Gamma)) =
    noop_substitution.
Proof.
  subst_ext.
Qed.

Lemma substitute_noop_substitution :
  forall Gamma t (e: expr Gamma t),
    apply_substitution noop_substitution e = e.
Proof.
  induction e; eauto; simpl; rewrite ?noop_substitution_shift; congruence.
Qed.

Lemma shift_ren_ren :
  forall Gamma Gamma' Gamma'' t
    (r: renaming Gamma Gamma')
    (r': renaming Gamma' Gamma''),
    renaming_shift (t:=t) (compose_ren_ren r r') =
    compose_ren_ren (renaming_shift r) (renaming_shift r').
Proof.
  subst_ext.
Qed.

Lemma apply_ren_ren :
  forall Gamma t (e: expr Gamma t) Gamma' Gamma''
    (r: renaming Gamma Gamma')
    (r': renaming Gamma' Gamma'') ,
    apply_renaming (compose_ren_ren r r') e = apply_renaming r' (apply_renaming r e).
Proof.
  induction e; do_rewrites shift_ren_ren.
Qed.

Lemma shift_ren_sub :
  forall Gamma Gamma' Gamma'' t
    (r: renaming Gamma Gamma')
    (s: substitution Gamma' Gamma''),
    substitution_shift (t:=t) (compose_ren_sub r s) =
    compose_ren_sub (renaming_shift r) (substitution_shift s).
Proof.
  subst_ext.
Qed.

Lemma apply_ren_sub :
  forall Gamma t (e: expr Gamma t) Gamma' Gamma''
    (r: renaming Gamma Gamma')
    (s: substitution Gamma' Gamma'') ,
    apply_substitution (compose_ren_sub r s) e = apply_substitution s (apply_renaming r e).
Proof.
  induction e; do_rewrites shift_ren_sub.
Qed.

Lemma shift_sub_ren :
  forall Gamma Gamma' Gamma'' t
    (s: substitution Gamma Gamma')
    (r: renaming Gamma' Gamma''),
    substitution_shift (t:=t) (compose_sub_ren s r) =
    compose_sub_ren (substitution_shift s) (renaming_shift r).
Proof.
  subst_ext.
  unfold compose_sub_ren; simpl.
  unfold expr_shift; simpl.
  rewrite <- ?apply_ren_ren; auto.
Qed.

Lemma apply_sub_ren :
  forall Gamma t (e: expr Gamma t) Gamma' Gamma''
    (s: substitution Gamma Gamma')
    (r: renaming Gamma' Gamma''),
    apply_substitution (compose_sub_ren s r) e = apply_renaming r (apply_substitution s e).
Proof.
  induction e; do_rewrites shift_sub_ren.
Qed.

Lemma shift_sub_sub :
  forall Gamma Gamma' Gamma'' t
    (s: substitution Gamma Gamma')
    (s': substitution Gamma' Gamma''),
    substitution_shift (t:=t) (compose_substitutions s s') =
    compose_substitutions (substitution_shift s) (substitution_shift s').
Proof.
  subst_ext; simpl.
  unfold compose_substitutions; simpl.
  unfold expr_shift; simpl.
  rewrite <- apply_sub_ren, <- apply_ren_sub; auto.
Qed.

Lemma apply_sub_sub :
  forall Gamma t (e: expr Gamma t) Gamma' Gamma''
    (s: substitution Gamma Gamma')
    (s': substitution Gamma' Gamma''),
    apply_substitution (compose_substitutions s s') e =
    apply_substitution s' (apply_substitution s e).
Proof.
  induction e; do_rewrites shift_sub_sub.
Qed.

Definition subst_expr t' (e': expr [] t') t (e: expr [t'] t) : expr [] t :=
  apply_substitution (substitution_shift_expr e' noop_substitution) e.

Definition subst2_expr t1 t2 (e1: expr [] t1) (e2: expr [] t2) t (e: expr [t1;t2] t) : expr [] t :=
  apply_substitution
    (substitution_shift_expr e1 (substitution_shift_expr e2 noop_substitution)) e.

Inductive val Gamma : forall t, expr Gamma t -> Prop :=
| val_nil : val nil
| val_eats : forall (e1 e2 : expr Gamma tree), val e1 -> val e2 -> val (e1 ◁ e2)
| val_abs : forall t1 t2 (e: expr (t1 :: Gamma) t2), val (abs e).
Hint Constructors val.

Inductive step : forall t, expr [] t -> expr [] t -> Prop :=
| step_eats1 : forall (e1 e1' e2 : expr [] tree),
    step e1 e1' ->
    step (e1 ◁ e2) (e1' ◁ e2)
| step_eats2 : forall (e1 e2 e2': expr [] tree),
    val e1 ->
    step e2 e2' ->
    step (e1 ◁ e2) (e1 ◁ e2')
| step_ap1 : forall t1 t2 (e1 e1': expr [] (arrow t1 t2)) e2,
    step e1 e1' ->
    step (app e1 e2) (app e1' e2)
| step_ap2 : forall t1 t2 (e1: expr [] (arrow t1 t2)) e2 e2',
    val e1 ->
    step e2 e2' ->
    step (app e1 e2) (app e1 e2')
| step_apE : forall t1 t2 (e2: expr [] t1) (e: expr [t1] t2),
    val e2 ->
    step (app (abs e) e2) (subst_expr e2 e)
| step_recur1 : forall t (enil : expr [] t) e v v',
    step v v' ->
    step (recur enil e v) (recur enil e v')
| step_recur2 : forall t (enil : expr [] t) e,
    step (recur enil e nil) enil
| step_recur3 : forall t (enil : expr [] t) e v1 v2,
    val v1 -> val v2 ->
    step (recur enil e (v1 ◁ v2)) (subst2_expr (recur enil e v2) (recur enil e v1) e).

Ltac deex :=
  match goal with
  | [ H: exists (varname:_), _ |- _ ] =>
    let name := fresh varname in
    destruct H as [name ?]
  end;
  repeat match goal with
         | [ H: _ /\ _ |- _ ] => destruct H
         end.


Ltac inj_pair2 :=
  match goal with
  | [ H: @existT type ?P ?p _ = existT ?P ?p _ |- _ ] =>
    apply (inj_pair2_eq_dec type type_dec) in H; subst
  end.

Hint Constructors step val.

Theorem progress : forall t (e: expr [] t),
    val e \/
    exists e', step e e'.
Proof.
  intros.
  dependent induction e; subst; eauto.
  - inversion v.
  - edestruct IHe1; repeat deex; eauto.
    edestruct IHe2; repeat deex; eauto.
  - edestruct IHe1; repeat deex; eauto.
    edestruct IHe2; repeat deex; eauto.
    inversion H; repeat inj_pair2; eauto.
  - edestruct IHe3; repeat deex; eauto.
    inversion H; repeat inj_pair2; eauto.
Qed.

Ltac inv_step :=
  match goal with
  | [ H: step _ _ |- _ ] =>
    inversion H; repeat inj_pair2; clear H
  end.

Arguments step {t} e e'.
Hint Constructors clos_refl_trans_1n.
Arguments clos_refl_trans_1n {A} R _ _.
Infix "|->" := (step) (at level 20).
Infix "|->*" := (clos_refl_trans_1n step) (at level 20).

Lemma rt1n_trans' : forall A (R : A -> A -> Prop) x y z,
    clos_refl_trans_1n R x y ->
    clos_refl_trans_1n R y z ->
    clos_refl_trans_1n R x z.
Proof.
  eauto using clos_rt_rt1n, clos_rt1n_rt, rt_trans.
Qed.

Hint Extern 1 (clos_refl_trans_1n _ _ ?x ?y) =>
match goal with
| _ => is_evar x; fail 1
| _ => is_evar y; fail 1
| _ => eapply rt1n_trans'
end.

Lemma step_from_eats : forall e1 e2 e',
    e1 ◁ e2 |->* e' ->
    exists v1 v2, e' = v1 ◁ v2.
Proof.
  intros.
  remember (e1 ◁ e2) as e0.
  generalize dependent e1.
  generalize dependent e2.
  induction H; intros; subst; eauto.
  inv_step; eauto.
Qed.

Definition terminating t (e: expr [] t) : Prop := exists e', e |->* e' /\ val e'.

Fixpoint hereditary_termination t : expr [] t -> Prop :=
  match t with
  | tree => fun e => terminating e
  | arrow t1 t2 => fun e =>
                    exists e0, e |->* abs e0 /\
                          (forall e1: expr [] t1, hereditary_termination e1 ->
                                             hereditary_termination (subst_expr e1 e0))
  end.

Lemma step_respects_eats_1 : forall e1 e1' e2,
    e1 |->* e1' ->
    e1 ◁ e2 |->* e1' ◁ e2.
Proof.
  induction 1; intros; eauto.
Qed.

Lemma step_respects_eats_2 : forall e1 e2 e2',
    val e1 ->
    e2 |->* e2' ->
    e1 ◁ e2 |->* e1 ◁ e2'.
Proof.
  induction 2; intros; eauto.
Qed.

Hint Resolve step_respects_eats_1 step_respects_eats_2.

Definition HT_context Gamma (gamma: substitution Gamma []) :=
  forall t (v: variable Gamma t), hereditary_termination (gamma _ v).

Lemma hereditary_termination_eats_1' : forall (e1 e2: expr [] tree),
    hereditary_termination (e1 ◁ e2) ->
    hereditary_termination e1.
Proof.
  simpl; unfold terminating; intros.
  deex.

  remember (e1 ◁ e2) as e0.
  generalize dependent e2.
  generalize dependent e1.
  induction H; intros; subst.
  - inversion H0; eauto.
  - inv_step; eauto.
    intuition.
    specialize (H e1' e2); intuition.
    deex; eauto.
Qed.

Lemma hereditary_termination_eats_2' : forall (e1 e2: expr [] tree),
    hereditary_termination (e1 ◁ e2) ->
    hereditary_termination e2.
Proof.
  simpl; unfold terminating; intros.
  deex.

  remember (e1 ◁ e2) as e0.
  generalize dependent e2.
  generalize dependent e1.
  induction H; intros; subst.
  - inversion H0; eauto.
  - inv_step; eauto.
    intuition.
    specialize (H e1 e2'); intuition.
    deex; eauto.
Qed.

Lemma hereditary_termination_eats' : forall (e1 e2: expr [] tree),
    hereditary_termination (e1 ◁ e2) ->
    hereditary_termination e1 /\ hereditary_termination e2.
Proof.
  eauto using hereditary_termination_eats_1', hereditary_termination_eats_2'.
Qed.

Ltac simplify :=
  repeat match goal with
         | [ |- forall _, _ ] => intros
         | _ => progress subst
         | [ H: exists _, _ |- _ ] => deex
         | [ H: ?a = ?a |- _ ] => clear H
         | _ => inj_pair2
         | [ H: @hereditary_termination tree _ |- _ ] =>
           simpl in H
         | [ H: @hereditary_termination (arrow _ _) _ |- _ ] =>
           simpl in H
         | _ => progress simpl
         | _ => progress unfold terminating in *
         end.

Definition deterministic A (R: A -> A -> Prop) :=
  forall a a' a'', R a a' -> R a a'' ->
              a' = a''.

Theorem deterministic_clos_refl_R : forall A (R: A -> A -> Prop),
    deterministic R ->
    forall a a' a'',
      clos_refl_trans_1n R a a'' ->
      (forall a''', ~R a'' a''') ->
      R a a' ->
      clos_refl_trans_1n R a' a''.
Proof.
  intros.
  induction H0.
  - exfalso; intuition eauto.
  - erewrite H; eauto.
Qed.

Lemma val_no_step : forall t (e e': expr [] t),
    val e ->
    ~e |-> e'.
Proof.
  induction 1; simplify;
    inversion 1; simplify; intuition eauto.
Qed.

Definition val_dec : forall t (e: expr [] t), {val e} + {~val e}.
Proof.
  induction e; intuition;
    try solve [ right; inversion 1; intuition ].
Defined.

Theorem step_deterministic : forall t, deterministic (step (t:=t)).
Proof.
  unfold deterministic. intros.
  induction H; simplify;
    inversion H0; simplify;
      try pose proof (IHstep _ ltac:(eauto));
      repeat (intuition eauto || simplify);
      solve [ exfalso; match goal with
                       | [ H: val ?e, H': step ?e ?e' |- _ ] =>
                         apply (val_no_step H H')
                       | [ H: step ?e _ |- _ ] =>
                         let Hval := fresh in
                         assert (val e) as Hval by eauto;
                         apply (val_no_step Hval H)
                       end ].
Qed.

Lemma step_clos_refl_R : forall t (e e' e'': expr [] t),
    val e'' ->
    e |->* e'' ->
    e |-> e' ->
    e' |->* e''.
Proof.
  eauto using step_deterministic, val_no_step, deterministic_clos_refl_R.
Qed.

Hint Resolve step_clos_refl_R.

Lemma HT_respects_step : forall t (e e': expr [] t),
    hereditary_termination e ->
    e |-> e' ->
    hereditary_termination e'.
Proof.
  induction t; simplify; eauto.
Qed.

Hint Resolve HT_respects_step.

Lemma HT_prepend_step : forall t (e e': expr [] t),
    hereditary_termination e' ->
    e |-> e' ->
    hereditary_termination e.
Proof.
  simplify.
  generalize dependent e.
  generalize dependent e'.
  induction t; simplify; eauto.
Qed.

Definition rename_substitution Gamma Gamma' (r: renaming Gamma Gamma') : substitution Gamma Gamma' :=
  fun t e => var (r _ e).

Lemma rename_substitution_shift_commute : forall Gamma Gamma' t (r: renaming Gamma Gamma'),
    rename_substitution (renaming_shift (t:=t) r) =
    substitution_shift (rename_substitution r).
Proof.
  intros; extensionality t'; extensionality e.
  dependent induction e; simplify; eauto.
Qed.

Theorem apply_renaming_as_substitution : forall Gamma Gamma' (r: renaming Gamma Gamma'),
    apply_renaming r = apply_substitution (rename_substitution r).
Proof.
  intros.
  extensionality t; extensionality e.
  generalize dependent Gamma'.
  induction e; simplify; f_equal; eauto.
  erewrite ?IHe,
  ?rename_substitution_shift_commute by eauto;
    auto.
  erewrite ?IHe1, ?IHe2, ?IHe3,
  ?rename_substitution_shift_commute by eauto;
    eauto.
Qed.

Arguments renaming_shift {Gamma Gamma'} t gamma [t0] v.
Arguments substitution_shift {Gamma Gamma'} t gamma [t0] v.

Lemma var_shift_expr_noop : forall Gamma t (e: expr Gamma t) (s: substitution Gamma Gamma),
    compose_substitutions (rename_substitution (var_shift t))
                          (substitution_shift_expr e s) =
    s.
Proof.
  intros.
  extensionality t0; extensionality v.
  dependent destruction v; simplify; eauto.
Qed.

Lemma expr_shift_expr_noop : forall Gamma Gamma' (s: substitution Gamma Gamma')
                             t (e: expr Gamma t)
                             t' (e': expr Gamma' t'),
    apply_substitution (substitution_shift_expr e' s)
                       (expr_shift t' e) = apply_substitution s e.
Proof.
  induction e; simplify; f_equal;
    eauto;
    rewrite ?apply_renaming_as_substitution,
    <- ?apply_sub_sub,
    ?rename_substitution_shift_commute,
    <- ?shift_sub_sub,
    ?noop_substitution_shift,
    ?substitute_noop_substitution;
    auto.
Qed.

Lemma compose_substitutions_assoc : forall Gamma Gamma' Gamma'' Gamma'''
                                      (s1: substitution Gamma Gamma')
                                      (s2: substitution Gamma' Gamma'')
                                      (s3: substitution Gamma'' Gamma'''),
    compose_substitutions s1 (compose_substitutions s2 s3) =
    compose_substitutions (compose_substitutions s1 s2) s3.
Proof.
  intros.
  unfold compose_substitutions at 1 3.
  extensionality t; extensionality v.
  rewrite apply_sub_sub.
  reflexivity.
Qed.

Lemma compose_noop_r : forall Gamma Gamma' (s: substitution Gamma Gamma'),
    compose_substitutions s noop_substitution = s.
Proof.
  intros.
  extensionality t; extensionality v.
  unfold compose_substitutions.
  apply substitute_noop_substitution.
Qed.

Lemma compose_shift_expr : forall Gamma Gamma' Gamma'' t e
                             (gamma1: substitution Gamma Gamma')
                             (gamma2: substitution Gamma' Gamma''),
    compose_substitutions (substitution_shift t gamma1) (substitution_shift_expr e gamma2)
    = substitution_shift_expr e (compose_substitutions gamma1 gamma2).
Proof.
  intros.
  extensionality t0; extensionality v.
  unfold compose_substitutions.
  dependent destruction v; simplify; eauto.
  apply expr_shift_expr_noop.
Qed.

Lemma subst_shift :
  forall Gamma (gamma: substitution Gamma []) t1 t2 (e: expr (t1 :: Gamma) t2) e2,
    apply_substitution (substitution_shift_expr e2 gamma) e =
    subst_expr e2 (apply_substitution (substitution_shift t1 gamma) e).
Proof.
  unfold subst_expr.
  intros.
  rewrite <- ?apply_sub_sub.
  rewrite compose_shift_expr.
  rewrite compose_noop_r.
  reflexivity.
Qed.

Lemma subst2_shift :
  forall Gamma (gamma: substitution Gamma []) t1 t2 (e: expr (t1 :: t2 :: Gamma) t2) e1 e2,
    apply_substitution (substitution_shift_expr e1 (substitution_shift_expr e2 gamma)) e =
    subst2_expr e1 e2 (apply_substitution (substitution_shift t1 (substitution_shift t2 gamma)) e).
Proof.
  unfold subst2_expr.
  intros.
  rewrite <- ?apply_sub_sub.
  rewrite ?compose_shift_expr.
  rewrite compose_noop_r.
  reflexivity.
Qed.

Theorem hereditary_termination_terminating :
  forall t (e: expr [] t),
    hereditary_termination e -> terminating e.
Proof.
  intros.
  destruct t; simplify; eauto.
Qed.

Lemma HT_abs :
  forall t1 t2 (e1: expr [] (arrow t1 t2)) e2,
    hereditary_termination e1 ->
    hereditary_termination e2 ->
    hereditary_termination (app e1 e2).
Proof.
  intros.
  edestruct H.
  intuition.
  generalize H0; intros Ht2.
  apply hereditary_termination_terminating in H0.
  destruct H0.
  intuition.
  remember (abs x).
  induction H2; subst; eauto using HT_prepend_step.
  induction H1; eauto using HT_prepend_step.
Qed.

Lemma hereditary_termination_eats : forall e1 e2,
    hereditary_termination e1 ->
    hereditary_termination e2 ->
    hereditary_termination (e1 ◁ e2).
Proof.
  simplify.
  eauto 7 using rt1n_trans'.
Qed.

Hint Resolve HT_abs.

(* TODO: factor better *)
Lemma HT_recur:
  forall Gamma t e1
    (e2 : expr (t :: t :: Gamma) t) (gamma : substitution Gamma []),
    hereditary_termination (apply_substitution gamma e1) ->
    (forall gamma0 : substitution (t :: t :: Gamma) [],
       HT_context gamma0 ->
       hereditary_termination (apply_substitution gamma0 e2)) ->
    forall e : expr [] tree,
      hereditary_termination e ->
      HT_context gamma ->
      hereditary_termination
        (recur (apply_substitution gamma e1)
              (apply_substitution (substitution_shift t (substitution_shift t gamma)) e2) e).
Proof.
  intros Gamma t e1 e2 gamma IHe1 IHe2 e IHe3 H.
  generalize IHe3; intro Ht3.
  eapply hereditary_termination_terminating in Ht3.
  unfold terminating in Ht3; deex.
  induction H0; eauto using HT_prepend_step.
  dependent induction H1; eauto 3 using HT_prepend_step.
  eapply hereditary_termination_eats' in IHe3; intuition.
  specialize (IHval1 _ H0).
  specialize (IHval2 _ H1).
  eapply HT_prepend_step; try eapply step_recur3; eauto.
  rewrite <- subst2_shift.
  eapply IHe2.
  dependent destruction v; simplify; eauto.
  dependent destruction v; simplify; eauto.
Qed.

Hint Resolve HT_recur.

Theorem HT_context_subst : forall Gamma t (e: expr Gamma t) (gamma: substitution Gamma []),
    HT_context gamma -> hereditary_termination (apply_substitution gamma e).
Proof.
  unfold HT_context.
  intros.
  generalize dependent gamma.
  induction e; simplify; eauto.
  - eapply hereditary_termination_eats; eauto.
  - eexists.
    intuition eauto.
    rewrite <- subst_shift.
    eapply IHe.
    intros.
    dependent destruction v; simplify; eauto.
Qed.

Hint Resolve substitute_noop_substitution.

Theorem exprs_ht :
  forall t (e: expr [] t),
    hereditary_termination e.
Proof.
  intros.
  replace e with (apply_substitution noop_substitution e) by auto.
  eapply HT_context_subst.
  unfold HT_context; intros.
  inversion v.
Qed.

Theorem exprs_terminating :
  forall t (e: expr [] t),
    terminating e.
Proof.
  auto using hereditary_termination_terminating, exprs_ht.
Qed.

Inductive Tree := Nil | Eats (t e: Tree).

Notation "⋅" := Nil.
Infix "△" := Eats (at level 16, left associativity).

Fixpoint type_denote (t: type) : Type :=
  match t with
  | tree => Tree
  | arrow t1 t2 => type_denote t1 -> type_denote t2
  end.

Definition denote_context Gamma :=
  forall t (v: variable Gamma t), type_denote t.

Definition empty_denote_context : denote_context [] :=
  fun t v => match v in (variable m t0) return (match m with
                                             | [] => type_denote t
                                             | _ :: _ => unit
                                             end) with
          | var_here _ _ => tt
          | var_outer _ _ => tt
          end.

Program Definition denote_context_insert
        Gamma t
        (x: type_denote t)
        (c: denote_context Gamma) : denote_context (t :: Gamma) :=
  fun t' (v: variable (t :: Gamma) t') =>
    match v with
      | var_here _ _ => x
      | var_outer _ v' => c _ v'
    end.

Fixpoint Tree_rec_nondep {T: Type} (z: T) (f: T -> T -> T) (t: Tree) : T :=
  match t with
  | ⋅ => z
  | t1 △ t2 => f (Tree_rec_nondep z f t1) (Tree_rec_nondep z f t2)
  end.

Fixpoint expr_denote Gamma (c: denote_context Gamma) t (e: expr Gamma t) : type_denote t :=
  match e with
  | var v => c _ v
  | nil => ⋅
  | eats e1 e2 => expr_denote c e1 △ expr_denote c e2
  | abs e => fun x => expr_denote (denote_context_insert x c) e
  | app e1 e2 => (expr_denote c e1) (expr_denote c e2)
  | @recur _ t ez ef et => Tree_rec_nondep
                            (expr_denote c ez)
                            (fun x1 x2 => (expr_denote
                                          (denote_context_insert x1 (denote_context_insert x2 c))
                                          ef))
                            (expr_denote c et)
  end.

Arguments var_here {_} {_}.
Arguments var_outer {_} {_} {_} _.

Definition x0 {Gamma t0} := @var (t0 :: Gamma) t0 var_here.
Definition x1 {Gamma t0 t1} := @var (t0 :: t1 :: Gamma) t1 (var_outer var_here).
Definition x2 {Gamma t0 t1 t2} := @var (t0 :: t1 :: t2 :: Gamma) t2 (var_outer (var_outer var_here)).

Definition id t := abs x0 : expr [] (arrow t t).
Definition K t1 t2 := abs (abs x1) : expr [] (arrow t1 (arrow t2 t1)).
Definition flip := abs (recur nil (x1 ◁ x0) x0) : expr [] (arrow tree tree).

Eval lazy in expr_denote empty_denote_context (id tree).
Eval lazy in expr_denote empty_denote_context (K tree (arrow tree tree)).
Eval lazy in expr_denote empty_denote_context flip.
Eval lazy in expr_denote empty_denote_context (app flip (nil ◁ nil ◁ nil)).

Fixpoint encode_var Gamma t (v: variable Gamma t) : Tree :=
  match v with
  | var_here => ⋅
  | var_outer v' => encode_var v' △ ⋅
  end.

Fixpoint encode_expr Gamma t (e: expr Gamma t) : Tree :=
  match e with
  | var v => ⋅ △ encode_var v
  | nil => ⋅
  | eats e1 e2 => (⋅ △ (encode_expr e1 △ encode_expr e2)) △ ⋅ 
  | abs e' => (⋅ △ ⋅) △ encode_expr e'
  | app e1 e2 => (encode_expr e1 △ encode_expr e2) △ ⋅ △ ⋅
  | recur ez ef et => encode_expr ez △ encode_expr ef △ (⋅ △ ⋅) △ encode_expr et
  end.

Eval lazy in encode_expr (abs (app x0 x1)).
Eval lazy in encode_expr (abs (app x0 x2)).
Definition omega_enc := ⋅ △ ⋅ △ (⋅ △ ⋅ △ (⋅ △ ⋅) △ ⋅ △ ⋅).
Definition Omega_enc := (omega_enc △ omega_enc) △ ⋅ △ ⋅.

Theorem encode_var_injective : forall Gamma t (v1 v2: variable Gamma t),
    encode_var v1 = encode_var v2 -> v1 = v2.
Proof.
  induction v1; intros; dependent destruction v2; try discriminate.
  - auto.
  - simpl in H.
    inversion H.
    f_equal.
    auto.
Qed.
Hint Resolve encode_var_injective.

(*
Theorem encode_expr_injective : forall Gamma t (e1 e2: expr Gamma t),
    encode_expr e1 = encode_expr e2 -> e1 = e2.
Proof.
  induction e1; intros; dependent destruction e2; try discriminate;
    simpl in H; inversion H; f_equal; auto.
  (* Oops, only true for type-erased version... *)
Abort.
*)

Fixpoint encoded_context_lookup (n: Tree) (c: list Tree) : option Tree :=
  match n, c with
  | ⋅, v :: _ => Some v
  | n' △ ⋅, _ :: c' => encoded_context_lookup n' c'
  | _, _ => None
  end.

(* TODO: does our interpreter need type tags at runtime?
   otherwise it can't do most runtime type checking, but maybe it doesn't need to *)
Fixpoint eval_encoded_expr (fuel: nat) (c: list Tree) (e: Tree) {struct fuel} : option Tree :=
  match fuel with
  | O => None
  | S fuel' =>
    match e with
    | (* var v *) ⋅ △ v => encoded_context_lookup v c
    | (* nil *) ⋅ => Some ⋅
    | (* eats e1 e2 *) (⋅ △ (e1 △ e2)) △ ⋅ =>
      match eval_encoded_expr fuel' c e1, eval_encoded_expr fuel' c e2 with
      | Some t1, Some t2 => Some (t1 △ t2)
      | _, _ => None
      end
    | (* abs e' *) (⋅ △ ⋅) △ e' => Some e' (* no type tags -> ambiguous with tree values *)
    | (* app ef ex *) (ef △ ex) △ ⋅ △ ⋅ =>
      match eval_encoded_expr fuel' c ef, eval_encoded_expr fuel' c ex with
      | Some f, Some x => eval_encoded_expr fuel' (x :: c) f
      | _, _ => None
      end
    | (* recur ez f et *) ez △ f △ (⋅ △ ⋅) △ et =>
      match eval_encoded_expr fuel' c et with
      | Some t => Tree_rec_nondep (eval_encoded_expr fuel' c ez)
                                 (fun (t1 t2: option Tree) =>
                                    match t1, t2 with
                                    | Some t1', Some t2' =>
                                      eval_encoded_expr fuel' (t1' :: t2' :: c) f
                                    | _, _ => None
                                    end)
                                 t
      | None => None
      end
    | _ => None
    end
  end.

Eval lazy in expr_denote empty_denote_context (app flip (nil ◁ nil ◁ nil)).
Eval lazy in eval_encoded_expr 4 [] (encode_expr (app flip (nil ◁ nil ◁ nil))).

Lemma val_eats_1 : forall Gamma (e1 e2: expr Gamma tree), val (e1 ◁ e2) -> val e1.
Proof.
  intros.
  inversion H; auto.
Qed.

Lemma val_eats_2 : forall Gamma (e1 e2: expr Gamma tree), val (e1 ◁ e2) -> val e2.
Proof.
  intros.
  inversion H; auto .
Qed.

(*
Definition tree_val (x: expr [] tree) (Hv: val x) : Tree.
  remember tree as t.
  induction x; try abstract solve [ discriminate | exfalso; inversion Hv ].
  - exact Nil.
  - exact (Eats (IHx1 Heqt (val_eats_1 Hv)) (IHx2 Heqt (val_eats_2 Hv))).
Defined.

Theorem tree_val_correct : forall (x: expr [] tree) (Hv: val x),
    tree_val Hv = expr_denote empty_denote_context x.
Proof.
*)

(*
Theorem eval_encoded_expr_S_fuel : forall c e fuel x,
    eval_encoded_expr fuel c e = Some x -> eval_encoded_expr (S fuel) c e = Some x.
Proof.
  induction fuel; simpl; auto; intros; try discriminate.
  destruct e; simpl in *; auto.
  destruct e1; simpl in *; auto.
  destruct e1_1; simpl in *; auto.
    destruct e1_2; simpl in *; auto.
    destruct e2; simpl in *; auto.
    destruct (eval_encoded_expr fuel c e1_2_1) eqn:He121; try discriminate.
    destruct (eval_encoded_expr fuel c e1_2_2) eqn:He122; try discriminate.
    clear IHfuel.
    inversion H; clear H; subst.
Admitted.

Theorem eval_encoded_expr_more_fuel : forall c e fuel fuel' x,
    fuel' >= fuel ->
    eval_encoded_expr fuel c e = Some x -> eval_encoded_expr fuel' c e = Some x.
Proof.
  induction 1; auto using eval_encoded_expr_S_fuel.
Qed.

Hint Resolve Nat.le_max_l Nat.le_max_r.

Definition encoding_context Gamma := substitution Gamma [].

Definition pop_context Gamma t0 (c: encoding_context (t0 :: Gamma)) : encoding_context Gamma :=
  fun t (v: variable Gamma t) => c _ (var_outer v).

Fixpoint encode_context Gamma : forall (c: encoding_context Gamma), list Tree :=
  match Gamma with
  | [] => fun c => []
  | t :: Gamma' => fun c => encode_expr (c _ var_here) :: encode_context (pop_context c)
  end.

Definition encoding_context_denote Gamma (c: encoding_context Gamma) : denote_context Gamma :=
  fun t (v: variable Gamma t) => expr_denote empty_denote_context (c _ v).

Theorem eval_encoded_complete' : forall Gamma t (c: encoding_context Gamma) (e e': expr Gamma t) fuel,
    apply_substitution c e |->* apply_substitution c e' ->
    eval_encoded_expr fuel (encode_context c) (encode_expr e) = Some (expr_denote (encoding_context_denote c) e').
Proof.

Theorem eval_encoded_complete : forall (e e': expr [] tree),
    e |->* e' ->
    exists fuel, eval_encoded_expr fuel [] (encode_expr e) = Some (expr_denote empty_denote_context e').
Proof.
  induction 1; simpl.
  - dependent induction x; simpl; try solve [ inversion v ].
    + exists 1. auto.
    + specialize (IHx1 x3 JMeq_refl eq_refl JMeq_refl); deex.
      specialize (IHx2 x4 JMeq_refl eq_refl JMeq_refl); deex.
      exists (1 + max fuel fuel0); simpl.
      apply eval_encoded_expr_more_fuel with (fuel' := max fuel fuel0) in H; [ | auto ].
      apply eval_encoded_expr_more_fuel with (fuel' := max fuel fuel0) in H0; [ | auto ].
      rewrite H, H0.
      reflexivity.
    + specialize (IHx1 x3 JMeq_refl eq_refl JMeq_refl); deex.

*)