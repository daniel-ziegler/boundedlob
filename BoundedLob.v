Require Import Setoid.
Require Import Omega.
Set Implicit Arguments.
Set Universe Polymorphism.

Parameter IsProvableOutside : Prop -> Prop.
Parameter IsBoundedlyProvableOutside : nat -> Prop -> Prop.
Parameter IsBoundedlyProvable : nat -> Prop -> Prop.

(* The metalogical statement that p is provable in the logic *)
Notation "|- p" := (IsProvableOutside p) (at level 105, no associativity).

(* The metalogical statement that p is provable in n steps in the logic *)
Notation "|-( n ) p" := (IsBoundedlyProvableOutside n p) (at level 105, no associativity).

(* Encoded within the logic, the statement that p is provable in n steps in the logic *)
Notation "[[ p ]]_ n" := (IsBoundedlyProvable n p) (at level 50).

Axiom ProofsAreBounded : forall P : Prop, |- P -> exists N, |-(N) P.
Axiom BoundedProofsAreProofs : forall (P : Prop) N, (|-(N) P) -> |- P.
Axiom OutsideProofBoundsAreLoose : forall (P : Prop) N N', N' > N -> (|-(N) P) -> (|-(N') P).
Axiom ProofBoundsAreLoose : forall (P : Prop) N N', N' >= N -> [[ P ]]_N -> [[ P ]]_N'.

Parameter Log : nat -> nat.
Axiom LogPos : forall n, 1 <= Log n. (* The sort of "log" useful in big-O notation... *)

(* Property 1 - ModusPonensT *)
Axiom ImplicationDistribution : exists c : nat, forall (P Q : Prop), forall a b, |- [[ P -> Q ]]_a -> [[ P ]]_b -> [[ Q ]]_(a+b+c).

(* Property 2 *)
Axiom QuantifierDistribution :
  exists c : nat, forall (phi : nat -> Prop) N, |- [[ forall k, phi k ]]_ N -> forall k, [[ phi k ]]_(c * Log k).
(* TODO: this is a little sketchy. There should be an additive constant dependent on N.
   See Section 4.2 in the paper. *)

(* Property 2, for quantification restricted to numbers bounded below. TODO: verify that this is
   reasonable. *)
Axiom RestrictedQuantifierDistribution :
  exists c : nat, forall (phi : nat -> Prop) N k0, |- [[ forall k, k > k0 -> phi k ]]_ N -> forall k, k > k0 -> [[ phi k ]]_(c * Log k).

(* Epsilon - proof expansion bound *)
Parameter Epsilon : nat -> nat.

(* Property 3 *)
Axiom BoundedNecessitation :
  forall p k, ( |-(k) p ) -> ( |-(Epsilon k) [[ p ]]_k ).

(* Property 4 *)
Axiom BoundedInnerNecessitation :
  forall p k, |- [[ p ]]_ k -> [[ [[ p ]]_k ]]_(Epsilon k).

(* Proposition 1 *)
Parameter ParametricDiagonalLemmaPsi : 
  forall G : (nat -> Prop) -> nat -> Prop, nat -> Prop.
Axiom ParametricDiagonalLemma :
  forall G : (nat -> Prop) -> nat -> Prop,
      forall k, |- (ParametricDiagonalLemmaPsi G) k <-> G (ParametricDiagonalLemmaPsi G) k.

Definition dominates (g : nat -> nat) (f : nat -> nat) :=
  forall M, exists N, forall n, n > N -> M * f n < g n.
Notation "f ≻ g" := (dominates f g) (at level 65, no associativity).

Axiom Epsilon_dom : forall f g, f ≻ (fun n => Epsilon (g n)) -> f ≻ g.
(* i.e. [Epsilon] is [Omega(n)] *)

Lemma dom_sum : forall f g h, f ≻ g -> f ≻ h -> f ≻ (fun n => g n + h n).
Proof.
  unfold dominates; intros.
  destruct (H (2 * M)) as [ Ng Hg ].
  destruct (H0 (2 * M)) as [ Nh Hh ].
  exists (max Ng Nh); intros.
  assert (n > Ng) by (pose proof (Nat.le_max_l Ng Nh); omega).
  assert (n > Nh) by (pose proof (Nat.le_max_r Ng Nh); omega).
  specialize (Hg n); specialize (Hh n); intuition idtac.
  clear H H0 H1.
  rewrite <-Nat.double_twice in *.
  unfold Nat.double in *.
  rewrite Nat.mul_add_distr_l in *.
  rewrite Nat.mul_add_distr_r in *.
  omega.
Qed.

Lemma dom_const : forall c f g, f ≻ g -> f ≻ (fun n => c * g n).
Proof.
  unfold dominates; intros.
  destruct (H (M * c)) as [ N Hd ].
  exists N.
  intros.
  rewrite Nat.mul_assoc.
  auto.
Qed.

Section BoundedLob.

  Variable p : nat -> Prop.

  Variable f : nat -> nat.
  Hypothesis f_bound_below : f ≻ (fun k => Epsilon (Log k)).

  Hypothesis Hyp : forall k, |- [[ p k ]]_(f k) -> p k.
  

  Parameter g : nat -> nat.
  Axiom g_bound_below : g ≻ Log.
  Axiom g_bound_above : f ≻ (fun k => Epsilon (g k)).

  (* [G phi k] represents what is written as G(⌜φ⌝,k) in the paper. (The quasi-quoting is elided.) *)
  Definition G (phi : nat -> Prop) (k : nat) : Prop := [[ phi k ]]_(g k) -> p k.

  (* Differences from the paper:
     - to avoid fiddling around inside boxes inside quantifiers, we split up Step1a and Step1b
       (forward and reverse directions of the iff which defines G).
     - we don't use Big-O notation, instead doing explicit existential quantification
       over constants. the assumptions are currently slightly sketchy. *)

  Definition psi := ParametricDiagonalLemmaPsi G.

  (* The forward direction of Equation 5.3 *)
  Lemma Step1a : exists n, |-(n) forall k, psi k -> G psi k.
  Proof.
    apply ProofsAreBounded.
    pose proof (ParametricDiagonalLemma G).
    firstorder.
  Qed.

  Lemma Step2a : exists n, [[ forall k, psi k -> G psi k ]]_ n.
  Proof.
    destruct Step1a as [ n H ]; exists n.
    eapply BoundedProofsAreProofs.
    apply BoundedNecessitation.
    exact H.
  Qed.

  Lemma Step4 : exists c0, forall k, [[ psi k -> G psi k ]]_ (c0 * Log k).
  Proof.
    destruct QuantifierDistribution as [ c QD ].
    destruct Step2a as [ n H ]; eexists.
    exact (QD _ n H).
  Qed.

  Lemma Step5 : exists c1, forall k a, [[ psi k ]]_a -> [[ G psi k ]]_(a + c1 * Log k).
  Proof.
    destruct ImplicationDistribution as [c ID].
    destruct Step4 as [ c0 H ]; eexists; intros.
    eapply ProofBoundsAreLoose.
    shelve.
    eapply ID.
    apply H.
    apply H0.
    Unshelve.
    exact (c0 + c).
    {
      replace (c0 * Log k + a + c) with (a + (c0 * Log k + c)) by omega.
      unfold ge.
      apply plus_le_compat_l.
      rewrite ?Nat.mul_add_distr_r.
      apply plus_le_compat_l.
      replace c with (c * 1) at 1 by (apply Nat.mul_1_r).
      apply Nat.mul_le_mono_l.
      apply LogPos.
    }
  Qed.

  Lemma Step6 : exists c2, forall k a b, [[ psi k ]]_a -> [[ [[ psi k ]]_(g k) ]]_b -> [[ p k ]]_(a + b + c2 * Log k).
  Proof.
    destruct ImplicationDistribution as [c ID].
    destruct Step5 as [ c1 H ]; eexists; intros.
    eapply ProofBoundsAreLoose. shelve.
    eapply ID.
    apply H.
    apply H0.
    apply H1.
    Unshelve.
    exact (c1 + c).
    {
      rewrite <-?Nat.add_assoc.
      unfold ge.
      apply plus_le_compat_l.
      rewrite ?Nat.mul_add_distr_r.
      replace (c1 * Log k + (b + c)) with (b + (c1 * Log k + c)) by omega.
      repeat apply plus_le_compat_l.
      replace c with (c * 1) at 1 by (apply Nat.mul_1_r).
      apply Nat.mul_le_mono_l.
      apply LogPos.
    }
  Qed.

  Parameter h : nat -> nat.
  Axiom h_bound_above : f ≻ h.
  Axiom h_bound_below : h ≻ (fun k => Epsilon (g k)).

  Lemma Step7 : exists c2, forall k, [[ psi k ]]_(g k) -> [[ [[ psi k ]]_(g k) ]]_(h k) -> [[ p k ]]_(g k +  h k + c2 * Log k).
  Proof.
    destruct Step6 as [c2 H]; exists c2.
    auto.
  Qed.

  Lemma Step8 : exists k1, forall k, k > k1 -> [[ psi k ]]_(g k) -> [[ [[ psi k ]]_(g k) ]]_(h k) -> [[ p k ]]_(f k).
  Proof.
    destruct Step7 as [c2 S7].
    assert (f ≻ (fun k => g k + h k + c2 * Log k)).
    {
      repeat apply dom_sum.
      apply Epsilon_dom.
      apply g_bound_above.
      apply h_bound_above.
      apply dom_const.
      apply Epsilon_dom.
      apply f_bound_below.
    }
    assert (exists k1, forall k, k > k1 -> f k >= g k + h k + c2 * Log k).
    {
      destruct (H 1); exists x.
      simpl in H0.
      intros.
      specialize (H0 k).
      omega.
    }
    destruct H0 as [k1 Hk]; exists k1.
    intros; specialize (S7 k); specialize (Hk k); intuition idtac.
    eapply ProofBoundsAreLoose; eassumption.
  Qed.

  (* Equation 5.4 *)
  Lemma Step9 : exists k1, forall k, k > k1 -> [[ psi k ]]_(g k) -> [[ [[ psi k ]]_(g k) ]]_(h k) -> p k.
  Proof.
    destruct Step8 as [k1 S8]; exists k1.
    intros.
    apply Hyp.
    apply S8; assumption.
  Qed.

  (* Without any previous steps, by bounded necessitation on [psi k] *)
  Lemma Step10 : forall k a, [[ psi k ]]_a -> [[ [[ psi k ]]_a ]]_(Epsilon a).
  Proof.
    intros k a.
    apply BoundedInnerNecessitation.
  Qed.

  (* Specialize Step10 to a := g k *)
  Lemma Step11 : forall k, [[ psi k ]]_(g k) -> [[ [[ psi k ]]_(g k) ]]_(Epsilon (g k)).
  Proof.
    intros.
    apply Step10; assumption.
  Qed.

  (* Equation 5.5 *)
  (* Since [Epsilon g(k) < h k] after some bound [k > k2] *)
  Lemma Step12 : exists k2, forall k, k > k2 -> [[ psi k ]]_(g k) -> [[ [[ psi k ]]_(g k) ]]_(h k).
  Proof.
    assert (exists k2, forall k, k > k2 -> h k > Epsilon (g k)).
    {
      destruct (h_bound_below 1). exists x.
      intros.
      specialize (H k).
      omega.
    }
    intros.
    destruct H as [k2 Hd]; exists k2.
    intros.
    eapply ProofBoundsAreLoose.
    apply Nat.lt_le_incl.
    apply Hd; assumption.
    apply Step11; assumption.
  Qed.

  (* Equation 5.6 *)
  (* Combining Equations 5.4 and 5.5 *)
  Lemma Step13 : exists k2, forall k, k > k2 -> [[ psi k ]]_(g k) -> p k.
  Proof.
    destruct Step9 as [k1 S9].
    destruct Step12 as [k2 S12].
    exists (max k1 k2).
    intros.
    assert (k > k1) by (pose proof (Nat.le_max_l k1 k2); omega).
    assert (k > k2) by (pose proof (Nat.le_max_r k1 k2); omega).
    auto.
  Qed.

  (* The reverse direction of Equation 5.3 *)
  Lemma Step1b : exists n, |-(n) forall k, G psi k -> psi k.
  Proof.
    apply ProofsAreBounded.
    pose proof (ParametricDiagonalLemma G).
    firstorder.
  Qed.

  (* By Step1b and the definition of G: *)
  Lemma Step14 : exists k2 N, |-(N) forall k, k > k2 -> psi k.
  Proof.
    destruct Step13 as [k2 S13].
    destruct Step1b as [n S1].
    exists k2.
    apply BoundedProofsAreProofs in S1.
    apply ProofsAreBounded.
    intros; specialize (S13 k); specialize (S1 k); intuition idtac.
  Qed.

  Lemma Step15 : exists k2 N, [[ forall k, k > k2 -> psi k ]]_ N.
  Proof.
    destruct Step14 as [k2 [N S14]].
    exists k2; exists N.
    eapply BoundedProofsAreProofs.
    apply BoundedNecessitation.
    assumption.
  Qed.

  Lemma TakeOutHyp : forall (P Q : Prop) n1, [[ P -> Q ]]_n1 -> (P -> exists n2, [[ Q ]]_(n1 + n2)).
  Proof.
    destruct ImplicationDistribution as [c0 ID].
    intros.
    destruct (ProofsAreBounded H0) as [c1 PB].
    eexists.
    eapply ProofBoundsAreLoose.
    shelve.
    eapply ID.
    eassumption.
    eapply BoundedProofsAreProofs.
    eapply BoundedNecessitation.
    eassumption.
    Unshelve.
    exact (c1 + c0).
    omega.
  Qed.

  Lemma Step16 : exists k2 c, forall k, k > k2 -> [[ psi k ]]_(c * Log k).
  Proof.
    destruct Step15 as [k2 [N S15]].
    destruct RestrictedQuantifierDistribution as [c RQD].
    destruct ImplicationDistribution as [c0 ID].
    exists k2; eexists.

    intros.
    apply RQD with (k := k) in S15; eassumption.
  Qed.

  (* Equation 5.7 *)
  Lemma Step17 : exists k_hat, forall k, k > k_hat -> [[ psi k ]]_(g k).
  Proof.
    destruct Step16 as [k2 [c S16]].
    destruct (g_bound_below c) as [k3 Hgb].
    exists (max k2 k3); intros.
    assert (k > k2) by (pose proof (Nat.le_max_l k2 k3); omega).
    assert (k > k3) by (pose proof (Nat.le_max_r k2 k3); omega).
    eapply ProofBoundsAreLoose; [ | apply S16; assumption ].
    apply Nat.lt_le_incl.
    apply Hgb.
    assumption.
  Qed.

  Lemma TheoremStatement : exists k_hat, forall k, k > k_hat -> p k.
  Proof.
    destruct Step13 as [k2 S13].
    destruct Step17 as [k_hat S17].
    (* a bit silly to max in k2 again since we know [k_hat >= k2], but whatever *)
    exists (max k2 k_hat).
    intros.
    assert (k > k2) by (pose proof (Nat.le_max_l k2 k_hat); omega).
    assert (k > k_hat) by (pose proof (Nat.le_max_r k2 k_hat); omega).
    auto.
  Qed.

  (* Done! *)

End BoundedLob.

Check TheoremStatement. (* Reads very literally like Theorem 3 in the paper! *)