From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category ModuleInfrastructure MackeyStructures MackeyGenerated.

(** Algebraic least-support argument. The rank assumptions below are merely
    properties of the arrow category, instantiated by actual finite fusion
    orbit geometry in MackeyFusionMinimal.v. No classification is assumed. *)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section PointedGenerators.
Variable R : comPzRingType.
Variable C : category.
Variable B : mackey_shape C.
Variable M : @mackey_module R C B.
Variable Q : C.
Variable W : module_subspace (mackey_value M Q).

Definition pointed_seed P (x : mackey_value M P) :=
  exists h : Q = P, exists y : mackey_value M Q,
    W y /\ eq_rect Q (mackey_value M) y P h = x.

Lemma pointed_seed_here x : W x -> @pointed_seed Q x.
Proof. move=> hx; exists (erefl Q), x; by split. Qed.

Definition generated_at_value := @generated_value R C B M (@pointed_seed).
Definition generated_at := @generated_mackey R C B M (@pointed_seed).

Lemma generated_at_contains x : W x -> generated_at_value Q x.
Proof. move=> hx; apply: generated_contains; exact: pointed_seed_here hx. Qed.

Lemma generated_at_normal_least P (N : module_subspace (mackey_value M P))
    (hN : forall A (a : hom C A Q) (b : hom C A P) y,
      W y -> N (mackey_push M b (mackey_pull M a y))) x :
    generated_at_value P x -> N x.
Proof.
apply: (@span_least R (mackey_value M P) (@normal_generator R C B M (@pointed_seed) P) N).
move=> v [T [A [a [b [y [[h [z [hz heq]]] <-]]]]]].
subst T; simpl in heq; subst y; exact: hN hz.
Qed.

Lemma simple_generated_at_full (hM : mackey_simple M)
    (hW : exists x, W x /\ x <> 0) : forall P x, generated_at_value P x.
Proof.
apply: simple_generated_full hM _.
have [x [hx hn]] := hW; exists Q, x; split=> //; exact: pointed_seed_here hx.
Qed.

End PointedGenerators.

Section MinimalGeneration.
Variable R : comPzRingType.
Variable C : category.
Variable B : mackey_shape C.
Variable M : @mackey_module R C B.
Variable rank : C -> nat.
Hypothesis arrow_rank : forall P Q, hom C P Q -> (rank P <= rank Q)%N.
Hypothesis equal_rank_iso : forall P Q (f : hom C P Q), rank P = rank Q ->
  exists e : isomorphism P Q, iso_hom e = f.
Variable Q : C.
Hypothesis leastQ : mackey_least_nonzero M rank Q.

Definition transfer_generator P (y : mackey_value M P) :=
  exists f : hom C Q P, exists x : mackey_value M Q, mackey_push M f x = y.

Lemma least_support_normal_form P (N : module_subspace (mackey_value M P))
    (hN : forall f : hom C Q P, forall x, N (mackey_push M f x))
    A (a : hom C A Q) (b : hom C A P) x :
    N (mackey_push M b (mackey_pull M a x)).
Proof.
have hle := arrow_rank a.
case: (ltngtP (rank A) (rank Q)) => hlt.
- have hz := leastQ.2 A hlt (mackey_pull M a x).
  rewrite hz linear0; exact: subspace_zero.
- by move: hle; rewrite leqNgt hlt.
- have [e he] := equal_rank_iso a hlt.
  rewrite -he mackey_pull_iso -mackey_push_comp.
  exact: hN.
Qed.

Lemma simple_minimal_transfer_generation (hM : mackey_simple M) P x :
    module_span (@transfer_generator P) x.
Proof.
apply: (@generated_at_normal_least R C B M Q (subspace_full (mackey_value M Q))
  P (span_subspace (@transfer_generator P))) _ _.
- move=> A a b y _; apply: least_support_normal_form.
  move=> f v; apply: span_generator; by exists f, v.
- apply: (@simple_generated_at_full R C B M Q
    (subspace_full (mackey_value M Q)) hM _ P x).
  have [y hy] := leastQ.1; exists y; by split.
Qed.

Lemma simple_minimal_support_arrow (hM : mackey_simple M) P :
    (exists x : mackey_value M P, x <> 0) -> exists f : hom C Q P, True.
Proof.
move=> [x hx].
have hs := simple_minimal_transfer_generation hM x.
have hnot : ~ (forall f : hom C Q P, False).
  move=> hn; apply: hx.
  apply: (@span_least R (mackey_value M P) (@transfer_generator P)
    (subspace_zero_space (mackey_value M P))) _ hs.
  by move=> y [f [v hv]]; case: (hn f).
have [f|hn] := pselect (exists f : hom C Q P, True); first exact f.
exfalso; apply: hnot => f; apply: hn; by exists f.
Qed.

Definition detection_value P : module_subspace (mackey_value M P).
Proof.
refine (@ModuleSubspace R (mackey_value M P)
  (fun x => forall f : hom C Q P, mackey_pull M f x = 0) _ _ _).
- move=> f; exact: linear0.
- by move=> x y hx hy f; rewrite linearD hx hy addr0.
- by move=> a x hx f; rewrite linearZ /= hx scaler0.
Defined.

Lemma detection_pull P T (f : hom C P T) x :
    detection_value T x -> detection_value P (mackey_pull M f x).
Proof. move=> hx g; rewrite -mackey_pull_comp; exact: hx. Qed.

Lemma detection_push P T (f : hom C P T) x :
    detection_value P x -> detection_value T (mackey_push M f x).
Proof.
move=> hx g; rewrite mackey_formula.
apply: big1=> s _.
pose A := span_apex (mackey_term B f g s).
pose a := span_left (mackey_term B f g s).
pose b := span_right (mackey_term B f g s).
change (mackey_push M b (mackey_pull M a x) = 0).
have hle := arrow_rank b.
case: (ltngtP (rank A) (rank Q)) => hlt.
- by rewrite (leastQ.2 A hlt (mackey_pull M a x)) linear0.
- by move: hle; rewrite leqNgt hlt.
- have [e he] := equal_rank_iso b hlt.
  have h := hx (compose (iso_inv e) a).
  rewrite mackey_pull_comp in h.
  have hi := mackey_pull_iso (m := M) (iso_symm e) (mackey_pull M a x).
  change (mackey_pull M (iso_inv e) (mackey_pull M a x) =
    mackey_push M (iso_hom e) (mackey_pull M a x)) in hi.
  by rewrite hi he in h.
Qed.

Definition detection_subfunctor : mackey_subfunctor M :=
  @MackeySubfunctor R C B M detection_value (@detection_pull) (@detection_push).

Lemma simple_minimal_restriction_detection (hM : mackey_simple M) P x :
    (forall f : hom C Q P, mackey_pull M f x = 0) -> x = 0.
Proof.
move=> hx; have [_ hs] := hM.
case: (hs detection_subfunctor) => hz.
- exact: hz hx.
- have [v hv] := leastQ.1.
  have h := hz Q v (identity Q).
  rewrite mackey_pull_id in h; exact: False_ind _ (hv h).
Qed.

Lemma simple_minimal_restriction_injective (hM : mackey_simple M) P
    (x y : mackey_value M P) :
    (forall f : hom C Q P, mackey_pull M f x = mackey_pull M f y) -> x = y.
Proof.
move=> h; apply/eqP; rewrite -subr_eq0; apply/eqP.
apply: (@simple_minimal_restriction_detection hM P (x - y)) => f.
by rewrite linearB h subrr.
Qed.

Definition automorphism_simple_at :=
  (exists x : mackey_value M Q, x <> 0) /\
  forall W : module_subspace (mackey_value M Q),
    (forall (e : isomorphism Q Q) x, W x -> W (mackey_push M (iso_hom e) x)) ->
    (forall x, W x -> x = 0) \/ (forall x, W x).

Lemma simple_minimal_automorphism_simple (hM : mackey_simple M) :
    automorphism_simple_at.
Proof.
split; first exact: leastQ.1.
move=> W hW.
have hnormal : forall A (a : hom C A Q) (b : hom C A Q) x,
    W x -> W (mackey_push M b (mackey_pull M a x)).
  move=> A a b x hx; have hle := arrow_rank a.
  case: (ltngtP (rank A) (rank Q)) => hlt.
  - rewrite (leastQ.2 A hlt (mackey_pull M a x)) linear0; exact: subspace_zero.
  - by move: hle; rewrite leqNgt hlt.
  - have [e he] := equal_rank_iso a hlt.
    rewrite -he mackey_pull_iso -mackey_push_comp.
    have [d hd] := equal_rank_iso (compose (iso_inv e) b) (erefl (rank Q)).
    rewrite -hd; exact: hW hx.
have [_ hs] := hM.
case: (hs (@generated_at R C B M Q W)) => h.
- left=> x hx; exact: h (generated_at_contains hx).
- right=> x; apply: (@generated_at_normal_least R C B M Q W Q W hnormal x).
  exact: h.
Qed.

End MinimalGeneration.






