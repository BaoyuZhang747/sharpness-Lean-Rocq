(** Every actual finite quotient-equivalence derivation occurs at a finite
    skeletal stage. No injectivity of the global inclusion is presumed. *)
From mathcomp Require Import all_ssreflect all_algebra all_classical reals topology.
From DiazPark Require Import Category.
From DiazParkV16b Require Import SimplexCategory SimplicialSet SimplicialSubcomplex SimplicialSkeleton
  TopologicalCategory TopologicalSimplexAffine GeometricRealizationCarrier GeometricRealizationMaps.
Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import numFieldTopology.Exports.

Module DPRealizationSkeletonRelations.
Import DPSimplexCategory DPSimplicialSet DPSimplicialSubcomplex DPSimplicialSkeleton
  DPGeometricRealization DPGeometricRealizationMaps.
Local Opaque realization_equiv realization_quotient.
Section Relations.
Variable Real : realType.
Variable X : simplicial_set.

Definition raw_dimension (p : pre_realization Real X) : nat := projT1 (projT1 p).

Definition raw_skeleton_lift N (p : pre_realization Real X)
    (hp : (raw_dimension p <= N)%N) : pre_realization Real (skeleton_set X N).
Proof.
  destruct p as [[n x] t]; cbn in hp.
  exact (@pre_point Real (skeleton_set X N) n
    (exist _ x (skeleton_contains_degree x hp)) t).
Defined.

Lemma raw_skeleton_lift_proof N p (h h' : (raw_dimension p <= N)%N) :
  raw_skeleton_lift h = raw_skeleton_lift h'.
Proof. by have -> : h = h' := Prop_irrelevance _ _. Qed.

Lemma raw_skeleton_lift_transition N M (hNM : (N <= M)%N) p
    (hp : (raw_dimension p <= N)%N) (hp' : (raw_dimension p <= M)%N) :
  realization_map Real (skeleton_transition X hNM)
    (realization_class (raw_skeleton_lift hp)) =
  realization_class (raw_skeleton_lift hp').
Proof.
  destruct p as [[n x] t].
  change (realization_map Real (skeleton_transition X hNM)
    (@characteristic Real (skeleton_set X N) n
      (exist _ x (skeleton_contains_degree x hp)) t) =
    @characteristic Real (skeleton_set X M) n
      (exist _ x (skeleton_contains_degree x hp')) t).
  rewrite realization_map_characteristic.
  apply (f_equal (fun s : simplex (skeleton_set X M) n =>
    @characteristic Real (skeleton_set X M) n s t)).
  apply subcomplex_simplex_ext; reflexivity.
Qed.

Definition bounded_relation (p q : pre_realization Real X) :=
  exists N (hp : (raw_dimension p <= N)%N) (hq : (raw_dimension q <= N)%N),
    realization_class (raw_skeleton_lift hp) = realization_class (raw_skeleton_lift hq).

Lemma bounded_relation_refl p : bounded_relation p p.
Proof. exists (raw_dimension p), (leqnn _), (leqnn _); reflexivity. Qed.

Lemma bounded_relation_sym p q : bounded_relation p q -> bounded_relation q p.
Proof. by move=> [N [hp [hq e]]]; exists N, hq, hp; symmetry. Qed.

Lemma bounded_relation_trans p q r :
  bounded_relation p q -> bounded_relation q r -> bounded_relation p r.
Proof.
move=> [N [hp [hq e]]] [M [hq' [hr e']]].
pose K := maxn N M.
have hNK : (N <= K)%N := leq_maxl N M.
have hMK : (M <= K)%N := leq_maxr N M.
have hpK := leq_trans hp hNK.
have hqK := leq_trans hq hNK.
have hrK := leq_trans hr hMK.
exists K, hpK, hrK.
transitivity (realization_class (raw_skeleton_lift hqK)).
- rewrite -(raw_skeleton_lift_transition hNK hp hpK)
    -(raw_skeleton_lift_transition hNK hq hqK).
  exact: (f_equal (fun z => realization_map Real (skeleton_transition X hNK) z) e).
- rewrite -(raw_skeleton_lift_transition hMK hq' hqK)
    -(raw_skeleton_lift_transition hMK hr hrK).
  exact: (f_equal (fun z => realization_map Real (skeleton_transition X hMK) z) e').
Qed.

Lemma bounded_relation_ordinal n m (f : SimplexCategory.DPSimplexCategory.ordinal_map n m)
    (x : simplex X m) (t : TopologicalSimplexBasic.DPTopologicalSimplex.simplex Real n) :
  bounded_relation (@pre_point Real X n (simplex_map X f x) t)
    (@pre_point Real X m x (TopologicalSimplexAffine.DPTopologicalSimplexAffine.pushforward f t)).
Proof.
exists (maxn n m), (leq_maxl n m), (leq_maxr n m).
change (@characteristic Real (skeleton_set X (maxn n m)) n
  (exist _ (simplex_map X f x) (skeleton_contains_degree _ (leq_maxl n m))) t =
  @characteristic Real (skeleton_set X (maxn n m)) m
  (exist _ x (skeleton_contains_degree _ (leq_maxr n m)))
  (TopologicalSimplexAffine.DPTopologicalSimplexAffine.pushforward f t)).
rewrite -characteristic_ordinal.
apply (f_equal (fun s : simplex (skeleton_set X (maxn n m)) n =>
  @characteristic Real (skeleton_set X (maxn n m)) n s t)).
apply subcomplex_simplex_ext; reflexivity.
Qed.

Theorem realization_relation_bounded p q :
  realization_equivalent p q -> bounded_relation p q.
Proof.
move=> h; elim: h => [p0|p0 q0 hpq ih|p0 q0 r0 hpq ih hqr ih'|n m f x t].
- exact: bounded_relation_refl.
- exact: bounded_relation_sym ih.
- exact: bounded_relation_trans ih ih'.
- exact: bounded_relation_ordinal.
Qed.

Definition raw_skeleton_forget N (p : pre_realization Real (skeleton_set X N)) :
    pre_realization Real X :=
  match p with @existT _ _ (@existT _ _ n x) t =>
    @pre_point Real X n (proj1_sig x) t end.

Lemma raw_skeleton_forget_class N (p : pre_realization Real (skeleton_set X N)) :
  realization_map Real (skeleton_inclusion X N) (realization_class p) =
  realization_class (raw_skeleton_forget p).
Proof.
destruct p as [[n x] t]; exact: realization_map_characteristic.
Qed.

Lemma raw_skeleton_forget_lift N M (hNM : (N <= M)%N)
  (p : pre_realization Real (skeleton_set X N))
  (hp : (raw_dimension (raw_skeleton_forget p) <= M)%N) :
  realization_map Real (skeleton_transition X hNM) (realization_class p) =
  realization_class (raw_skeleton_lift hp).
Proof.
destruct p as [[n [x hx]] t].
change (realization_map Real (skeleton_transition X hNM)
  (@characteristic Real (skeleton_set X N) n (exist _ x hx) t) =
  @characteristic Real (skeleton_set X M) n
    (exist _ x (skeleton_contains_degree x hp)) t).
rewrite realization_map_characteristic.
apply (f_equal (fun s : simplex (skeleton_set X M) n =>
  @characteristic Real (skeleton_set X M) n s t)).
apply subcomplex_simplex_ext; reflexivity.
Qed.

Theorem realized_skeleton_injective_of_transitions
  (hi : forall n m (h : (n <= m)%N),
    injective (realization_map Real (skeleton_transition X h))) N :
  injective (realization_map Real (skeleton_inclusion X N)).
Proof.
move=> z w e.
have [p hp0] := realization_class_surjective z.
have [q hq0] := realization_class_surjective w.
rewrite -hp0 -hq0 in e |- *.
rewrite !raw_skeleton_forget_class in e.
have hrel := (proj1 (realization_class_eq _ _) e).
have [K [hp [hq eqK]]] := realization_relation_bounded hrel.
pose M := maxn N K.
have hNM : (N <= M)%N := leq_maxl N K.
have hKM : (K <= M)%N := leq_maxr N K.
have hpM := leq_trans hp hKM.
have hqM := leq_trans hq hKM.
apply (hi N M hNM).
rewrite (raw_skeleton_forget_lift hNM hpM) (raw_skeleton_forget_lift hNM hqM).
rewrite -(raw_skeleton_lift_transition hKM hp hpM)
  -(raw_skeleton_lift_transition hKM hq hqM).
exact: (f_equal (fun a => realization_map Real (skeleton_transition X hKM) a) eqK).
Qed.
End Relations.
End DPRealizationSkeletonRelations.
