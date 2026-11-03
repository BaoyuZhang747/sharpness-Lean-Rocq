(** Pointwise maps and exactness of arbitrary dependent module direct sums.
    Lifts retain the finite support of the requested target family. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import CategoryModules CategoryModuleLinear CategoryModuleProducts
  CategoryModuleDirectSums ModuleInfrastructure MackeyModuleCarriers.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section SumMap.
Variable R : pzRingType.
Variable I : Type.
Variables U V : I -> lmodType R.
Variable f : forall i, {linear U i -> V i}.

Definition sum_map_family (x : module_sum_type U) (i : I) := f i (sum_coefficient x i).
Lemma sum_map_support (x : module_sum_type U) : sum_finite_support (sum_map_family x).
Proof.
exists (sum_support x); move=> i hi.
rewrite /sum_map_family (sum_coefficient_outside hi) linear0; reflexivity.
Qed.

Definition sum_map (x : module_sum_type U) : module_sum_type V :=
  @submodule_in R (module_product_type V) (sum_support_subspace V)
    (sum_map_family x) (sum_map_support x).

Lemma sum_map_coefficient x i : sum_coefficient (sum_map x) i = f i (sum_coefficient x i).
Proof. reflexivity. Qed.

Lemma sum_map_linear : linear sum_map.
Proof.
move=> a x y; apply sum_coefficient_ext => i.
change (f i (a *: sum_coefficient x i + sum_coefficient y i) =
  a *: f i (sum_coefficient x i) + f i (sum_coefficient y i)).
exact: linearP.
Qed.
HB.instance Definition _ := GRing.isLinear.Build R (module_sum_type U) (module_sum_type V) _
  sum_map sum_map_linear.

Lemma sum_map_single i (x : U i) : sum_map (sum_single x) = sum_single (f i x).
Proof.
apply sum_coefficient_ext => j.
case: (pselect (i = j)) => [h|h].
- subst j; by rewrite sum_map_coefficient !sum_single_same.
- by rewrite sum_map_coefficient !sum_single_away // linear0.
Qed.

Lemma sum_map_injective : (forall i, injective (f i)) -> injective sum_map.
Proof.
move=> hf x y h; apply sum_coefficient_ext => i; apply hf.
exact (congr1 (fun z => sum_coefficient z i) h).
Qed.

Section SupportedLift.
Variable y : module_sum_type V.
Hypothesis hy : forall i, exists x, f i x = sum_coefficient y i.

Definition sum_preimage_family (i : I) : U i :=
  if i \in sum_support y then proj1_sig (constructive_indefinite_description (hy i)) else 0.

Lemma sum_preimage_support : sum_finite_support sum_preimage_family.
Proof.
exists (sum_support y); move=> i hi.
by rewrite /sum_preimage_family (negPf hi).
Qed.

Definition sum_preimage : module_sum_type U :=
  @submodule_in R (module_product_type U) (sum_support_subspace U)
    sum_preimage_family sum_preimage_support.

Lemma sum_preimage_spec : sum_map sum_preimage = y.
Proof.
apply sum_coefficient_ext => i.
change (f i (sum_preimage_family i) = sum_coefficient y i).
rewrite /sum_preimage_family; case hi: (i \in sum_support y).
- exact: (proj2_sig (constructive_indefinite_description (hy i))).
- rewrite linear0; symmetry; apply sum_coefficient_outside; by rewrite hi.
Qed.
End SupportedLift.

Lemma sum_map_surjective :
  (forall i y, exists x, f i x = y) -> forall y, exists x, sum_map x = y.
Proof.
move=> hf y.
exists (sum_preimage (fun i => hf i (sum_coefficient y i))).
exact: sum_preimage_spec.
Qed.

End SumMap.

Section SumExactness.
Variable R : pzRingType.
Variable I : Type.
Variables U V W : I -> lmodType R.
Variable f : forall i, {linear U i -> V i}.
Variable g : forall i, {linear V i -> W i}.

Theorem sum_map_exact :
  (forall i, linear_exact (f i) (g i)) ->
  linear_exact (sum_map f) (sum_map g).
Proof.
move=> h y; split.
- move=> hy.
  have hp : forall i, exists x, f i x = sum_coefficient y i.
    move=> i; apply/(h i).
    have hz := congr1 (fun z => sum_coefficient z i) hy.
    exact hz.
  exists (sum_preimage hp); exact: sum_preimage_spec.
- move=> [x <-]; apply sum_coefficient_ext => i.
  change (g i (f i (sum_coefficient x i)) = 0).
  apply/(h i); exists (sum_coefficient x i); reflexivity.
Qed.

End SumExactness.
