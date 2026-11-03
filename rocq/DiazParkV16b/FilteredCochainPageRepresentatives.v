(** Literal representative equations for incoming page maps and comparison
    of the successive denominator submodules. *)
From Coq Require Import ZArith Lia.
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import ModuleInfrastructure MackeyModuleCarriers MackeyModuleQuotient
  MackeyModuleMaps HomologicalComplex.
From DiazParkV16b Require Import FilteredCochainCycles FilteredCochainPages
  FilteredCochainPageHomology FilteredCochainPageCycleLifting.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomological DPFilteredCycles DPFilteredPages
  DPFilteredPageHomology DPFilteredPageCycleLifting.
Local Open Scope ring_scope.

Module DPFilteredPageRepresentatives.
Section Representatives.
Variable R : pzRingType.
Variable C : cochain_complex R.
Variable F : cochain_filtration C.

Lemma page_class_eq r p n x y (hx : almost_cycles F r.+1 p n x)
    (hy : almost_cycles F r.+1 p n y) :
    page_class hx = page_class hy <-> page_relations F r p n (x-y).
Proof.
split; intro h.
- apply/subspace_predP; move/eqP: h; rewrite /page_class quotient_pi_eq; exact (fun h => h).
- apply/eqP; rewrite /page_class quotient_pi_eq; apply/subspace_predP; exact h.
Qed.

Lemma page_index_cast_class r p q n (h : p=q) x
    (hx : almost_cycles F r.+1 p n x) (hy : almost_cycles F r.+1 q n x) :
    page_index_cast F r n h (page_class hx) = page_class hy.
Proof. destruct h; simpl; unfold page_class; f_equal; apply submodule_val_injective; reflexivity. Qed.

Lemma incoming_d_cycles r p n x (hx : almost_cycles F r.+1 (Z.sub p (Z.of_nat r.+1)) n x) :
    almost_cycles F r.+1 p n.+1 (cochain_d C n x).
Proof.
split.
- have hdx := proj2 hx.
  change (filtration F (Z.add (Z.sub p (Z.of_nat r.+1)) (Z.of_nat r.+1)) n.+1 (cochain_d C n x)) in hdx.
  by rewrite incoming_index in hdx.
- change (filtration F (Z.add p (Z.of_nat r.+1)) n.+2 (cochain_d C n.+1 (cochain_d C n x))).
  rewrite cochain_d2; exact: subspace_zero.
Qed.

Lemma page_incoming_class r p n x (hx : almost_cycles F r.+1 (Z.sub p (Z.of_nat r.+1)) n x) :
    page_incoming (page_class hx) = page_class (incoming_d_cycles hx).
Proof. rewrite /page_incoming page_d_class; exact: page_index_cast_class. Qed.

Lemma filtered_boundaries_mono r s p n (h : (r<=s)%coq_nat) :
    subspace_le (filtered_boundaries F r p n) (filtered_boundaries F s p n).
Proof.
intros x [hx hb]; split; [exact hx|].
destruct n; [exact hb|].
destruct hb as [v [hv hdv]]; exists v; split; [|exact hdv].
apply: (@filtration_decreasing R C F (Z.sub p (Z.of_nat s)) (Z.sub p (Z.of_nat r)) n _ _ hv); lia.
Qed.

Lemma next_relation_of_old_difference r p n x y
    (hx : almost_cycles F r.+2 p n x) (hy : filtered_boundaries F r.+1 p n y)
    (hxy : page_relations F r p n (x-y)) : page_relations F r.+1 p n x.
Proof.
destruct hxy as [a [b [[ha hda] [hb hab]]]].
exists a,(b+y); split.
- split; [exact ha|].
  have he : a = x-(b+y).
    have hx' : x=a+(b+y) by rewrite addrA hab subrK.
    by rewrite hx' addrK.
  change (filtration F (Z.add (Z.succ p) (Z.of_nat r.+1)) n.+1 (cochain_d C n a)).
  rewrite he linearB linearD (filtered_boundary_d_zero (proj2 hb))
    (filtered_boundary_d_zero (proj2 hy)) add0r subr0.
  have hi : Z.add (Z.succ p) (Z.of_nat r.+1) = Z.add p (Z.of_nat r.+2) by lia.
  rewrite hi; exact (proj2 hx).
- split.
  + apply subspace_add; [apply: filtered_boundaries_mono hb; lia|exact hy].
  + rewrite addrA hab subrK; reflexivity.
Qed.

End Representatives.
End DPFilteredPageRepresentatives.
