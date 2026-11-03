(** A literal join contraction: id -> join <- constant(base).  Its maps
    are actual simultaneous fusion extensions, not a contractibility premise. *)
From mathcomp Require Import all_boot all_fingroup generic_quotient boolp.
From DiazPark Require Import Category FusionMaps FusionSystems FusionOrbit FusionCentricBasics.
From DiazParkV16b Require Import NormalizerPointedSubgroupExtensions NormalizerPointedSubgroups.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPFusion DPFusionOrbit DPNormalizerSubgroupExtensions DPNormalizerPointedSubgroups.
Local Open Scope group_scope.
Local Open Scope quotient_scope.

Module DPNormalizerPointedSubgroupsContraction.
Section Contraction.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable P : centric_object F.
Local Notation C := (pointed_category P).

Definition join_object (A : C) : C.
Proof.
refine (@Build_object S F P (acting A) (point A) (val (acting A) <*> subgroup A)%G _ _).
- exact (DPFusionCentricBasics.centric_overgroup (joing_subr _ _) (subgroup_centric A)).
- exact (subset_trans (joing_subl _ _) (normG _)).
Defined.

Lemma join_related A B : related A B -> related (join_object A) (join_object B).
Proof.
move=> [f [hf [a]]]; exists f; split; first exact hf.
constructor; exact (join_extension a).
Qed.

Definition join_functor : functor C C.
Proof.
refine (@Build_functor C C join_object (fun A B f => join_related f) _ _);
  intros; apply hom_unique.
Defined.

Definition join_unit_component (A : C) : hom C A (join_object A).
Proof.
exists (DPFusionSystem.arrow_identity F (val (acting A))); split.
- exact (compose_id_right (iso_hom (point A))).
- constructor.
  pose V := (val (acting A) <*> subgroup A)%G.
  refine (@Build_extension S F (subgroup A) V (val (acting A)) (val (acting A))
    (identity (val (acting A))) V (joing_subl _ _) (joing_subr _ _)
    (inclusion (subsetT V)) (DPFusionSystem.inclusion_allowed F _) _ _).
  + move=> x hx; by rewrite inclusion_in ?(subsetP (joing_subl _ _) _ hx) // identity_in.
  + move=> x hx; rewrite inclusion_in ?(subsetP (joing_subr _ _) _ hx) //.
Defined.

Definition join_unit : nat_trans (functor_id C) join_functor.
Proof. refine (@Build_nat_trans C C (functor_id C) join_functor join_unit_component _); intros; apply hom_unique. Defined.

Definition base : C := @Build_object S F P P (@iso_refl (centric_orbit_category F) P)
  (val P) (valP P) (normG (val P)).

Definition base_constant : functor C C.
Proof.
refine (@Build_functor C C (fun _ => base) (fun _ _ _ => Category.identity base) _ _);
  intros; apply hom_unique.
Defined.

Definition base_to_join_component (A : C) : hom C base (join_object A).
Proof.
pose f : DPFusionSystem.arrow F (val P) (val (acting A)) := repr (iso_hom (point A)).
exists f; split.
- change (@Category.compose (centric_orbit_category F) P P (acting A)
    (@Category.identity (centric_orbit_category F) P) (orbit_class f) = iso_hom (point A)).
  rewrite compose_id_left; exact: reprK.
- constructor.
  pose b := DPFusion.compose (val f) (DPFusion.inclusion (subsetT (val (acting A)))).
  refine (@Build_extension S F (val P) (val (acting A) <*> subgroup A)%G
    (val P) (val (acting A)) (val f) (val P) (subxx _) (subxx _) b _ _ _).
  + apply: DPFusionSystem.composition_closed.
    * exact (valP f).
    * exact: DPFusionSystem.inclusion_allowed.
  + move=> x hx; by rewrite /b compose_in // inclusion_in ?map_into.
  + move=> x hx; rewrite /b compose_in // inclusion_in ?map_into //.
    exact (subsetP (joing_subl _ _) _ (map_into (val f) hx)).
Defined.

Definition base_to_join : nat_trans base_constant join_functor.
Proof. refine (@Build_nat_trans C C base_constant join_functor base_to_join_component _); intros; apply hom_unique. Defined.
End Contraction.
End DPNormalizerPointedSubgroupsContraction.

Print Assumptions DPNormalizerPointedSubgroupsContraction.join_unit.
Print Assumptions DPNormalizerPointedSubgroupsContraction.base_to_join.

