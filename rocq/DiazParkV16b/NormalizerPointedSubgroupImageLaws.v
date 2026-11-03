(** The chosen pointed-subgroup image agrees with every actual extension
    presenting the arrow; no map or naturality is supplied as a premise. *)
From mathcomp Require Import all_boot all_fingroup generic_quotient pgroup.
From DiazPark Require Import Category FusionMaps FusionSystems FusionOrbit FusionSaturation.
From DiazParkV16b Require Import NormalizerPointedSubgroupExtensions NormalizerPointedSubgroups
  NormalizerPointedSubgroupImages NormalizerPointedSubgroupImageIndependence
  NormalizerPointedSubgroupImageFactorization NormalizerPointedSubgroupImageComposition.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPFusion DPFusionOrbit DPNormalizerSubgroupExtensions DPNormalizerPointedSubgroups
  DPNormalizerSubgroupImages DPNormalizerPointedSubgroupImageFactorization
  DPNormalizerSubgroupImageIndependence DPNormalizerSubgroupImageComposition.
Local Open Scope group_scope.
Local Open Scope quotient_scope.

Module DPNormalizerPointedSubgroupImageLaws.
Section Laws.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable p : nat.
Hypothesis pS : p.-group [set: S].
Hypothesis sat : DPFusionSaturation.saturated F p.
Variable P : centric_object F.
Local Notation C := (pointed_category P).
Local Notation OC := (centric_orbit_category F).

Theorem arrow_image_eq_extension (A B : C) (h : hom C A B)
    (g : DPFusionSystem.arrow F (val (acting A)) (val (acting B)))
    (hg : @Category.compose OC P (acting A) (acting B) (iso_hom (point A))
      (orbit_class g) = iso_hom (point B))
    (a : extension F (subgroup A) (subgroup B) (val g)) :
    arrow_image h = subgroup_image a.
Proof.
have he : orbit_class (data_raw (chosen_data h)) = orbit_class g.
  have hh := congr1 (fun t => @Category.compose OC (acting A) P (acting B)
    (iso_inv (point A)) t) (eq_trans (data_point (chosen_data h)) (esym hg)).
  by rewrite -!Category.compose_assoc iso_inv_hom !compose_id_left in hh.
exact (@image_eq_of_orbit_eq S F p pS sat _ _ _ _ _ _ _
  (data_extension (chosen_data h)) a (valP (acting A)) (valP (acting B))
  (normalizes A) (raw_onto _) (raw_onto _) he).
Qed.
End Laws.
End DPNormalizerPointedSubgroupImageLaws.
