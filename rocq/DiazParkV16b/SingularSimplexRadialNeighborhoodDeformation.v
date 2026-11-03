(** Actual deformation of the literal open radial neighborhood in a cell attachment. *)
From mathcomp Require Import all_ssreflect all_algebra all_classical reals topology subtype_topology.
From DiazPark Require Import Category.
From DiazParkV16b Require Import TopologicalCategory TopologicalCategoryHomotopy
  TopologicalPushoutCarrier TopologicalOpenImage SingularSimplexRadialFamily
  SingularSimplexRadialAttachment SingularSimplexRadialNeighborhoodMaps SingularSimplexRadialNeighborhood.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPTopological DPTopologicalHomotopy DPTopologicalPushoutCarrier DPTopologicalOpenImage
  DPSingularSimplexRadialFamily DPSingularSimplexRadialAttachment
  DPSingularSimplexRadialNeighborhoodMaps DPSingularSimplexRadialNeighborhood.

Module DPSingularSimplexRadialNeighborhoodDeformation.
Section Neighborhood.
Variable Real : realType.
Variable I : choiceType.
Variable d : I -> nat.
Variable X : topologicalType.
Variable j : hom topological_category (boundary_family Real d) X.

Definition radial_neighborhood_space := [the topologicalType of set_type (@radial_neighborhood Real I d X j)].
Definition radial_neighborhood_homeomorphism : homeomorphism
    (@radial_attaching_space Real I d X j) radial_neighborhood_space :=
  @open_image_homeomorphism _ _ (radial_neighborhood_map j)
    (@radial_neighborhood_injective Real I d X j) (@radial_neighborhood_open_image Real I d X j).

Lemma radial_neighborhood_homeomorphism_val z :
  val (iso_hom radial_neighborhood_homeomorphism z) = radial_neighborhood_map j z.
Proof. reflexivity. Qed.

Definition radial_old_to_neighborhood : continuousType X radial_neighborhood_space :=
  continuous_compose (attaching_right_map (family_boundary_punctured Real d) j)
    (iso_hom radial_neighborhood_homeomorphism).
Definition radial_neighborhood_retraction : continuousType radial_neighborhood_space X :=
  continuous_compose (iso_inv radial_neighborhood_homeomorphism) (radial_attaching_retraction j).

Lemma radial_old_to_neighborhood_val x :
  val (radial_old_to_neighborhood x) = attaching_right (family_boundary_inclusion Real d) j x.
Proof. exact: radial_neighborhood_map_right. Qed.

Lemma radial_neighborhood_retraction_equation x :
  radial_neighborhood_retraction (radial_old_to_neighborhood x) = x.
Proof.
change (radial_attaching_retraction j (iso_inv radial_neighborhood_homeomorphism
  (iso_hom radial_neighborhood_homeomorphism (attaching_right (family_boundary_punctured Real d) j x))) = x).
rewrite homeomorphism_forwardK; exact: radial_attaching_retraction_right.
Qed.

Definition radial_neighborhood_deformation_map : continuousType
    (unit_interval_space Real * radial_neighborhood_space)%type radial_neighborhood_space.
Proof.
refine (@continuous_map _ _ (fun p => iso_hom radial_neighborhood_homeomorphism
  (homotopy_map (radial_attaching_homotopy j) (p.1,iso_inv radial_neighborhood_homeomorphism p.2))) _).
move=> p; apply: (@continuous_comp _ (@radial_attaching_space Real I d X j) radial_neighborhood_space
  (fun q => homotopy_map (radial_attaching_homotopy j) (q.1,iso_inv radial_neighborhood_homeomorphism q.2))
  (iso_hom radial_neighborhood_homeomorphism) p); last exact: cts_fun.
apply: (@continuous_comp _ [the topologicalType of (unit_interval_space Real * @radial_attaching_space Real I d X j)%type]
  (@radial_attaching_space Real I d X j)
  (fun q => (q.1,iso_inv radial_neighborhood_homeomorphism q.2))
  (homotopy_map (radial_attaching_homotopy j)) p); last exact: cts_fun.
apply: (@cvg_pair _ (unit_interval_space Real) (@radial_attaching_space Real I d X j)
  (nbhs p) (nbhs p.1) (nbhs (iso_inv radial_neighborhood_homeomorphism p.2))
  (@nbhs_filter [the topologicalType of (unit_interval_space Real * radial_neighborhood_space)%type] p)
  (@nbhs_filter (unit_interval_space Real) p.1)
  (@nbhs_filter (@radial_attaching_space Real I d X j) (iso_inv radial_neighborhood_homeomorphism p.2)));
  first exact: cvg_fst.
apply: (@continuous_comp _ radial_neighborhood_space (@radial_attaching_space Real I d X j)
  snd (iso_inv radial_neighborhood_homeomorphism) p); [exact: cvg_snd | exact: cts_fun].
Defined.

Definition radial_neighborhood_deformation : continuous_homotopy Real
    (continuous_identity radial_neighborhood_space)
    (continuous_compose radial_neighborhood_retraction radial_old_to_neighborhood).
Proof.
refine (@ContinuousHomotopy Real _ _ _ _ radial_neighborhood_deformation_map _ _).
- move=> z; change (iso_hom radial_neighborhood_homeomorphism
    (homotopy_map (radial_attaching_homotopy j) (interval_zero Real,iso_inv radial_neighborhood_homeomorphism z)) = z).
  by rewrite homotopy_start homeomorphism_inverseK.
- move=> z; change (iso_hom radial_neighborhood_homeomorphism
    (homotopy_map (radial_attaching_homotopy j) (interval_one Real,iso_inv radial_neighborhood_homeomorphism z)) =
      radial_old_to_neighborhood (radial_neighborhood_retraction z)).
  rewrite homotopy_end; reflexivity.
Defined.

Theorem radial_neighborhood_deformation_fixed t x :
  homotopy_map radial_neighborhood_deformation (t,radial_old_to_neighborhood x) = radial_old_to_neighborhood x.
Proof.
change (iso_hom radial_neighborhood_homeomorphism
  (homotopy_map (radial_attaching_homotopy j) (t,iso_inv radial_neighborhood_homeomorphism
    (iso_hom radial_neighborhood_homeomorphism (attaching_right (family_boundary_punctured Real d) j x)))) =
      radial_old_to_neighborhood x).
by rewrite homeomorphism_forwardK radial_attaching_homotopy_fixed.
Qed.

End Neighborhood.
End DPSingularSimplexRadialNeighborhoodDeformation.
