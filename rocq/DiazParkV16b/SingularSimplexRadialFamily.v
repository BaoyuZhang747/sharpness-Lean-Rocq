(** Actual arbitrary families of simplex punctures and boundary-fixed radial deformations. *)
From mathcomp Require Import all_ssreflect all_algebra all_classical.
From mathcomp Require Import reals topology sigT_topology subtype_topology.
From DiazPark Require Import Category.
From DiazParkV16b Require Import TopologicalCategory TopologicalCategoryHomotopy
  TopologicalSimplexBasic SingularSimplexRadialContinuity SingularSimplexRadialDeformationGeometry
  SingularSimplexRadialDeformation TopologicalCoproductHomotopy.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPTopological DPTopologicalHomotopy DPTopologicalSimplex
  DPSingularSimplexRadialContinuity DPSingularSimplexRadialDeformationGeometry
  DPSingularSimplexRadialDeformation DPTopologicalCoproductHomotopy.
Local Open Scope classical_set_scope.

Module DPSingularSimplexRadialFamily.
Section Family.
Variable Real : realType.
Variable I : choiceType.
Variable d : I -> nat.

Definition cell_family := family_space (fun i => simplex_space Real (d i)).
Definition boundary_family := family_space (fun i => boundary_space Real (d i)).
Definition punctured_family := family_space (fun i => punctured_space Real (d i)).

Definition punctured_cell_map n : continuousType (punctured_space Real n) (simplex_space Real n) :=
  continuous_map (@punctured_val_continuous Real n).

Definition boundary_cell_map n : continuousType (boundary_space Real n) (simplex_space Real n).
Proof.
refine (@continuous_map (boundary_space Real n) (simplex_space Real n) (fun x => val x) _).
exact: initial_continuous.
Defined.

Definition family_punctured_inclusion : continuousType punctured_family cell_family :=
  family_map (fun i => punctured_cell_map (d i)).
Definition family_boundary_inclusion : continuousType boundary_family cell_family :=
  family_map (fun i => boundary_cell_map (d i)).
Definition family_boundary_punctured : continuousType boundary_family punctured_family :=
  family_map (fun i => boundary_punctured_map Real (d i)).
Definition family_radial_projection : continuousType punctured_family boundary_family :=
  family_map (fun i => radial_boundary_map Real (d i)).

Lemma family_boundary_factorization :
  continuous_compose family_boundary_punctured family_punctured_inclusion = family_boundary_inclusion.
Proof. apply: topological_hom_ext => [[i x]]; reflexivity. Qed.

Lemma family_radial_retraction :
  continuous_compose family_boundary_punctured family_radial_projection = continuous_identity boundary_family.
Proof.
apply: topological_hom_ext => [[i x]].
change (existT (fun i => boundary_space Real (d i)) i
  (radial_boundary_map Real (d i) (boundary_punctured_map Real (d i) x)) = existT _ i x).
by rewrite radial_boundary_map_retraction.
Qed.

Definition family_radial_homotopy : continuous_homotopy Real
    (continuous_identity punctured_family)
    (continuous_compose family_radial_projection family_boundary_punctured).
Proof.
pose H := @family_homotopy Real I (fun i => punctured_space Real (d i))
  (fun i => punctured_space Real (d i))
  (fun i => continuous_identity (punctured_space Real (d i)))
  (fun i => continuous_compose (radial_boundary_map Real (d i))
    (boundary_punctured_map Real (d i)))
  (fun i => radial_deformation Real (d i)).
refine (@ContinuousHomotopy Real _ _ _ _ (homotopy_map H) _ _).
- move=> [i x]; by rewrite (homotopy_start H).
- move=> [i x]; by rewrite (homotopy_end H).
Defined.

Lemma family_radial_homotopy_fixed t b :
  homotopy_map family_radial_homotopy (t, family_boundary_punctured b) = family_boundary_punctured b.
Proof.
case: b => i x.
change (existT (fun i => punctured_space Real (d i)) i
  (homotopy_map (radial_deformation Real (d i)) (t,boundary_punctured_map Real (d i) x)) =
  existT _ i (boundary_punctured_map Real (d i) x)).
by rewrite radial_deformation_fixed.
Qed.

Definition family_punctured_set : set cell_family :=
  fun z => @punctured_set Real (d (projT1 z)) (projT2 z).

Lemma family_punctured_set_open : open family_punctured_set.
Proof.
apply/sigT_openP => i.
change (@open (simplex_space Real (d i)) (@punctured_set Real (d i))).
exact: punctured_set_open.
Qed.

Lemma family_punctured_range :
  family_punctured_inclusion @` [set: punctured_family] = family_punctured_set.
Proof.
apply/seteqP; split=> z.
- move=> [[i x] _ <-]. exact: (@punctured_property Real (d i) x).
- case: z => i x hx.
  exists (existT (fun i => punctured_space Real (d i)) i (exist _ x (mem_set hx))); first by [].
  reflexivity.
Qed.

End Family.
End DPSingularSimplexRadialFamily.
