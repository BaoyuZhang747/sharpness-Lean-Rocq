(** Hom from any actual projective resolution, with its genuine differential. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryExtensionality CategoryModules
  CategoryModuleLinear CategoryDiagramHom CategoryEnoughProjectivesResolution
  CategoryEnoughProjectivesComparison HomologicalComplex HomologicalCohomology
  HomologicalCohomologyMaps MackeyModuleCarriers MackeyModuleQuotient.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPEnoughProjectiveResolutions DPProjectiveComparison
  DiazParkHomological DiazParkCohomology DiazParkCohomologyMaps.
Local Open Scope ring_scope.

Module DPProjectiveExt.
Section Precomposition.
Variables (R : comPzRingType) (C : category).
Variables A B D : module_diagram R C.
Variable u : nat_trans A B.
Definition diagram_hom_pre (f : diagram_hom_type B D) : diagram_hom_type A D := nat_comp u f.
Lemma diagram_hom_pre_linear : linear diagram_hom_pre.
Proof. intros a f g; apply diagram_hom_ext; intros x v; reflexivity. Qed.
HB.instance Definition _ := GRing.isLinear.Build R (diagram_hom_type B D)
  (diagram_hom_type A D) _ diagram_hom_pre diagram_hom_pre_linear.
End Precomposition.
Arguments diagram_hom_pre {R C A B} D u f.

Section Complex.
Variables (R : comPzRingType) (C : category).
Variable A : module_diagram R C.
Variable P : projective_resolution A.
Variable D : module_diagram R C.

Definition projective_hom_complex : cochain_complex R.
Proof.
refine (@CochainComplex R (fun n => diagram_hom_type (projective_term P n) D)
  (fun n => (diagram_hom_pre D (projective_d P n) :
    {linear diagram_hom_type (projective_term P n) D ->
      diagram_hom_type (projective_term P n.+1) D})) _).
intros n f; apply diagram_hom_ext; intros x v.
change (module_hom_fun (component f x)
  (module_hom_fun (component (projective_d P n) x)
    (module_hom_fun (component (projective_d P n.+1) x) v)) = 0).
by rewrite projective_d_squared module_hom_zero.
Defined.
End Complex.
Arguments projective_hom_complex {R C A} P D.

Section Maps.
Variables (R : comPzRingType) (C : category).
Variables A B D : module_diagram R C.
Variables (P : projective_resolution A) (Q : projective_resolution B).
Variable u : nat_trans A B.
Variable m : projective_resolution_map P Q u.

Definition projective_hom_map : cochain_map (projective_hom_complex Q D)
    (projective_hom_complex P D).
Proof.
refine (@CochainMap R (projective_hom_complex Q D) (projective_hom_complex P D)
  (fun n => (diagram_hom_pre D (projective_resolution_map_at m n) :
    {linear diagram_hom_type (projective_term Q n) D ->
      diagram_hom_type (projective_term P n) D})) _).
intros n f; apply diagram_hom_ext; intros x v.
change (module_hom_fun (component f x)
  (module_hom_fun (component (projective_resolution_map_at m n) x)
    (module_hom_fun (component (projective_d P n) x) v)) =
  module_hom_fun (component f x)
  (module_hom_fun (component (projective_d Q n) x)
    (module_hom_fun (component (projective_resolution_map_at m n.+1) x) v))).
by rewrite projective_resolution_map_commutes.
Defined.
End Maps.
Arguments projective_hom_map {R C A B} D {P Q u} m.

Definition projective_hom_coefficient_map {R : comPzRingType} {C : category}
    {A : module_diagram R C} (P : projective_resolution A)
    {D E : module_diagram R C} (u : nat_trans D E) :
    cochain_map (projective_hom_complex P D) (projective_hom_complex P E).
Proof.
refine (@CochainMap R (projective_hom_complex P D) (projective_hom_complex P E)
  (fun n => (diagram_hom_post (projective_term P n) u :
    {linear diagram_hom_type (projective_term P n) D ->
      diagram_hom_type (projective_term P n) E})) _).
intros n f; apply diagram_hom_ext; intros x v; reflexivity.
Defined.
End DPProjectiveExt.
