(** Any two actual projective resolutions give isomorphic Hom cohomology. *)
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryExtensionality CategoryModules
  CategoryDiagramHom CategoryEnoughProjectivesResolution CategoryEnoughProjectivesComparison
  CategoryEnoughProjectivesComparisonHomotopy ProjectiveExtComplex
  HomologicalComplex HomologicalCohomology HomologicalCohomologyMaps
  MackeyModuleCarriers MackeyModuleQuotient.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPEnoughProjectiveResolutions DPProjectiveComparison
  DPProjectiveHomotopy DPProjectiveExt DiazParkHomological DiazParkCohomology DiazParkCohomologyMaps.
Local Open Scope ring_scope.
Local Opaque module_quotient.

Module DPProjectiveExtIndependence.
Section Homotopy.
Variables (R : comPzRingType) (C : category).
Variables A B D : module_diagram R C.
Variables (P : projective_resolution A) (Q : projective_resolution B).
Variable u : nat_trans A B.
Variables f g : projective_resolution_map P Q u.
Variable h : projective_resolution_homotopy f g.
Definition projective_hom_homotopy :
    cochain_homotopy (projective_hom_map D f) (projective_hom_map D g).
Proof.
refine (@CochainHomotopy R (projective_hom_complex Q D) (projective_hom_complex P D)
  (projective_hom_map D f) (projective_hom_map D g)
  (fun n => (diagram_hom_pre D (projective_homotopy_at h n) :
    {linear diagram_hom_type (projective_term Q n.+1) D ->
      diagram_hom_type (projective_term P n) D})) _ _).
- intro a; apply diagram_hom_ext; intros x v.
  rewrite diagram_hom_at_add diagram_hom_at_opp.
  change (module_hom_fun (component a x) (module_hom_fun (component (projective_resolution_map_at f 0%N) x) v) -
    module_hom_fun (component a x) (module_hom_fun (component (projective_resolution_map_at g 0%N) x) v) =
    module_hom_fun (component a x) (module_hom_fun (component (projective_d Q 0%N) x)
      (module_hom_fun (component (projective_homotopy_at h 0%N) x) v))).
  by rewrite -module_hom_sub (projective_homotopy_zero h).
- intros n a; apply diagram_hom_ext; intros x v.
  rewrite !diagram_hom_at_add diagram_hom_at_opp.
  change (module_hom_fun (component a x) (module_hom_fun (component (projective_resolution_map_at f n.+1) x) v) -
    module_hom_fun (component a x) (module_hom_fun (component (projective_resolution_map_at g n.+1) x) v) =
    module_hom_fun (component a x) (module_hom_fun (component (projective_homotopy_at h n) x)
      (module_hom_fun (component (projective_d P n) x) v)) +
    module_hom_fun (component a x) (module_hom_fun (component (projective_d Q n.+1) x)
      (module_hom_fun (component (projective_homotopy_at h n.+1) x) v))).
  by rewrite -module_hom_sub (projective_homotopy_succ h) module_hom_add.
Defined.

Lemma projective_hom_maps_equal n (q : cohomology (projective_hom_complex Q D) n) :
    cohomology_map (projective_hom_map D f) n q = cohomology_map (projective_hom_map D g) n q.
Proof. exact: (cohomology_map_homotopy projective_hom_homotopy). Qed.
End Homotopy.

Section Independence.
Variables (R : comPzRingType) (C : category).
Variables A D : module_diagram R C.
Variables P Q : projective_resolution A.

Definition double_identity_lift (X : projective_resolution A) :
    projective_resolution_map X X (nat_comp (nat_id A) (nat_id A)).
Proof.
refine (@Build_projective_resolution_map R C A A X X
  (nat_comp (nat_id A) (nat_id A)) (fun n => nat_id (projective_term X n)) _ _).
- intros n x v; reflexivity.
- apply nat_trans_ext; intro x; apply module_hom_ext; intro v; reflexivity.
Defined.

Lemma projective_hom_inverse (f : projective_resolution_map P Q (nat_id A))
    (g : projective_resolution_map Q P (nat_id A)) n
    (q : cohomology (projective_hom_complex P D) n) :
    cohomology_map (projective_hom_map D f) n
      (cohomology_map (projective_hom_map D g) n q) = q.
Proof.
have [z <-] := quotient_pi_surjective q.
have he := projective_hom_maps_equal (D := D)
  (projective_resolution_maps_homotopic (projective_resolution_composition f g)
    (double_identity_lift P)) (quotient_pi (boundaries_in_cycles (projective_hom_complex P D) n) z).
rewrite !cohomology_map_pi in he *.
transitivity (quotient_pi (boundaries_in_cycles (projective_hom_complex P D) n) (cycle_map
  (projective_hom_map D (projective_resolution_composition f g)) n z)).
- congr (quotient_pi _ _); apply submodule_val_injective; apply diagram_hom_ext; intros x v; reflexivity.
- rewrite he; congr (quotient_pi _ _); apply submodule_val_injective; apply diagram_hom_ext; intros x v; reflexivity.
Qed.

End Independence.
Section Isomorphism.
Variables (R : comPzRingType) (C : category).
Variables A D : module_diagram R C.
Variables P Q : projective_resolution A.

Definition projective_hom_resolution_iso n : @isomorphism (module_category R)
    [the lmodType R of cohomology (projective_hom_complex P D) n]
    [the lmodType R of cohomology (projective_hom_complex Q D) n].
Proof.
pose f := projective_resolution_comparison P Q (nat_id A).
pose g := projective_resolution_comparison Q P (nat_id A).
refine (@Build_isomorphism (module_category R) _ _
  (module_hom_of_linear (cohomology_map (projective_hom_map D g) n))
  (module_hom_of_linear (cohomology_map (projective_hom_map D f) n)) _ _).
- apply module_hom_ext; intro q; exact: projective_hom_inverse.
- apply module_hom_ext; intro q.
  exact: (@projective_hom_inverse R C A D Q P g f n q).
Defined.
End Isomorphism.
End DPProjectiveExtIndependence.
