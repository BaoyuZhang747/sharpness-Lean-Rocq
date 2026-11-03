(** Actual diagram and replacement comparisons from compatible degreewise natural isomorphisms. *)
From mathcomp Require Import all_ssreflect all_algebra boolp.
From DiazPark Require Import Category CategoryExtensionality CategoryModules CategoryModuleLinear CategoryModuleExactness CategoryNaturalIso
  HomologicalComplex HomologicalCohomology HomologicalCohomologyMaps CategoryComplexIso
  HomologicalDiagramInjectives CategoryInjectiveResolutionComparison.
From DiazParkV16b Require Import CategoryCochainReplacementTotal.
Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomological DiazParkCohomology DiazParkCohomologyMaps.

Module DPCategoryCochainReplacementTermIso.
Section Comparison.
Variable R : pzRingType.
Variable C : category.
Variables K L : @diagram_complex R (opposite C).
Variable e : forall n, @isomorphism (functor_category (opposite C) (module_category R))
  (diagram_term K n) (diagram_term L n).
Variable he : forall n c (x : fobj (diagram_term K n) c),
  module_hom_fun (component (diagram_d L n) c)
    (module_hom_fun (component (iso_hom (e n)) c) x) =
  module_hom_fun (component (iso_hom (e n.+1)) c)
    (module_hom_fun (component (diagram_d K n) c) x).

Lemma diagram_term_iso_left n c (x : fobj (diagram_term K n) c) :
  module_hom_fun (component (iso_inv (e n)) c)
    (module_hom_fun (component (iso_hom (e n)) c) x) = x.
Proof. exact (@module_iso_hom_inv_apply R _ _ (nat_iso_component (e n) c) x). Qed.
Lemma diagram_term_iso_right n c (x : fobj (diagram_term L n) c) :
  module_hom_fun (component (iso_hom (e n)) c)
    (module_hom_fun (component (iso_inv (e n)) c) x) = x.
Proof. exact (@module_iso_inv_hom_apply R _ _ (nat_iso_component (e n) c) x). Qed.

Definition diagram_term_iso_map : diagram_cochain_map K L :=
  @Build_diagram_cochain_map R (opposite C) K L (fun n => iso_hom (e n)) he.
Definition diagram_term_iso_inverse : diagram_cochain_map L K.
Proof.
refine (@Build_diagram_cochain_map R (opposite C) L K (fun n => iso_inv (e n)) _).
move=> n c x; apply (@module_iso_hom_injective R _ _ (nat_iso_component (e n.+1) c)).
change (module_hom_fun (component (iso_hom (e n.+1)) c)
  (module_hom_fun (component (diagram_d K n) c) (module_hom_fun (component (iso_inv (e n)) c) x)) =
  module_hom_fun (component (iso_hom (e n.+1)) c)
    (module_hom_fun (component (iso_inv (e n.+1)) c) (module_hom_fun (component (diagram_d L n) c) x))).
by rewrite -he !diagram_term_iso_right.
Defined.

Let T := cochain_replacement_total K.
Let U := cochain_replacement_total L.
Let f := cochain_replacement_total_map diagram_term_iso_map.
Let g := cochain_replacement_total_map diagram_term_iso_inverse.
Definition replacement_term_degree_iso n : @isomorphism (module_category R) (cochain_term T n) (cochain_term U n).
Proof.
refine (@Build_isomorphism (module_category R) (cochain_term T n) (cochain_term U n)
  (module_hom_of_linear (cochain_map_at f n)) (module_hom_of_linear (cochain_map_at g n)) _ _).
- apply module_hom_ext => x; apply functional_extensionality_dep => p;
    apply functional_extensionality_dep => q; apply functional_extensionality_dep => h;
    apply functional_extensionality_dep => c; apply functional_extensionality_dep => t.
  exact: diagram_term_iso_left.
- apply module_hom_ext => x; apply functional_extensionality_dep => p;
    apply functional_extensionality_dep => q; apply functional_extensionality_dep => h;
    apply functional_extensionality_dep => c; apply functional_extensionality_dep => t.
  exact: diagram_term_iso_right.
Defined.
Lemma replacement_term_differential n (x : cochain_term T n) :
  cochain_d U n (module_hom_fun (iso_hom (replacement_term_degree_iso n)) x) =
  module_hom_fun (iso_hom (replacement_term_degree_iso n.+1)) (cochain_d T n x).
Proof. exact: cochain_map_commutes. Qed.
Definition replacement_term_cochain :=
  @term_iso_cochain_map R T U replacement_term_degree_iso replacement_term_differential.
Definition replacement_term_cochain_inverse :=
  @term_iso_cochain_inverse R T U replacement_term_degree_iso replacement_term_differential.
Definition replacement_term_cohomology_iso n :=
  @term_iso_cohomology_iso R T U replacement_term_degree_iso replacement_term_differential n.

Theorem replacement_term_cochain_left n (x : cochain_term T n) :
  cochain_map_at replacement_term_cochain_inverse n (cochain_map_at replacement_term_cochain n x)=x.
Proof. exact: module_iso_hom_inv_apply. Qed.
Theorem replacement_term_cochain_right n (x : cochain_term U n) :
  cochain_map_at replacement_term_cochain n (cochain_map_at replacement_term_cochain_inverse n x)=x.
Proof. exact: module_iso_inv_hom_apply. Qed.
Theorem replacement_term_component n (x : cochain_term T n) p q h c t :
  cochain_map_at replacement_term_cochain n x p q h c t =
  module_hom_fun (component (iso_hom (e q)) c) (x p q h c t).
Proof. reflexivity. Qed.
Theorem replacement_term_projection n (x : cochain_term T n) c :
  cochain_map_at (replacement_projection L c) n (cochain_map_at replacement_term_cochain n x) =
  module_hom_fun (component (iso_hom (e n)) c) (cochain_map_at (replacement_projection K c) n x).
Proof. reflexivity. Qed.
Theorem replacement_term_cohomology_iso_hom n (x : cohomology T n) :
  module_hom_fun (iso_hom (replacement_term_cohomology_iso n)) x =
  cohomology_map replacement_term_cochain n x.
Proof. reflexivity. Qed.
End Comparison.
End DPCategoryCochainReplacementTermIso.
