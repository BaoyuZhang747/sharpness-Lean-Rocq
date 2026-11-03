(** The genuine orbit-category comma-cohomology coefficient functor.
    The comma reindexing laws hold through literal identity-component
    natural transformations, which induce strict cohomology equalities. *)
From mathcomp Require Import all_boot all_algebra all_fingroup.
From DiazPark Require Import Category CategoryComma CategoryModules FusionSystems FusionOrbit.
From DiazParkV16b Require Import LinkingSystem LinkingOrbitProjection LinkingCommaCategory
  CategoryConstantCohomology LinkingCommaCohomology.
Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPCentricLinking DPLinkingOrbit DPLinkingComma.

Module DPLinkingCommaCohomologyDiagram.
Section Reindexing.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Local Notation Obj := (DPFusionOrbit.centric_object F).
Local Notation O := (DPFusionOrbit.centric_orbit_category F).

Definition identity_component (P : Obj) (X : subgroup_comma L P) :
    hom (subgroup_comma L P)
      (fobj (subgroup_comma_map L (@identity O P)) X) X.
Proof.
refine (@Build_costructured_hom (linking_category L) O (orbit_projection L) P
  (fobj (subgroup_comma_map L (@identity O P)) X) X
  (@identity (linking_category L) (costructured_source X)) _).
change (@compose O _ _ _ (fmap (orbit_projection L) (@identity (linking_category L) _))
    (costructured_arrow X) = @compose O _ _ _ (costructured_arrow X) (@identity O P)).
by rewrite fmap_id compose_id_left compose_id_right.
Defined.

Definition identity_naturality (P : Obj) :
    nat_trans (subgroup_comma_map L (@identity O P)) (functor_id (subgroup_comma L P)).
Proof.
refine (@Build_nat_trans (subgroup_comma L P) (subgroup_comma L P)
  (subgroup_comma_map L (@identity O P)) (functor_id (subgroup_comma L P))
  (@identity_component P) _).
move=> X Y f; apply costructured_hom_ext.
change (@compose (linking_category L) _ _ _ (costructured_map f)
    (@identity (linking_category L) _) =
  @compose (linking_category L) _ _ _ (@identity (linking_category L) _) (costructured_map f)).
by rewrite compose_id_left compose_id_right.
Defined.

Definition composition_component (P Q T : Obj) (a : hom O P Q) (b : hom O Q T)
    (X : subgroup_comma L P) : hom (subgroup_comma L T)
      (fobj (functor_comp (subgroup_comma_map L a) (subgroup_comma_map L b)) X)
      (fobj (subgroup_comma_map L (@compose O P Q T a b)) X).
Proof.
refine (@Build_costructured_hom (linking_category L) O (orbit_projection L) T
  (fobj (functor_comp (subgroup_comma_map L a) (subgroup_comma_map L b)) X)
  (fobj (subgroup_comma_map L (@compose O P Q T a b)) X)
  (@identity (linking_category L) (costructured_source X)) _).
change (@compose O _ _ _ (fmap (orbit_projection L) (@identity (linking_category L) _))
    (@compose O _ _ _ (costructured_arrow X) (@compose O _ _ _ a b)) =
  @compose O _ _ _ (@compose O _ _ _ (costructured_arrow X) a) b).
by rewrite fmap_id compose_id_left compose_assoc.
Defined.

Definition composition_naturality (P Q T : Obj) (a : hom O P Q) (b : hom O Q T) :
    nat_trans (functor_comp (subgroup_comma_map L a) (subgroup_comma_map L b))
      (subgroup_comma_map L (@compose O P Q T a b)).
Proof.
refine (@Build_nat_trans (subgroup_comma L P) (subgroup_comma L T)
  (functor_comp (subgroup_comma_map L a) (subgroup_comma_map L b))
  (subgroup_comma_map L (@compose O P Q T a b)) (composition_component a b) _).
move=> X Y f; apply costructured_hom_ext.
change (@compose (linking_category L) _ _ _ (costructured_map f)
    (@identity (linking_category L) _) =
  @compose (linking_category L) _ _ _ (@identity (linking_category L) _) (costructured_map f)).
by rewrite compose_id_left compose_id_right.
Defined.

Section Coefficients.
Variable R : comPzRingType.
Variable A : lmodType R.
Variable n : nat.

Lemma pull_identity (P : Obj) :
    DPLinkingCommaCohomology.pull A L (@identity O P) n =
    module_hom_id (DPLinkingCommaCohomology.value A L P n).
Proof.
change (DPCategoryConstantCohomology.pull A (subgroup_comma_map L (@identity O P)) n =
  module_hom_id (DPCategoryConstantCohomology.value R A (subgroup_comma L P) n)).
rewrite -(@DPCategoryConstantCohomology.pull_nat_trans R A _ _ _ _ (identity_naturality P) n).
exact: DPCategoryConstantCohomology.pull_identity.
Qed.

Lemma pull_composition (P Q T : Obj) (a : hom O P Q) (b : hom O Q T) :
    DPLinkingCommaCohomology.pull A L (@compose O P Q T a b) n =
    module_hom_comp (DPLinkingCommaCohomology.pull A L b n)
      (DPLinkingCommaCohomology.pull A L a n).
Proof.
change (DPCategoryConstantCohomology.pull A (subgroup_comma_map L (@compose O P Q T a b)) n =
  module_hom_comp (DPCategoryConstantCohomology.pull A (subgroup_comma_map L b) n)
    (DPCategoryConstantCohomology.pull A (subgroup_comma_map L a) n)).
rewrite (@DPCategoryConstantCohomology.pull_nat_trans R A _ _ _ _ (composition_naturality a b) n).
exact: DPCategoryConstantCohomology.pull_composition.
Qed.

Definition coefficient : module_codiagram R O.
Proof.
refine (@Build_functor (opposite O) (module_category R)
  (fun P => DPLinkingCommaCohomology.value A L P n)
  (fun P Q a => DPLinkingCommaCohomology.pull A L a n) _ _).
- exact: pull_identity.
- move=> P Q T a b; exact: pull_composition.
Defined.

Lemma coefficient_object (P : Obj) :
    fobj coefficient P = DPLinkingCommaCohomology.value A L P n.
Proof. reflexivity. Qed.

Lemma coefficient_map (P Q : Obj) (a : hom O P Q) :
    @fmap _ _ coefficient Q P a = DPLinkingCommaCohomology.pull A L a n.
Proof. reflexivity. Qed.
End Coefficients.
End Reindexing.
End DPLinkingCommaCohomologyDiagram.

Check DPLinkingCommaCohomologyDiagram.coefficient.
Check DPLinkingCommaCohomologyDiagram.coefficient_map.
Print Assumptions DPLinkingCommaCohomologyDiagram.coefficient.
Print Assumptions DPLinkingCommaCohomologyDiagram.pull_composition.
