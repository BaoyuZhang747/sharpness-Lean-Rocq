import Sharpness.Unconditional.SingularChainExcisionSubspaces

/-! The actual singular-chain sequence of two subspaces. Its last object
is the native chain complex of simplices wholly in one of the two subspaces. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness.SingularChainExcision
open CategoryTheory CategoryTheory.Limits
open Sharpness.RealizationUnitHomology

variable (R : Type u) [CommRing R] (X : TopCat.{u}) (U V : Set X)

def intersectionChainsIso :
    ((SingularCohomology.chainsFunctor R).obj (TopCat.of ↥(U ∩ V))) ≅
      ((singularInSubcomplex X U ⊓ singularInSubcomplex X V).toSSet.chainComplex
        (ModuleCat.of R R)) :=
  singularSubsetChainsIso X R (U ∩ V) ≪≫
    (chains R).mapIso (SSet.Subcomplex.eqToIso (singularInSubcomplex_inf X U V))

def binarySmallChainsIso :
    ((singularInSubcomplex X U ⊔ singularInSubcomplex X V).toSSet.chainComplex
      (ModuleCat.of R R)) ≅ smallSingularChains X (fun b : Bool => if b then U else V) R :=
  (chains R).mapIso (SSet.Subcomplex.eqToIso (singularInSubcomplex_sup X U V))

def binarySmallLeft :
    ((SingularCohomology.chainsFunctor R).obj (TopCat.of U)) ⟶
      smallSingularChains X (fun b : Bool => if b then U else V) R :=
  (singularSubsetChainsIso X R U).hom ≫
    SSet.chainComplexMap (SSet.Subcomplex.homOfLE (le_sup_left :
      singularInSubcomplex X U ≤ singularInSubcomplex X U ⊔ singularInSubcomplex X V))
      (ModuleCat.of R R) ≫ (binarySmallChainsIso R X U V).hom

def binarySmallRight :
    ((SingularCohomology.chainsFunctor R).obj (TopCat.of V)) ⟶
      smallSingularChains X (fun b : Bool => if b then U else V) R :=
  (singularSubsetChainsIso X R V).hom ≫
    SSet.chainComplexMap (SSet.Subcomplex.homOfLE (le_sup_right :
      singularInSubcomplex X V ≤ singularInSubcomplex X U ⊔ singularInSubcomplex X V))
      (ModuleCat.of R R) ≫ (binarySmallChainsIso R X U V).hom

theorem subspaceUnion_isPushout :
    IsPushout
      ((SingularCohomology.chainsFunctor R).map (subsetMap X (Set.inter_subset_left : U ∩ V ⊆ U)))
      ((SingularCohomology.chainsFunctor R).map (subsetMap X (Set.inter_subset_right : U ∩ V ⊆ V)))
      (binarySmallLeft R X U V) (binarySmallRight R X U V) := by
  apply (subcomplexUnion_isPushout R (singularInSubcomplex X U)
    (singularInSubcomplex X V)).of_iso'
      (intersectionChainsIso R X U V) (singularSubsetChainsIso X R U)
      (singularSubsetChainsIso X R V) (binarySmallChainsIso R X U V).symm
  · calc
      _ = (singularSubsetChainsIso X R (U ∩ V)).hom ≫
          SSet.chainComplexMap (SSet.Subcomplex.homOfLE
            (singularInSubcomplex_mono X (Set.inter_subset_left : U ∩ V ⊆ U)))
            (ModuleCat.of R R) := by
        change (_ ≫ (chains R).map _) ≫ (chains R).map _ = _ ≫ (chains R).map _
        rw [Category.assoc, ← (chains R).map_comp]
        rfl
      _ = _ := (singularSubsetChainsIso_naturality X R Set.inter_subset_left).symm
  · calc
      _ = (singularSubsetChainsIso X R (U ∩ V)).hom ≫
          SSet.chainComplexMap (SSet.Subcomplex.homOfLE
            (singularInSubcomplex_mono X (Set.inter_subset_right : U ∩ V ⊆ V)))
            (ModuleCat.of R R) := by
        change (_ ≫ (chains R).map _) ≫ (chains R).map _ = _ ≫ (chains R).map _
        rw [Category.assoc, ← (chains R).map_comp]
        rfl
      _ = _ := (singularSubsetChainsIso_naturality X R Set.inter_subset_right).symm
  · simp only [binarySmallLeft, Iso.symm_hom, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  · simp only [binarySmallRight, Iso.symm_hom, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]

/-- C(U∩V) → C(U)⊞C(V) → C_small({U,V}), with maps (i,-j) and (k,l). -/
def subspaceUnionSequence : ShortComplex (ChainComplex (ModuleCat.{u} R) ℕ) :=
  (subspaceUnion_isPushout R X U V).shortComplex

theorem subspaceUnionSequence_shortExact : (subspaceUnionSequence R X U V).ShortExact where
  exact := (subspaceUnion_isPushout R X U V).exact_shortComplex
  mono_f := by
    have h : (subspaceUnionSequence R X U V).f ≫ biprod.fst =
        (SingularCohomology.chainsFunctor R).map (subsetMap X (Set.inter_subset_left : U ∩ V ⊆ U)) :=
      biprod.lift_fst _ _
    haveI : Mono ((subspaceUnionSequence R X U V).f ≫ biprod.fst) := by
      rw [h]
      infer_instance
    exact mono_of_mono _ biprod.fst
  epi_g := (subspaceUnion_isPushout R X U V).epi_shortComplex_g

theorem subspaceUnionSequence_degree_shortExact (n : ℕ) :
    ((subspaceUnionSequence R X U V).map
      (HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.down ℕ) n)).ShortExact :=
  (subspaceUnionSequence_shortExact R X U V).map_of_exact _

end Sharpness.SingularChainExcision
