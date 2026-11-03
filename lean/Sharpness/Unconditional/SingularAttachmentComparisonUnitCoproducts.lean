import Sharpness.Unconditional.SingularAttachmentComparisonCoproducts
import Sharpness.Unconditional.FirstQuadrantTotalComparisonCoproduct
import Sharpness.Unconditional.RealizationUnitHomologySimplex
import Sharpness.RealizationUnitCochainNaturality

/-! The actual realization unit on an arbitrary coproduct, including the
families of standard simplices attached in a skeletal step. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness.SingularAttachmentComparison
open CategoryTheory CategoryTheory.Limits Simplicial Opposite
open Sharpness.SingularChainExcision

variable (R : Type u) [CommRing R] {ι : Type u}

def explicitChainsCofan (K : ι → ChainComplex (ModuleCat.{u} R) ℕ) : Cofan K :=
  Cofan.mk (coproductChains K) (coproductChainsInclusion K)

def explicitChainsCofanIsColimit (K : ι → ChainComplex (ModuleCat.{u} R) ℕ) :
    IsColimit (explicitChainsCofan R K) :=
  Cofan.IsColimit.mk _
    (fun t => coproductChainsDesc K t.inj)
    (fun t i => coproductChainsInclusion_desc K t.inj i)
    (fun t _ hm => coproductChains_hom_ext K fun i =>
      (hm i).trans (coproductChainsInclusion_desc K t.inj i).symm)

def explicitChainsSigmaIso (K : ι → ChainComplex (ModuleCat.{u} R) ℕ) :
    coproductChains K ≅ ∐ K :=
  (explicitChainsCofanIsColimit R K).coconePointUniqueUpToIso (colimit.isColimit _)

@[reassoc]
theorem explicitChainsSigmaIso_inclusion (K : ι → ChainComplex (ModuleCat.{u} R) ℕ) (i : ι) :
    coproductChainsInclusion K i ≫ (explicitChainsSigmaIso R K).hom = Sigma.ι K i :=
  (explicitChainsCofanIsColimit R K).comp_coconePointUniqueUpToIso_hom
    (colimit.isColimit _) ⟨i⟩

theorem nativeSigmaMap_quasiIso {K L : ι → ChainComplex (ModuleCat.{u} R) ℕ}
    (f : ∀ i, K i ⟶ L i) [∀ i, QuasiIso (f i)] :
    QuasiIso (CategoryTheory.Limits.Sigma.map f) := by
  letI := TotalComparison.coproductChainsMap_quasiIso f
  have h : (explicitChainsSigmaIso R K).hom ≫ CategoryTheory.Limits.Sigma.map f =
      coproductChainsMap K L id f ≫ (explicitChainsSigmaIso R L).hom := by
    apply coproductChains_hom_ext
    intro i
    rw [explicitChainsSigmaIso_inclusion_assoc, Sigma.ι_map,
      coproductChainsMap_inclusion_assoc]
    erw [explicitChainsSigmaIso_inclusion]
    rfl
  haveI : QuasiIso ((explicitChainsSigmaIso R K).hom ≫ CategoryTheory.Limits.Sigma.map f) := by
    rw [h]
    infer_instance
  exact quasiIso_of_comp_left (explicitChainsSigmaIso R K).hom (CategoryTheory.Limits.Sigma.map f)

instance realizationSingularChains_preservesCoproductsOfShape :
    PreservesColimitsOfShape (Discrete ι)
      (SSet.toTop.{u} ⋙ SingularCohomology.chainsFunctor R) := by infer_instance

theorem realizationUnitChainMap_coproduct_naturality (X : ι → SSet.{u}) :
    sigmaComparison (simplicialChainsFunctor R) X ≫ realizationUnitChainMap R (∐ X) =
      CategoryTheory.Limits.Sigma.map (fun i => realizationUnitChainMap R (X i)) ≫
        sigmaComparison (SSet.toTop ⋙ SingularCohomology.chainsFunctor R) X := by
  apply Sigma.hom_ext
  intro i
  rw [ι_comp_sigmaComparison_assoc, Sigma.ι_map_assoc]
  exact (realizationUnitChainMap_naturality R (Sigma.ι X i)).trans
    (congrArg (fun f => realizationUnitChainMap R (X i) ≫ f)
      (ι_comp_sigmaComparison (SSet.toTop ⋙ SingularCohomology.chainsFunctor R) X i).symm)

/-- Arbitrary coproducts of already proved actual realization-unit comparisons. -/
theorem realizationUnitChainMap_coproduct_quasiIso (X : ι → SSet.{u})
    (hX : ∀ i, QuasiIso (realizationUnitChainMap R (X i))) :
    QuasiIso (realizationUnitChainMap R (∐ X)) := by
  letI : ∀ i, QuasiIso (realizationUnitChainMap R (X i)) := hX
  letI := nativeSigmaMap_quasiIso R (fun i => realizationUnitChainMap R (X i))
  haveI : PreservesColimit (Discrete.functor X) (simplicialChainsFunctor R) := by
    change PreservesColimit (Discrete.functor X) (chains R)
    infer_instance
  haveI : QuasiIso (sigmaComparison (simplicialChainsFunctor R) X ≫
      realizationUnitChainMap R (∐ X)) := by
    rw [realizationUnitChainMap_coproduct_naturality]
    infer_instance
  exact quasiIso_of_comp_left (sigmaComparison (simplicialChainsFunctor R) X)
    (realizationUnitChainMap R (∐ X))

/-- The cell-family comparison needed by a skeletal attachment, with no finiteness bound. -/
theorem standardSimplexCoproduct_unit_quasiIso (n : ι → ℕ) :
    QuasiIso (realizationUnitChainMap R (∐ fun i => (Δ[n i] : SSet.{u}))) :=
  realizationUnitChainMap_coproduct_quasiIso R _
    (fun i => RealizationUnitHomology.standardSimplex_unit_quasiIso R ⦋n i⦌)

end Sharpness.SingularAttachmentComparison
