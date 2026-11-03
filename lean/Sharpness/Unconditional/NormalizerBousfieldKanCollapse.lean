import Sharpness.Unconditional.BousfieldKanReplacementSpectralSequence
import Sharpness.Unconditional.NormalizerDecompositionAugmentation
import Sharpness.Unconditional.NormalizerHigherLimitComparisonUnconditional
import Sharpness.SpectralConvergenceTransport

/-! The canonical normalizer decomposition has an actual cohomological
Bousfield--Kan spectral sequence with native higher-limit E2, geometric
abutment, and unconditional vertical-axis collapse. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness.FusionSystem.CentricLinkingSystem
open CategoryTheory CategoryTheory.Limits
variable {S : Type u} [Group S] [Finite S] {F : FusionSystem S}
    (L : F.CentricLinkingSystem) (R : Type u) [CommRing R] (A : ModuleCat.{u} R)

def normalizerBousfieldKanSpectralSequence : E₂CohomologicalSpectralSequenceNat (ModuleCat.{u} R) :=
  BousfieldKanReplacement.sequence R A L.canonicalLibmanNormalizerData.diagram

def normalizerBousfieldKanSecondPageIso (i n : ℕ) :
    ((L.normalizerBousfieldKanSpectralSequence R A).page 2).X (i,n) ≅
      higherLimit (L.canonicalLibmanNormalizerData.cohomologyDiagram R A n) i :=
  BousfieldKanReplacement.secondPageHigherLimitIso R A L.canonicalLibmanNormalizerData.diagram i n

def normalizerBousfieldKanOrdinarySecondPageIso (i n : ℕ) :
    ((L.normalizerBousfieldKanSpectralSequence R A).page 2).X (i,n) ≅
      higherLimit (L.normalizerOrdinaryDiagram R A n) i :=
  L.normalizerBousfieldKanSecondPageIso R A i n ≪≫
    L.normalizerOrdinaryHigherLimitIso_unconditional R A n i

variable (p : ℕ) [Fact p.Prime] (hS : IsPGroup p S) (sat : F.Saturated p)

def normalizerBousfieldKanConvergence :
    FiniteSpectralConvergence (L.normalizerBousfieldKanSpectralSequence R A)
      (fun n => SingularCohomology.cohomology R L.classifyingSpace A n) :=
  (BousfieldKanReplacement.totalConvergence R A L.canonicalLibmanNormalizerData.diagram).transport
    (fun n => (L.normalizerDecompositionCohomologyIso R p hS sat A n).symm)

theorem normalizerBousfieldKanConvergence_filtration (n j : ℕ) :
    (L.normalizerBousfieldKanConvergence R A p hS sat).filtration n j =
      (totalColumnHomologyFiltration (L.canonicalLibmanNormalizerData.bicomplex R A) n j).map
        (L.normalizerDecompositionCohomologyIso R p hS sat A n).symm.toLinearEquiv.toLinearMap := by
  change ((totalColumnConvergence (L.canonicalLibmanNormalizerData.bicomplex R A)).filtration n j).map _ = _
  rw [totalColumnConvergence_filtration]

def normalizerBousfieldKanCentricSecondPageIso
    (k : Type u) [Field k] [CharP k p] (A : ModuleCat.{u} k) (i n : ℕ) :
    ((L.normalizerBousfieldKanSpectralSequence k A).page 2).X (i,n) ≅
      higherLimit (F.cohomologyCoefficient (R := k) (A := A) n) i :=
  L.normalizerBousfieldKanOrdinarySecondPageIso k A i n ≪≫
    L.normalizerNativeHigherLimitIso p hS sat k A n i

include hS sat in
theorem normalizerBousfieldKan_collapses_onto_vertical_axis
    (k : Type u) [Field k] [CharP k p] (A : ModuleCat.{u} k) :
    (∀ r i n : ℕ, 0 < i →
      IsZero (((L.normalizerBousfieldKanSpectralSequence k A).page (r+2) (by omega)).X (i,n))) ∧
    (∀ (r : ℕ) (pq ab : ℕ × ℕ),
      ((L.normalizerBousfieldKanSpectralSequence k A).page (r+2) (by omega)).d pq ab = 0) ∧
    (∀ r n : ℕ, IsIso (spectralZeroColumnBack (L.normalizerBousfieldKanSpectralSequence k A) r n)) :=
  BousfieldKanReplacement.collapses_onto_vertical_axis k A L.canonicalLibmanNormalizerData.diagram
    (fun n => acyclic_of_iso (L.normalizerOrdinaryDiagramIso_unconditional k A n)
      (L.normalizerOrdinary_acyclic_unconditional p hS sat k A n))

end Sharpness.FusionSystem.CentricLinkingSystem
