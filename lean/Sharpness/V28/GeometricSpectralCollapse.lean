import Sharpness.V28.SubgroupSharpness
import Sharpness.V28.NormalizerSharpness
import Sharpness.Unconditional.SubgroupBousfieldKanCollapse
import Sharpness.Unconditional.NormalizerBousfieldKanCollapse

/-! Collapse of the constructed subgroup and normalizer replacement sequences. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness.FusionSystem.CentricLinkingSystem.V28
open CategoryTheory CategoryTheory.Limits
variable {S : Type u} [Group S] [Finite S] {F : FusionSystem S}
    (L : F.CentricLinkingSystem) (p : ℕ) [Fact p.Prime]
    (hS : IsPGroup p S) (sat : F.Saturated p)
    (k : Type u) [Field k] [CharP k p] (A : ModuleCat.{u} k)

include p hS sat

def normalizerBousfieldKanCentricSecondPageIso (i n : ℕ) :
    ((L.normalizerBousfieldKanSpectralSequence k A).page 2).X (i,n) ≅
      higherLimit (F.cohomologyCoefficient (R := k) (A := A) n) i :=
  L.normalizerBousfieldKanOrdinarySecondPageIso k A i n ≪≫
    normalizerNativeHigherLimitIso L p hS sat k A n i

theorem subgroupBousfieldKan_collapses_onto_vertical_axis :
    (∀ r i n : ℕ, 0 < i →
      IsZero (((L.subgroupBousfieldKanSpectralSequence k A).page (r+2) (by omega)).X (i,n))) ∧
    (∀ (r : ℕ) (pq ab : ℕ × ℕ),
      ((L.subgroupBousfieldKanSpectralSequence k A).page (r+2) (by omega)).d pq ab = 0) ∧
    (∀ r n : ℕ, IsIso (spectralZeroColumnBack (L.subgroupBousfieldKanSpectralSequence k A) r n)) :=
  BousfieldKanReplacement.collapses_onto_vertical_axis k A L.subgroupDiagram
    (fun n => subgroupCohomology_acyclic L p hS sat k A n)

theorem normalizerBousfieldKan_collapses_onto_vertical_axis :
    (∀ r i n : ℕ, 0 < i →
      IsZero (((L.normalizerBousfieldKanSpectralSequence k A).page (r+2) (by omega)).X (i,n))) ∧
    (∀ (r : ℕ) (pq ab : ℕ × ℕ),
      ((L.normalizerBousfieldKanSpectralSequence k A).page (r+2) (by omega)).d pq ab = 0) ∧
    (∀ r n : ℕ, IsIso (spectralZeroColumnBack (L.normalizerBousfieldKanSpectralSequence k A) r n)) :=
  BousfieldKanReplacement.collapses_onto_vertical_axis k A L.canonicalLibmanNormalizerData.diagram
    (fun n => normalizerCohomology_acyclic L p hS sat k A n)

end Sharpness.FusionSystem.CentricLinkingSystem.V28
