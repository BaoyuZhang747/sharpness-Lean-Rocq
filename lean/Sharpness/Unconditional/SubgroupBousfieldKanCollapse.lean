import Sharpness.Unconditional.BousfieldKanReplacementSpectralSequence
import Sharpness.Unconditional.SubgroupCohomologyUnconditional
import Sharpness.Unconditional.SubgroupDecompositionAugmentation
import Sharpness.LinkingSubgroupSpectralSequence
import Sharpness.SpectralConvergenceTransport

/-! Actual Bousfield--Kan pages, E2 identification, geometric abutment and
vertical-axis collapse for the canonical subgroup decomposition. This uses
the constructed singular-cochain replacement filtration, not merely an
abstract edge isomorphism. The main algebraic proof remains separate. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness.FusionSystem.CentricLinkingSystem
open CategoryTheory CategoryTheory.Limits
variable {S : Type u} [Group S] [Finite S] {F : FusionSystem S}
    (L : F.CentricLinkingSystem) (R : Type u) [CommRing R] (A : ModuleCat.{u} R)

def subgroupBousfieldKanSpectralSequence : E₂CohomologicalSpectralSequenceNat (ModuleCat.{u} R) :=
  BousfieldKanReplacement.sequence R A L.subgroupDiagram

omit [Finite S] in
theorem subgroupBousfieldKanSpectralSequence_eq :
    L.subgroupBousfieldKanSpectralSequence R A = L.subgroupE₂SpectralSequence R A := rfl

def subgroupBousfieldKanSecondPageIso (i n : ℕ) :
    ((L.subgroupBousfieldKanSpectralSequence R A).page 2).X (i,n) ≅
      higherLimit (L.subgroupCohomologyDiagram R A n) i :=
  BousfieldKanReplacement.secondPageHigherLimitIso R A L.subgroupDiagram i n

/-- Finite convergence to actual singular cohomology of the uncompleted
linking-system realization, transported by its actual augmentation. -/
def subgroupBousfieldKanConvergence :
    FiniteSpectralConvergence (L.subgroupBousfieldKanSpectralSequence R A)
      (fun n => SingularCohomology.cohomology R L.classifyingSpace A n) :=
  (BousfieldKanReplacement.totalConvergence R A L.subgroupDiagram).transport
    (fun n => (L.subgroupDecompositionCohomologyIso R A n).symm)

theorem subgroupBousfieldKanConvergence_filtration (n j : ℕ) :
    (L.subgroupBousfieldKanConvergence R A).filtration n j =
      (totalColumnHomologyFiltration (L.subgroupBicomplex R A) n j).map
        (L.subgroupDecompositionCohomologyIso R A n).symm.toLinearEquiv.toLinearMap := by
  change ((totalColumnConvergence (L.subgroupBicomplex R A)).filtration n j).map _ = _
  rw [totalColumnConvergence_filtration]

variable (p : ℕ) [Fact p.Prime] (hS : IsPGroup p S) (sat : F.Saturated p)

def subgroupBousfieldKanOrdinarySecondPageIso (i n : ℕ) :
    ((L.subgroupBousfieldKanSpectralSequence R A).page 2).X (i,n) ≅
      higherLimit (F.cohomologyCoefficient (R := R) (A := A) n) i :=
  L.subgroupBousfieldKanSecondPageIso R A i n ≪≫
    higherLimitIso (L.subgroupCohomologyCoefficientIso p R A n hS sat) i

include hS sat in
theorem subgroupBousfieldKan_collapses_onto_vertical_axis
    (k : Type u) [Field k] [CharP k p] (A : ModuleCat.{u} k) :
    (∀ r i n : ℕ, 0 < i →
      IsZero (((L.subgroupBousfieldKanSpectralSequence k A).page (r+2) (by omega)).X (i,n))) ∧
    (∀ (r : ℕ) (pq ab : ℕ × ℕ),
      ((L.subgroupBousfieldKanSpectralSequence k A).page (r+2) (by omega)).d pq ab = 0) ∧
    (∀ r n : ℕ, IsIso (spectralZeroColumnBack (L.subgroupBousfieldKanSpectralSequence k A) r n)) :=
  BousfieldKanReplacement.collapses_onto_vertical_axis k A L.subgroupDiagram
    (fun n => L.subgroupCohomology_acyclic_unconditional p hS sat k A n)

include hS sat in
theorem subgroupBousfieldKan_primeLocal_collapses_onto_vertical_axis
    (A : ModuleCat.{u} (PrimeLocalRing.{u} p)) :
    (∀ r i n : ℕ, 0 < i → IsZero (((L.subgroupBousfieldKanSpectralSequence
      (PrimeLocalRing.{u} p) A).page (r+2) (by omega)).X (i,n))) ∧
    (∀ (r : ℕ) (pq ab : ℕ × ℕ), ((L.subgroupBousfieldKanSpectralSequence
      (PrimeLocalRing.{u} p) A).page (r+2) (by omega)).d pq ab = 0) ∧
    (∀ r n : ℕ, IsIso (spectralZeroColumnBack
      (L.subgroupBousfieldKanSpectralSequence (PrimeLocalRing.{u} p) A) r n)) :=
  BousfieldKanReplacement.collapses_onto_vertical_axis (PrimeLocalRing.{u} p) A L.subgroupDiagram
    (fun n => L.subgroupCohomology_primeLocal_acyclic_unconditional p hS sat A n)

end Sharpness.FusionSystem.CentricLinkingSystem
