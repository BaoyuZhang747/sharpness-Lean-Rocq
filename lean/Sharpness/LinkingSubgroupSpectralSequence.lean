import Sharpness.LinkingSubgroupCochains
import Sharpness.ColumnFilteredSpectralObject
import Sharpness.ColumnHomologyFiltration

/-! The actual subgroup singular double complex determines a native
first-quadrant spectral sequence, for every constant module A. The pages
are constructed from the actual column filtration. Finite convergence
is proved in LinkingSubgroupConvergence. Identifying E2 with native
higher limits remains explicit work, not an assumed field. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem.CentricLinkingSystem
open CategoryTheory
variable {S : Type u} [Group S] {F : FusionSystem S}
    (L : F.CentricLinkingSystem) (R : Type u) [CommRing R] (A : ModuleCat.{u} R)

def subgroupColumnSpectralSequence : CohomologicalSpectralSequenceNat (ModuleCat.{u} R) 1 :=
  totalColumnSpectralSequence (L.subgroupBicomplex R A)

def subgroupE₂SpectralSequence : E₂CohomologicalSpectralSequenceNat (ModuleCat.{u} R) :=
  totalColumnE₂SpectralSequence (L.subgroupBicomplex R A)

def subgroupTotalHomologyFiltration (n k : ℕ) :
    Submodule R ((L.subgroupTotalCochains R A).homology n) :=
  totalColumnHomologyFiltration (L.subgroupBicomplex R A) n k

theorem subgroupTotalHomologyFiltration_start (n : ℕ) :
    L.subgroupTotalHomologyFiltration R A n 0 = ⊤ :=
  totalColumnHomologyFiltration_start (L.subgroupBicomplex R A) n

theorem subgroupTotalHomologyFiltration_stop (n : ℕ) :
    L.subgroupTotalHomologyFiltration R A n (n+1) = ⊥ :=
  totalColumnHomologyFiltration_stop (L.subgroupBicomplex R A) n

end Sharpness.FusionSystem.CentricLinkingSystem
