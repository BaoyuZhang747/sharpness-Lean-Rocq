import Sharpness.ColumnIntegerConvergence
import Sharpness.SpectralConvergenceTransport
import Sharpness.CochainSubmoduleHomology

/-! Finite convergence of the actual column spectral sequence to the
native cohomology of the original natural-number total complex. The
abutment comparison is extension by zero followed by the zeroth
filtered-complex inclusion, whose every component is an isomorphism. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory
variable {R : Type u} [CommRing R]
    (K : HomologicalComplex₂ (ModuleCat.{u} R) (ComplexShape.up ℕ) (ComplexShape.up ℕ))

set_option backward.isDefEq.respectTransparency false in
def totalColumnAbutmentIso (n : ℕ) :
    ((totalColumnFiltrationIntFunctor K).obj (OrderDual.toDual 0)).homology (n : ℤ) ≅
      (K.total (ComplexShape.up ℕ)).homology n := by
  let V := totalColumnSubmodules K 0
  letI : IsIso V.inclusion := V.inclusion_isIso_of_top (totalColumnFiltration_start K)
  letI : IsIso (HomologicalComplex.homologyMap V.inclusion n) :=
    inferInstanceAs (IsIso ((HomologicalComplex.homologyFunctor (ModuleCat.{u} R)
      (ComplexShape.up ℕ) n).map V.inclusion))
  let eH := asIso (HomologicalComplex.homologyMap V.inclusion n)
  exact (totalColumnFilteredComplex K 0).extendHomologyIso ComplexShape.embeddingUpNat
    (show ComplexShape.embeddingUpNat.f n = (n : ℤ) from rfl) ≪≫
      eH

def totalColumnConvergence : FiniteSpectralConvergence (totalColumnE₂SpectralSequence K)
    (fun n => (K.total (ComplexShape.up ℕ)).homology n) :=
  (totalColumnIntegerConvergence K).transport (totalColumnAbutmentIso K)

end Sharpness
