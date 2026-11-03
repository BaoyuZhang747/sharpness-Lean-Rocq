import Sharpness.ColumnFiltrationFunctor
import Sharpness.ColumnFiltrationSupport
import Sharpness.CochainSubmoduleHomology

/-! The actual finite filtration on total cohomology, defined as images
of the homology maps of the actual column subcomplex inclusions.
This constructs the filtration and proves its bounds. Its graded-page
comparison is proved in ColumnConvergenceFiltration. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory CategoryTheory.Limits
variable {R : Type u} [CommRing R]
    (K : HomologicalComplex₂ (ModuleCat.{u} R) (ComplexShape.up ℕ) (ComplexShape.up ℕ))

def totalColumnHomologyFiltration (n k : ℕ) :
    Submodule R ((K.total (ComplexShape.up ℕ)).homology n) :=
  (totalColumnSubmodules K k).homologyImage n

theorem totalColumnHomologyFiltration_antitone (n : ℕ) :
    Antitone (totalColumnHomologyFiltration K n) := by
  intro k l h
  exact CochainSubmodules.homologyImage_mono _ (fun i => totalColumnFiltration_antitone K i h) n

theorem totalColumnHomologyFiltration_start (n : ℕ) :
    totalColumnHomologyFiltration K n 0 = ⊤ :=
  CochainSubmodules.homologyImage_top _ (totalColumnFiltration_start K) n

theorem totalColumnHomologyFiltration_stop (n : ℕ) :
    totalColumnHomologyFiltration K n (n+1) = ⊥ :=
  CochainSubmodules.homologyImage_eq_bot _ n
    (HomologicalComplex.ExactAt.of_isZero
      (totalColumnFilteredComplex_term_zero K (n+1) n (Nat.lt_succ_self n))).isZero_homology

end Sharpness
