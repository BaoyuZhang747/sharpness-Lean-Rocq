import Sharpness.ChainDualHomotopy
import Mathlib.Algebra.Homology.DerivedCategory.KProjective

/-! A quasi-isomorphism between actual nonnegative degreewise
projective chain complexes remains a quasi-isomorphism under the
actual Hom_R(-,A) map for arbitrary A. This uses a constructed chain
homotopy inverse; A need not be injective. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.SingularCohomology
open CategoryTheory HomologicalComplex
variable (R : Type u) [CommRing R] (A : ModuleCat.{u} R)
    {K L : ChainComplex (ModuleCat.{u} R) ℕ}
    [∀ n, Projective (K.X n)] [∀ n, Projective (L.X n)]

theorem chainDualMap_quasiIso_of_projective (f : K ⟶ L) [QuasiIso f] :
    QuasiIso (chainDualMap R f A) := by
  obtain ⟨e, he⟩ := (ChainComplex.quasiIso_iff_of_projective f).mp inferInstance
  rw [← he]
  exact inferInstanceAs (QuasiIso (chainDualHomotopyEquiv R A e).hom)

end Sharpness.SingularCohomology
