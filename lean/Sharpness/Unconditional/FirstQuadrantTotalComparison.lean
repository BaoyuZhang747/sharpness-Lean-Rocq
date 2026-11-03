import Sharpness.Unconditional.FirstQuadrantTotalComparisonConeIso
import Sharpness.Unconditional.ChainHomotopyCofiberQuasiIso
import Sharpness.Unconditional.BisimplicialAlexanderWhitneyNaturality

/-! Elementary comparison for the actual nonnegative total complex.
The proof uses finite-diagonal boundary elimination and native mapping cofibers. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness.TotalComparison
open CategoryTheory HomologicalComplex Simplicial Opposite
variable {R : Type u} [CommRing R]

/-- Columnwise quasi-isomorphisms induce a quasi-isomorphism on the actual signed total. -/
theorem totalMap_quasiIso_of_columns
    {K L : HomologicalComplex₂ (ModuleCat.{u} R) (ComplexShape.down ℕ) (ComplexShape.down ℕ)}
    (φ : K ⟶ L) (hφ : ∀ p, QuasiIso (φ.f p)) :
    QuasiIso (HomologicalComplex₂.total.map φ (ComplexShape.down ℕ)) := by
  have hc : ∀ p, ((columnCofiber φ).X p).Acyclic := by
    intro p
    letI := hφ p
    exact ChainCofiber.cofiber_acyclic_of_quasiIso (φ.f p)
  have ht := total_acyclic_of_columns (columnCofiber φ) hc
  letI := columnCofiberTotalComparison_isIso φ
  apply ChainCofiber.quasiIso_of_cofiber_acyclic
  intro n
  exact (ht n).of_iso (asIso (columnCofiberTotalComparison φ)).symm

theorem bisimplicialTotalChainsMap_quasiIso_of_columns
    {X Y : SimplicialObject SSet.{u}} (φ : X ⟶ Y)
    (hφ : ∀ p : ℕ, QuasiIso ((simplicialChainsFunctor R).map (φ.app (op ⦋p⦌)))) :
    QuasiIso (bisimplicialTotalChainsMap φ R) := by
  apply totalMap_quasiIso_of_columns
  intro p
  exact hφ p

end Sharpness.TotalComparison
