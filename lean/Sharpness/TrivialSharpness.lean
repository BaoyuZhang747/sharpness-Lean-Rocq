import Sharpness.CentricSimple
import Sharpness.ArbitraryCoefficients

/-! The actual trivial-group base case, using the centric supported
result and the proved arbitrary-value reduction. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem
open CategoryTheory
variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)

theorem isCentric_of_subsingleton [Subsingleton S] (P : Subgroup S) : F.IsCentric P := by
  intro Q _ _ _ x _
  exact (Subsingleton.elim x 1) ▸ Q.one_mem

variable (p : ℕ) [Fact p.Prime] (hS : IsPGroup p S) (sat : F.Saturated p)
    {k : Type u} [Field k] [CharP k p]
    [EnoughProjectives (CoefficientCategory k F.CentricOrbit)]
    [EnoughProjectives (CoefficientCategory (PrimeLocalRing.{u} p) F.CentricOrbit)]
    (DP : F.DiazParkTheoremAInput p hS sat)
    (BR : FiniteBarModel (PrimeLocalRing.{u} p) F.CentricOrbit) (cmpR : BR.Comparison)
    (BK : FiniteBarModel k F.CentricOrbit) (cmpK : BK.Comparison)
    (scalar : ScalarBarComparison BR BK)

include DP cmpR cmpK scalar

theorem sharp_of_subsingleton [Subsingleton S] (classification : F.DiazParkInputs (k := k)) :
    F.Sharp (R := k) := by
  apply F.arbitrary_acyclic_of_simple BK cmpK
  intro M simple
  obtain ⟨label⟩ := classification.propositions_3_1_3_2 M simple
  exact F.centric_simple_acyclic_from_references p hS sat DP BR cmpR BK cmpK scalar
    classification M label (F.isCentric_of_subsingleton _)

end Sharpness.FusionSystem
