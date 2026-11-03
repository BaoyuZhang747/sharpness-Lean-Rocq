import Sharpness.QuotientMackeyLimits
import Sharpness.HigherLimitsEquivalence
import Sharpness.CollectionRestrictionField
import Sharpness.ArbitraryCoefficients
import Sharpness.ZeroCoefficients

/-! Manuscript Proposition 3.4 on the actual saturated fusion systems:
sharpness for F/Z implies sharpness for F. The simple quotient, category
comparison, scalar passage, and simple-to-arbitrary reduction are proved
in this project; only the precisely stated general reference inputs remain. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem
open CategoryTheory CategoryTheory.Limits
variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)
    {Z : Subgroup S} [Z.Normal] (hZ : F.CentralSubgroup Z)
    (p : ℕ) [Fact p.Prime] (hS : IsPGroup p S) (sat : F.Saturated p)
    (I : F.AKOQuotientInput (p := p) hZ hS sat)
    {k : Type u} [Field k] [CharP k p]
    [EnoughProjectives (CoefficientCategory k F.CentricOrbit)]
    [EnoughProjectives (CoefficientCategory k I.system.CentricOrbit)]
    [EnoughProjectives (CoefficientCategory k (F.QuotientCentricLiftOrbit hZ p hS sat I))]
    [EnoughProjectives (CoefficientCategory k (F.quotientComparisonCollection p hS sat hZ I).Orbit)]
    [EnoughProjectives (CoefficientCategory (PrimeLocalRing.{u} p) F.CentricOrbit)]
    [EnoughProjectives (CoefficientCategory (PrimeLocalRing.{u} p)
      (F.quotientComparisonCollection p hS sat hZ I).Orbit)]
    (Y : F.YalcinRestrictionInput p hS sat)
    (BR : FiniteBarModel (PrimeLocalRing.{u} p) F.CentricOrbit) (cmpR : BR.Comparison)
    (BK : FiniteBarModel k F.CentricOrbit) (cmpK : BK.Comparison)
    (scalar : ScalarBarComparison BR BK)
    (BRX : FiniteBarModel (PrimeLocalRing.{u} p)
      (F.quotientComparisonCollection p hS sat hZ I).Orbit) (cmpRX : BRX.Comparison)
    (BKX : FiniteBarModel k (F.quotientComparisonCollection p hS sat hZ I).Orbit) (cmpKX : BKX.Comparison)
    (scalarX : ScalarBarComparison BRX BKX)

include Y cmpR cmpK scalar cmpRX cmpKX scalarX

theorem simple_central_acyclic_of_quotient_sharp
    (M : MackeyModule.{u,u,u} k F.Orbit F.mackeyShape) (label : F.SimpleLabel M)
    (hZQ : Z ≤ label.Q.as.subgroup) (sharp : I.system.Sharp (R := k)) :
    Acyclic (F.centricCoefficient M) := by
  let X := F.quotientComparisonCollection p hS sat hZ I
  let D := X.toCentric.op ⋙ F.centricCoefficient M
  let N := F.quotientMackey hZ p hS sat I M label hZQ
  let eq := (F.quotientCentricFunctor hZ p hS sat I).asEquivalence
  let ex := (F.quotientLiftToCollection hZ p hS sat I).asEquivalence
  have hN : Acyclic (I.system.centricCoefficient N) := sharp N
  have hq := acyclic_equivalence_pullback_of k eq (I.system.centricCoefficient N) hN
  have hl : Acyclic ((F.quotientLiftToCollection hZ p hS sat I).op ⋙ D) :=
    acyclic_of_iso (F.quotientMackeyLiftCentricCoefficientIso hZ p hS sat I M label hZQ).symm hq
  have hX : Acyclic D := acyclic_of_equivalence_pullback k ex D hl
  exact F.acyclic_of_collection_restriction p hS sat Y X BR cmpR BK cmpK scalar
    BRX cmpRX BKX cmpKX scalarX (F.centricCoefficient M) hX

theorem central_quotient_sharpness (classification : F.DiazParkInputs (k := k))
    (trace : F.DiazParkTraceInput (k := k)) (sharp : I.system.Sharp (R := k)) : F.Sharp (R := k) := by
  apply F.arbitrary_acyclic_of_simple BK cmpK
  intro M simple
  obtain ⟨label⟩ := classification.propositions_3_1_3_2 M simple
  by_cases hZQ : Z ≤ label.Q.as.subgroup
  · exact F.simple_central_acyclic_of_quotient_sharp hZ p hS sat I Y BR cmpR BK cmpK scalar
      BRX cmpRX BKX cmpKX scalarX M label hZQ sharp
  · apply BK.acyclic_of_values_zero (F.centricCoefficient M) cmpK
    intro P x
    exact F.simple_zero_on_centric_of_central_missing M label trace p hS hZ hZQ
      P.unop.obj.as.subgroup P.unop.property x

end Sharpness.FusionSystem
