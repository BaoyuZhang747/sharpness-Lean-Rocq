import Sharpness.CentralSharpness
import Sharpness.Unconditional.CollectionRestrictionFusion
import Sharpness.Unconditional.BarCalculation
import Sharpness.Unconditional.SimpleMackey
import Sharpness.Unconditional.TraceFormulaInput
import Sharpness.FullSubcategoryFinite

/-! Central-quotient sharpness using atomic vanishing and the constructed
finite bar resolution. The only comparison needed here is preservation of
acyclicity for the actual quotient collection. -/
set_option autoImplicit false
noncomputable section
universe u

namespace Sharpness.FusionSystem
open CategoryTheory CategoryTheory.Limits Opposite

variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)
    {Z : Subgroup S} [Z.Normal] (hZ : F.CentralSubgroup Z)
    (p : ℕ) [Fact p.Prime] (hS : IsPGroup p S) (sat : F.Saturated p)
    (I : F.AKOQuotientInput (p := p) hZ hS sat)
    {k : Type u} [Field k] [CharP k p]
    (atomic : ∀ Q : F.CentricOrbit, ¬ F.IsRadical p Q.obj.as.subgroup →
      ∀ A : CoefficientCategory k F.CentricOrbit,
      (∀ P, ¬ Nonempty (P ≅ Q) → IsZero (A.obj (op P))) →
      ∀ n, IsZero (higherLimit A n))

include atomic

theorem simple_central_acyclic_of_quotient_sharp_atomic
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
  exact (F.quotientCollectionRestriction_acyclic_iff p k hS sat hZ I atomic
    (F.centricCoefficient M)).mpr hX

theorem central_quotient_sharpness_of_atomic
    (sharp : I.system.Sharp (R := k)) : F.Sharp (R := k) := by
  let B := Unconditional.barCalculationInput p k
  apply F.arbitrary_acyclic_of_simple (B.model k F.CentricOrbit)
    (B.comparison k F.CentricOrbit)
  intro M simple
  let label := F.simpleLabel M simple
  by_cases hZQ : Z ≤ label.Q.as.subgroup
  · exact F.simple_central_acyclic_of_quotient_sharp_atomic hZ p hS sat I atomic
      M label hZQ sharp
  · apply (B.model k F.CentricOrbit).acyclic_of_values_zero
      (F.centricCoefficient M) (B.comparison k F.CentricOrbit)
    intro P x
    exact F.simple_zero_on_centric_of_central_missing M label F.diazParkTraceInput p hS
      hZ hZQ P.unop.obj.as.subgroup P.unop.property x

end Sharpness.FusionSystem
