import Sharpness.CollectionRestriction
import Sharpness.ScalarRestrictionAcyclic

/-! Applying the exact Z_(p)-coefficient Yalcin input to characteristic-p
field coefficients. Scalar comparison in both categories is used rather
than assuming the desired field-coefficient restriction assertion. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem
open CategoryTheory CategoryTheory.Limits
variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)
    (p : ℕ) [Fact p.Prime] (hS : IsPGroup p S) (sat : F.Saturated p)
    [EnoughProjectives (CoefficientCategory (PrimeLocalRing.{u} p) F.CentricOrbit)]
    (Y : F.YalcinRestrictionInput p hS sat)
    {k : Type u} [Field k] [CharP k p]
    [EnoughProjectives (CoefficientCategory k F.CentricOrbit)]
    (C : F.ComparisonCollection p)
    [EnoughProjectives (CoefficientCategory (PrimeLocalRing.{u} p) C.Orbit)]
    [EnoughProjectives (CoefficientCategory k C.Orbit)]
    (BR : FiniteBarModel (PrimeLocalRing.{u} p) F.CentricOrbit) (cmpR : BR.Comparison)
    (BK : FiniteBarModel k F.CentricOrbit) (cmpK : BK.Comparison)
    (scalar : ScalarBarComparison BR BK)
    (BRC : FiniteBarModel (PrimeLocalRing.{u} p) C.Orbit) (cmpRC : BRC.Comparison)
    (BKC : FiniteBarModel k C.Orbit) (cmpKC : BKC.Comparison)
    (scalarC : ScalarBarComparison BRC BKC)

include Y cmpR cmpK scalar cmpRC cmpKC scalarC

theorem acyclic_of_collection_restriction (D : CoefficientCategory k F.CentricOrbit)
    (h : Acyclic (C.toCentric.op ⋙ D)) : Acyclic D := by
  have hR := scalarC.acyclic_restrict_of (C.toCentric.op ⋙ D) cmpRC cmpKC h
  have hRC : Acyclic (C.toCentric.op ⋙ restrictCoefficientScalars (R := PrimeLocalRing.{u} p) D) := hR
  have hRD : Acyclic (restrictCoefficientScalars (R := PrimeLocalRing.{u} p) D) := by
    intro i hi
    exact IsZero.of_iso (hRC i hi) (Y.proposition_10_5 C _ i).symm
  exact scalar.acyclic_of_restrict D cmpR cmpK hRD

theorem acyclic_collection_restriction_of (D : CoefficientCategory k F.CentricOrbit)
    (h : Acyclic D) : Acyclic (C.toCentric.op ⋙ D) := by
  have hRD := scalar.acyclic_restrict_of D cmpR cmpK h
  have hRC : Acyclic (C.toCentric.op ⋙ restrictCoefficientScalars (R := PrimeLocalRing.{u} p) D) := by
    intro i hi
    exact IsZero.of_iso (hRD i hi) (Y.proposition_10_5 C _ i)
  exact scalarC.acyclic_of_restrict (C.toCentric.op ⋙ D) cmpRC cmpKC hRC

end Sharpness.FusionSystem
