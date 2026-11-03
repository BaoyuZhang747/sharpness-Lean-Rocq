import Sharpness.V29.Main
import Sharpness.Unconditional.InclusionMackeyBridge

/-! The main endpoints for two functors on the whole orbit category satisfying
the isomorphism law and the inclusion-only double-coset identity. -/
set_option autoImplicit false
noncomputable section
universe u

namespace Sharpness.FusionSystem.V29

/-- Localized-integer sharpness from inclusion-form Mackey data. The bridge
keeps exactly the given values, restrictions and transfers. -/
theorem inclusion_primeLocal_acyclic (p : ℕ) [Fact p.Prime]
    {S : Type u} [Group S] [Finite S] (F : FusionSystem S)
    (hS : IsPGroup p S) (sat : F.Saturated p)
    (E : MackeyFunctorData.{u,u} (PrimeLocalRing.{u} p) F.Orbit)
    (identity : F.HasInclusionMackeyFormula E) :
    Acyclic (F.centricCoefficient (F.fullMackeyOfInclusionIdentity E identity)) :=
  primeLocal_sharpness p F hS sat (F.fullMackeyOfInclusionIdentity E identity)

/-- Arbitrary-valued characteristic-p field sharpness from inclusion-form data. -/
theorem inclusion_field_acyclic (p : ℕ) [Fact p.Prime]
    (k : Type u) [Field k] [CharP k p]
    {S : Type u} [Group S] [Finite S] (F : FusionSystem S)
    (hS : IsPGroup p S) (sat : F.Saturated p)
    (E : MackeyFunctorData.{u,u} k F.Orbit)
    (identity : F.HasInclusionMackeyFormula E) :
    Acyclic (F.centricCoefficient (F.fullMackeyOfInclusionIdentity E identity)) :=
  field_sharpness_of_primeLocal p k F hS sat (F.fullMackeyOfInclusionIdentity E identity)

/-- The finite-dimensional conjecture for the inclusion-only axiom list. -/
theorem inclusion_diaz_park_conjecture (p : ℕ) [Fact p.Prime]
    {S : Type u} [Group S] [Finite S] (F : FusionSystem S)
    (hS : IsPGroup p S) (sat : F.Saturated p)
    (E : MackeyFunctorData.{u,u} (PrimeField.{u} p) F.Orbit)
    (identity : F.HasInclusionMackeyFormula E)
    [∀ P, FiniteDimensional (PrimeField.{u} p) (E.Value P)] :
    Acyclic (F.centricCoefficient (F.fullMackeyOfInclusionIdentity E identity)) := by
  let M := F.fullMackeyOfInclusionIdentity E identity
  letI : ∀ P, FiniteDimensional (PrimeField.{u} p) (M.Value P) :=
    fun P => inferInstanceAs (FiniteDimensional (PrimeField.{u} p) (E.Value P))
  exact diaz_park_conjecture p F hS sat M

end Sharpness.FusionSystem.V29
