import Sharpness.Unconditional.MainTheorem
import Sharpness.Unconditional.BarCalculation
import Sharpness.PrimeFieldMackey
import Sharpness.LocalReduction

/-! The manuscript's local-coefficient corollary for the actual ring Z_(p).
The characteristic-p field theorem, projective bar calculation, and scalar
comparison are all constructed in Lean. The coefficient modules need not
be finitely generated. -/

set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem
open CategoryTheory

variable (p : ℕ) [Fact p.Prime]
    {S : Type u} [Group S] [Finite S] (F : FusionSystem S)
    (hS : IsPGroup p S) (sat : F.Saturated p)

include hS sat

/-- A full Mackey module over Z_(p) annihilated by p is acyclic, by the
unconditional theorem over the prime field and the proved scalar comparison. -/
theorem prime_annihilated_mackey_acyclic_unconditional
    (M : MackeyModule.{u,u,u} (PrimeLocalRing.{u} p) F.Orbit F.mackeyShape)
    (killed : ∀ P (x : M.Value P), (p : PrimeLocalRing.{u} p) • x = 0) :
    Acyclic (F.centricCoefficient M) := by
  let B := Unconditional.barCalculationInput p (PrimeField.{u} p)
  let N := M.primeFieldMackey p killed
  have fieldVanishing : Acyclic (F.centricCoefficient N) :=
    F.saturated_fusion_sharpness_unconditional p (PrimeField.{u} p) hS sat N
  have restricted := (B.scalar F.CentricOrbit).acyclic_restrict_of
    (F.centricCoefficient N)
    (B.comparison (PrimeLocalRing.{u} p) F.CentricOrbit)
    (B.comparison (PrimeField.{u} p) F.CentricOrbit) fieldVanishing
  have hn : Acyclic (F.centricCoefficient (N.restrictScalars (PrimeLocalRing.{u} p))) :=
    acyclic_of_iso (F.centricRestrictScalarsIso N) restricted
  exact acyclic_of_iso (F.centricCoefficientIso (M.primeFieldMackeyRestrictIso p killed)) hn

/-- The unconditional local-coefficient corollary for all full Mackey modules,
including non-finitely-generated localized-integer values. -/
theorem saturated_fusion_sharpness_primeLocal_unconditional :
    F.Sharp (R := PrimeLocalRing.{u} p) := by
  intro M
  let B := Unconditional.barCalculationInput p (PrimeField.{u} p)
  let bar := B.model (PrimeLocalRing.{u} p) F.CentricOrbit
  apply (bar.acyclic_iff (B.comparison (PrimeLocalRing.{u} p) F.CentricOrbit) _).mpr
  apply F.arbitrary_local_exact_of_killed_exact bar (p : PrimeLocalRing.{u} p)
    (fun N killed => (bar.acyclic_iff
      (B.comparison (PrimeLocalRing.{u} p) F.CentricOrbit) _).mp
      (F.prime_annihilated_mackey_acyclic_unconditional p hS sat N killed))
    (primeLocal_prime_mem_jacobson p) M

end Sharpness.FusionSystem
