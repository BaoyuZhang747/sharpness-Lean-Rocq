import Sharpness.PrimeLocalAlgebra
import Mathlib.Algebra.Module.ZMod

/-! An actual prime-local module killed by p carries the canonical F_p
action. Its old localized-integer action agrees with scalar restriction;
this agreement is proved using localization denominators. -/
set_option autoImplicit false
noncomputable section
universe u v
namespace Sharpness
variable (p : ℕ) [Fact p.Prime]

abbrev PrimeField := ULift.{u} (ZMod p)

theorem primeLocal_field_smul {A : Type v} [AddCommGroup A]
    [Module (PrimeLocalRing.{u} p) A] [Module (PrimeField.{u} p) A]
    (r : PrimeLocalRing.{u} p) (x : A) :
    algebraMap (PrimeLocalRing.{u} p) (PrimeField.{u} p) r • x = r • x := by
  let R := PrimeLocalRing.{u} p
  let k := PrimeField.{u} p
  let e : IntPrimeLocal p →+* R :=
    (ULift.ringEquiv : R ≃+* IntPrimeLocal p).symm.toRingHom
  obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj (characteristicPrime p).primeCompl r.down
  have hfrac : r * (s.val : R) = (a : R) := by
    have hd : r.down * (s.val : IntPrimeLocal p) = (a : IntPrimeLocal p) := by
      simpa using hs
    exact congrArg (fun y : IntPrimeLocal p => (ULift.up y : R)) hd
  have hden : IsUnit (s.val : R) := by
    have h := (IsLocalization.map_units (S := IntPrimeLocal p) s).map e
    simpa [e] using h
  have hint (z : ℤ) (y : A) :
      algebraMap R k (z : R) • y = (z : R) • y := by
    rw [map_intCast, Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]
  obtain ⟨unit, hunit⟩ := hden.map (algebraMap R k)
  apply (MulAction.injective unit)
  change (unit : k) • (algebraMap R k r • x) = (unit : k) • (r • x)
  rw [hunit, ← mul_smul, ← map_mul, mul_comm (s.val : R) r, hfrac,
    hint a, hint s.val, ← mul_smul, mul_comm (s.val : R) r, hfrac]

end Sharpness
