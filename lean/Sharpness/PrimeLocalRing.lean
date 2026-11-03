import Sharpness.HigherLimits
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-! The actual coefficient ring Z_(p), as the localization of Z at the
kernel of Z -> F_p, and its canonical map to any field of characteristic p. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness

def characteristicPrime (p : ℕ) : Ideal ℤ := RingHom.ker (Int.castRingHom (ZMod p))

instance characteristicPrime_isPrime (p : ℕ) [Fact p.Prime] :
    (characteristicPrime p).IsPrime := RingHom.ker_isPrime _

theorem characteristicPrime_eq_span (p : ℕ) :
    characteristicPrime p = Ideal.span ({(p : ℤ)} : Set ℤ) := by
  ext z
  change (z : ZMod p) = 0 ↔ z ∈ Ideal.span ({(p : ℤ)} : Set ℤ)
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd, Ideal.mem_span_singleton]

abbrev IntPrimeLocal (p : ℕ) [Fact p.Prime] := Localization.AtPrime (characteristicPrime p)

def intPrimeLocalToField (p : ℕ) [Fact p.Prime]
    (k : Type u) [Field k] [CharP k p] : IntPrimeLocal p →+* k := by
  letI : Algebra (ZMod p) k := ZMod.algebra k p
  apply IsLocalization.lift (M := (characteristicPrime p).primeCompl)
    (g := Int.castRingHom k)
  intro y
  apply isUnit_iff_ne_zero.mpr
  intro hz
  have hy : (y.val : ZMod p) ≠ 0 := y.property
  apply hy
  apply (algebraMap (ZMod p) k).injective
  change (y.val : k) = 0 at hz
  simpa only [map_intCast, map_zero] using hz

/-- Universe lift only; the underlying ring is precisely Z_(p). -/
abbrev PrimeLocalRing (p : ℕ) [Fact p.Prime] := ULift.{u} (IntPrimeLocal p)

def primeLocalToField (p : ℕ) [Fact p.Prime]
    (k : Type u) [Field k] [CharP k p] : PrimeLocalRing.{u} p →+* k :=
  (intPrimeLocalToField p k).comp ULift.ringEquiv.toRingHom

instance primeLocalAlgebra (p : ℕ) [Fact p.Prime]
    (k : Type u) [Field k] [CharP k p] : Algebra (PrimeLocalRing.{u} p) k :=
  (primeLocalToField p k).toAlgebra

end Sharpness
