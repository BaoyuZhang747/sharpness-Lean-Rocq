import Sharpness.PrimeLocalRing
import Mathlib.RingTheory.Localization.Submodule

/-! Noetherian and Jacobson-radical facts for the actual localized
integer ring, not a ring postulated to have the needed properties. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
variable (p : ℕ) [Fact p.Prime]

instance primeLocal_noetherian : IsNoetherianRing (PrimeLocalRing.{u} p) :=
  isNoetherianRing_of_ringEquiv (IntPrimeLocal p) ULift.ringEquiv.symm

instance primeLocal_isLocalRing : IsLocalRing (PrimeLocalRing.{u} p) :=
  IsLocalRing.of_surjective'
    (ULift.ringEquiv : PrimeLocalRing.{u} p ≃+* IntPrimeLocal p).symm.toRingHom
    (ULift.ringEquiv : PrimeLocalRing.{u} p ≃+* IntPrimeLocal p).symm.surjective

theorem primeLocal_prime_mem_jacobson :
    (p : PrimeLocalRing.{u} p) ∈ Ideal.jacobson (⊥ : Ideal (PrimeLocalRing.{u} p)) := by
  rw [IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top, IsLocalRing.mem_maximalIdeal]
  intro unit
  have h := unit.map (primeLocalToField p (ULift.{u} (ZMod p)))
  have zero : primeLocalToField p (ULift.{u} (ZMod p)) (p : PrimeLocalRing.{u} p) = 0 := by
    rw [map_natCast, CharP.cast_eq_zero]
  rw [zero] at h
  exact not_isUnit_zero h

end Sharpness
