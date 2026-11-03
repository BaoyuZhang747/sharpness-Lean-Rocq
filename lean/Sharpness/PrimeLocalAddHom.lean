import Sharpness.PrimeLocalRing

/-! Every additive map between actual Z_(p)-modules is Z_(p)-linear.
The proof clears an actual localization denominator and cancels its unit
action. No coefficient-naturality or linearity input is required. -/
set_option autoImplicit false
noncomputable section
universe u v w
namespace Sharpness
variable (p : ℕ) [Fact p.Prime]
    {A : Type v} {B : Type w} [AddCommGroup A] [AddCommGroup B]
    [Module (PrimeLocalRing.{u} p) A] [Module (PrimeLocalRing.{u} p) B]

theorem primeLocal_addHom_map_smul (f : A →+ B) (r : PrimeLocalRing.{u} p) (x : A) :
    f (r • x) = r • f x := by
  let R := PrimeLocalRing.{u} p
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
  have hint (z : ℤ) (y : A) : f ((z : R) • y) = (z : R) • f y := by
    change f ((z : PrimeLocalRing.{u} p) • y) = (z : PrimeLocalRing.{u} p) • f y
    rw [Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]
    exact f.map_zsmul z y
  obtain ⟨unit, hunit⟩ := hden
  apply (MulAction.injective unit)
  change (unit : R) • f (r • x) = (unit : R) • (r • f x)
  rw [hunit]
  calc
    (s.val : R) • f (r • x) = f ((s.val : R) • (r • x)) := (hint _ _).symm
    _ = f ((a : R) • x) := by rw [← mul_smul, mul_comm (s.val : R) r, hfrac]
    _ = (a : R) • f x := hint _ _
    _ = (s.val : R) • (r • f x) := by rw [← mul_smul, mul_comm (s.val : R) r, hfrac]

def primeLocalLinearOfAddHom (f : A →+ B) : A →ₗ[PrimeLocalRing.{u} p] B where
  toFun := f
  map_add' := f.map_add
  map_smul' := primeLocal_addHom_map_smul p f

theorem primeLocalLinearOfAddHom_apply (f : A →+ B) (x : A) :
    primeLocalLinearOfAddHom p f x = f x := rfl

end Sharpness
