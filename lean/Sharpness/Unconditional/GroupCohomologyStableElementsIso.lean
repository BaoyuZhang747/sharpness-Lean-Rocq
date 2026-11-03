import Sharpness.Unconditional.GroupCohomologyStableElements

/-! The stable-elements theorem, with explicit inverse given by normalized
native transfer. The subgroup need only have invertible index. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness.OrdinaryCohomology
open CategoryTheory
variable {R G A : Type u} [CommRing R] [Group G] [Finite G]
  [AddCommGroup A] [Module R A]

def restrictionStableElementsEquiv (S : Subgroup G) (n : ℕ)
    (hindex : IsUnit (S.index : R)) :
    value R G A n ≃ₗ[R] stableElements (R := R) (A := A) S n where
  toLinearMap := restrictionToStableElements S n
  invFun x := (↑hindex.unit⁻¹ : R) • transfer S n x.1
  left_inv x := by
    change (↑hindex.unit⁻¹ : R) • transfer S n (pull S.subtype n x) = x
    have h := congrArg (fun f => f.hom x) (pull_transfer (R := R) (A := A) S n)
    change transfer S n (pull S.subtype n x) = S.index • x at h
    have hu : (↑hindex.unit⁻¹ : R) * (S.index : R) = 1 := hindex.val_inv_mul
    rw [h, ← Nat.cast_smul_eq_nsmul R, smul_smul, hu, one_smul]
  right_inv x := by
    apply Subtype.ext
    change pull S.subtype n ((↑hindex.unit⁻¹ : R) • transfer S n x.1) = x.1
    have hu : (↑hindex.unit⁻¹ : R) * (S.index : R) = 1 := hindex.val_inv_mul
    rw [map_smul, transfer_restrict_stable S n x,
      ← Nat.cast_smul_eq_nsmul R, smul_smul, hu, one_smul]

@[simp] theorem restrictionStableElementsEquiv_apply (S : Subgroup G) (n : ℕ)
    (hindex : IsUnit (S.index : R)) (x : value R G A n) :
    (restrictionStableElementsEquiv S n hindex x).1 = pull S.subtype n x := rfl

@[simp] theorem restrictionStableElementsEquiv_symm_apply (S : Subgroup G) (n : ℕ)
    (hindex : IsUnit (S.index : R)) (x : stableElements (R := R) (A := A) S n) :
    (restrictionStableElementsEquiv S n hindex).symm x =
      (↑hindex.unit⁻¹ : R) • transfer S n x.1 := rfl

theorem restriction_injective_of_index_isUnit (S : Subgroup G) (n : ℕ)
    (hindex : IsUnit (S.index : R)) :
    Function.Injective (pull (R := R) (A := A) S.subtype n) := by
  intro x y h
  apply (restrictionStableElementsEquiv (A := A) S n hindex).injective
  exact Subtype.ext h

theorem mem_stableElements_iff_exists_restriction (S : Subgroup G) (n : ℕ)
    (hindex : IsUnit (S.index : R)) (x : value R S A n) :
    x ∈ stableElements (R := R) (A := A) S n ↔
      ∃ y : value R G A n, pull S.subtype n y = x := by
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := (restrictionStableElementsEquiv (A := A) S n hindex).surjective ⟨x, hx⟩
    exact ⟨y, congrArg Subtype.val hy⟩
  · rintro ⟨y, rfl⟩
    exact restriction_mem_stableElements S n y

end Sharpness.OrdinaryCohomology
