import Sharpness.NormalPAction

/-!
The injective delta map used in Lemma 3.1 and Lemma 3.3.
The hypotheses say literally that the automorphism fixes Z pointwise and
induces the identity modulo Z. The p-group conclusion is proved, not supplied
as a theorem-shaped input.
-/
set_option autoImplicit false
noncomputable section
universe u v
namespace Sharpness

theorem isPGroup_function (p : ℕ) [Fact p.Prime]
    (I : Type u) [Finite I] (Z : Type v) [Group Z] [Finite Z]
    (hZ : IsPGroup p Z) : IsPGroup p (I → Z) := by
  classical
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hZ
  apply IsPGroup.of_card (n := n * Nat.card I)
  calc
    Nat.card (I → Z) = Nat.card Z ^ Nat.card I := by
      letI := Fintype.ofFinite I
      letI := Fintype.ofFinite Z
      letI : Fintype (I → Z) := inferInstance
      rw [Nat.card_eq_fintype_card (α := I → Z), Fintype.card_fun,
        Nat.card_eq_fintype_card (α := Z), Nat.card_eq_fintype_card (α := I)]
    _ = (p ^ n) ^ Nat.card I := by rw [hn]
    _ = p ^ (n * Nat.card I) := (pow_mul p n (Nat.card I)).symm

section Delta
variable {P : Type u} [Group P] {A : Type v} [Group A]
    (action : A →* MulAut P) (K : Subgroup A) (Z : Subgroup P)
    (fixZ : ∀ a : K, ∀ z : Z, action a.val z.val = z.val)
    (modZ : ∀ a : K, ∀ x : P, x⁻¹ * action a.val x ∈ Z)

def deltaHom : K →* (P → Z) where
  toFun a x := ⟨x⁻¹ * action a.val x, modZ a x⟩
  map_one' := by
    funext x
    apply Subtype.ext
    simp
  map_mul' a b := by
    funext x
    apply Subtype.ext
    change x⁻¹ * action (a.val * b.val) x =
      (x⁻¹ * action a.val x) * (x⁻¹ * action b.val x)
    have hb : action b.val x = x * (x⁻¹ * action b.val x) := by simp
    have hf := fixZ a ⟨x⁻¹ * action b.val x, modZ b x⟩
    rw [action.map_mul]
    change x⁻¹ * action a.val (action b.val x) = _
    rw [hb, map_mul, hf]
    simp [mul_assoc]

theorem deltaHom_injective (faithful : Function.Injective action) :
    Function.Injective (deltaHom action K Z fixZ modZ) := by
  intro a b hab
  apply Subtype.ext
  apply faithful
  apply MulEquiv.ext
  intro x
  have h := congrArg Subtype.val (congrFun hab x)
  exact mul_left_cancel h

include fixZ modZ in
theorem subgroup_isPGroup_of_delta (p : ℕ) [Fact p.Prime] [Finite P]
    (hZ : IsPGroup p Z) (faithful : Function.Injective action) : IsPGroup p K := by
  exact (isPGroup_function p P Z hZ).of_injective
    (deltaHom action K Z fixZ modZ) (deltaHom_injective action K Z fixZ modZ faithful)

end Delta
end Sharpness
