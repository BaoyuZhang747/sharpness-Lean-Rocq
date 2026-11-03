import Mathlib

/-!
The normal-p-subgroup action argument in manuscript Lemma 3.3, Step 2.
For an arbitrary field of characteristic p we use the finite prime-field
span of one orbit. No finiteness assumption on the coefficient field, or
on the entire module, is needed.
-/
set_option autoImplicit false
noncomputable section
universe u v
namespace Sharpness

theorem pgroup_has_nonzero_fixed_vector (p : ℕ) [Fact p.Prime]
    {G : Type u} [Group G] [Finite G] (hG : IsPGroup p G)
    {V : Type v} [AddCommGroup V] [Module (ZMod p) V]
    (ρ : G →* Module.End (ZMod p) V) (v : V) (hv : v ≠ 0) :
    ∃ w : V, w ≠ 0 ∧ ∀ g : G, ρ g w = w := by
  classical
  let W : Submodule (ZMod p) V := Submodule.span (ZMod p) (Set.range fun g : G => ρ g v)
  have fg : W.FG := Submodule.fg_span (Set.finite_range _)
  letI : Module.Finite (ZMod p) W := Module.Finite.of_fg fg
  letI : Finite W := Module.finite_of_finite (ZMod p)
  letI : Fintype W := Fintype.ofFinite W
  have stable (g : G) : W ≤ W.comap (ρ g) := by
    apply Submodule.span_le.mpr
    intro x hx
    obtain ⟨a, rfl⟩ := hx
    change ρ g (ρ a v) ∈ W
    have he : ρ g (ρ a v) = ρ (g * a) v := by
      rw [map_mul]
      rfl
    rw [he]
    exact Submodule.subset_span ⟨g * a, rfl⟩
  letI : MulAction G W :=
    { smul := fun g x => ⟨ρ g x.val, stable g x.property⟩
      one_smul := by
        intro x
        apply Subtype.ext
        change ρ 1 x.val = x.val
        rw [map_one]
        rfl
      mul_smul := by
        intro g h x
        apply Subtype.ext
        change ρ (g * h) x.val = ρ g (ρ h x.val)
        rw [map_mul]
        rfl }
  have hvW : v ∈ W := by
    apply Submodule.subset_span
    refine ⟨1, ?_⟩
    change ρ 1 v = v
    rw [map_one]
    rfl
  have hdim : 0 < Module.finrank (ZMod p) W := by
    apply Module.finrank_pos_iff_exists_ne_zero.mpr
    refine ⟨⟨v, hvW⟩, ?_⟩
    intro h
    exact hv (congrArg Subtype.val h)
  have hcard : Nat.card W = p ^ Module.finrank (ZMod p) W := by
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod p), ZMod.card]
  have hpW : p ∣ Nat.card W := by
    rw [hcard]
    exact dvd_pow_self p (Nat.ne_of_gt hdim)
  have hzero : (0 : W) ∈ MulAction.fixedPoints G W := by
    intro g
    apply Subtype.ext
    exact map_zero (ρ g)
  obtain ⟨w, hw, hne⟩ :=
    hG.exists_fixed_point_of_prime_dvd_card_of_fixed_point W hpW hzero
  refine ⟨w.val, ?_, ?_⟩
  · intro hz
    exact hne (Subtype.ext hz.symm)
  · intro g
    exact congrArg Subtype.val (hw g)

def fixedSubmodule {k : Type u} [Field k] {G : Type u} [Group G]
    {V : Type v} [AddCommGroup V] [Module k V]
    (ρ : G →* Module.End k V) (N : Subgroup G) : Submodule k V where
  carrier := {v | ∀ n : N, ρ n.val v = v}
  zero_mem' := fun n => map_zero (ρ n.val)
  add_mem' := by intro x y hx hy n; rw [map_add, hx n, hy n]
  smul_mem' := by intro a x hx n; rw [map_smul, hx n]

theorem normal_p_subgroup_acts_trivially (p : ℕ) [Fact p.Prime]
    {k : Type u} [Field k] [CharP k p]
    {G : Type u} [Group G] [Finite G]
    {V : Type v} [AddCommGroup V] [Module k V]
    (ρ : G →* Module.End k V) (N : Subgroup G) [N.Normal]
    (hN : IsPGroup p N) (v : V) (hv : v ≠ 0)
    (simple : ∀ A : Submodule k V,
      (∀ g : G, ∀ x ∈ A, ρ g x ∈ A) → A = ⊥ ∨ A = ⊤) :
    ∀ n : N, ∀ x : V, ρ n.val x = x := by
  letI : Algebra (ZMod p) k := ZMod.algebra k p
  letI : Module (ZMod p) V := Module.restrictScalars (ZMod p) k V
  letI : IsScalarTower (ZMod p) k V := IsScalarTower.restrictScalars (ZMod p) k V
  let ρN : N →* Module.End (ZMod p) V :=
    { toFun := fun n => (ρ n.val).restrictScalars (ZMod p)
      map_one' := by ext x; change ρ 1 x = x; rw [map_one]; rfl
      map_mul' := by intro n m; ext x; change ρ (n.val * m.val) x = ρ n.val (ρ m.val x); rw [map_mul]; rfl }
  obtain ⟨w, hw, hwfix⟩ := pgroup_has_nonzero_fixed_vector p hN ρN v hv
  let A := fixedSubmodule ρ N
  have wA : w ∈ A := hwfix
  have invariant : ∀ g : G, ∀ x ∈ A, ρ g x ∈ A := by
    intro g x hx n
    have hn : g⁻¹ * n.val * g ∈ N := by
      simpa using (inferInstance : N.Normal).conj_mem n.val n.property g⁻¹
    have hfix := hx ⟨g⁻¹ * n.val * g, hn⟩
    calc
      ρ n.val (ρ g x) = ρ (n.val * g) x := by rw [map_mul]; rfl
      _ = ρ g (ρ (g⁻¹ * n.val * g) x) := by
        rw [← Module.End.mul_apply, ← map_mul]
        simp only [mul_assoc, mul_inv_cancel_left]
      _ = ρ g x := by rw [hfix]
  rcases simple A invariant with hbot | htop
  · have : w = 0 := by simpa [hbot] using wA
    exact (hw this).elim
  · intro n x
    have hx : x ∈ A := by simp [htop]
    exact hx n

end Sharpness
