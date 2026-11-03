import Sharpness.Unconditional.AtomicSylowOrbit
import Mathlib.GroupTheory.GroupAction.Basic

/-! Orbit-category morphisms into a point stabilizer represent the fixed
points in that orbit. This is the uniqueness statement for terminal
objects in the atomic-comparison comma components. -/
set_option autoImplicit false
noncomputable section
universe u v

namespace Sharpness.AtomicGroupOrbit
open CategoryTheory
variable {p : ℕ} {G : Type u} [Group G] {X : Type v} [MulAction G X]

def stabilizerObject (x : X) (hx : IsPGroup p (MulAction.stabilizer G x)) : Object p G :=
  ⟨MulAction.stabilizer G x, hx⟩

def FixedOrbit (H : Object p G) (x : X) :=
  {y : X // H.subgroup ≤ MulAction.stabilizer G y ∧ y ∈ MulAction.orbit G x}

theorem transporter_smul_fixed (H : Object p G) (x : X)
    (hx : IsPGroup p (MulAction.stabilizer G x))
    (g : H ⟶ stabilizerObject x hx) :
    H.subgroup ≤ MulAction.stabilizer G (g.val • x) := by
  intro h hh
  have hg := g.property h hh
  change (g.val⁻¹ * h * g.val) • x = x at hg
  change h • (g.val • x) = g.val • x
  have he := congrArg (fun y => g.val • y) hg
  simpa only [← mul_smul, mul_assoc, mul_inv_cancel_left] using he

def rawFixedOrbit (H : Object p G) (x : X)
    (hx : IsPGroup p (MulAction.stabilizer G x))
    (g : H ⟶ stabilizerObject x hx) : FixedOrbit H x :=
  ⟨g.val • x, transporter_smul_fixed H x hx g, ⟨g.val, rfl⟩⟩

def orbitHomToFixedOrbit (H : Object p G) (x : X)
    (hx : IsPGroup p (MulAction.stabilizer G x)) :
    (toOrbit.obj H ⟶ toOrbit.obj (stabilizerObject x hx)) → FixedOrbit H x :=
  Quot.lift (rawFixedOrbit H x hx) (by
    intro f g hfg
    obtain ⟨k, hk⟩ := (HomRel.compClosure_iff_self _ _ _).mp hfg
    apply Subtype.ext
    change f.val • x = g.val • x
    rw [hk, mul_smul]
    exact (congrArg (fun y => f.val • y) k.property).symm)

@[simp]
theorem orbitHomToFixedOrbit_map (H : Object p G) (x : X)
    (hx : IsPGroup p (MulAction.stabilizer G x))
    (g : H ⟶ stabilizerObject x hx) :
    orbitHomToFixedOrbit H x hx (toOrbit.map g) = rawFixedOrbit H x hx g := rfl

theorem orbitHomToFixedOrbit_injective (H : Object p G) (x : X)
    (hx : IsPGroup p (MulAction.stabilizer G x)) :
    Function.Injective (orbitHomToFixedOrbit H x hx) := by
  intro f g hfg
  obtain ⟨a, rfl⟩ := toOrbit.map_surjective f
  obtain ⟨b, rfl⟩ := toOrbit.map_surjective g
  have hab : a.val • x = b.val • x := congrArg Subtype.val hfg
  apply (orbit_map_eq_iff a b).mpr
  have hk : a.val⁻¹ * b.val ∈ MulAction.stabilizer G x := by
    change (a.val⁻¹ * b.val) • x = x
    rw [mul_smul, ← hab, inv_smul_smul]
  exact ⟨⟨a.val⁻¹ * b.val, hk⟩, by simp⟩

theorem orbitHomToFixedOrbit_surjective (H : Object p G) (x : X)
    (hx : IsPGroup p (MulAction.stabilizer G x)) :
    Function.Surjective (orbitHomToFixedOrbit H x hx) := by
  rintro ⟨y, hfix, g, rfl⟩
  have hg : ∀ h ∈ H.subgroup, g⁻¹ * h * g ∈ MulAction.stabilizer G x := by
    intro h hh
    have he := hfix hh
    change h • (g • x) = g • x at he
    change (g⁻¹ * h * g) • x = x
    rw [mul_smul, mul_smul, he, inv_smul_smul]
  exact ⟨toOrbit.map ⟨g, hg⟩, rfl⟩

/-- The coset of a transporter is uniquely determined by its action on
the point whose stabilizer is the target. -/
def orbitHomToStabilizerEquiv (H : Object p G) (x : X)
    (hx : IsPGroup p (MulAction.stabilizer G x)) :
    (toOrbit.obj H ⟶ toOrbit.obj (stabilizerObject x hx)) ≃ FixedOrbit H x :=
  Equiv.ofBijective (orbitHomToFixedOrbit H x hx)
    ⟨orbitHomToFixedOrbit_injective H x hx, orbitHomToFixedOrbit_surjective H x hx⟩

@[simp]
theorem orbitHomToStabilizerEquiv_map (H : Object p G) (x : X)
    (hx : IsPGroup p (MulAction.stabilizer G x))
    (g : H ⟶ stabilizerObject x hx) :
    (orbitHomToStabilizerEquiv H x hx (toOrbit.map g)).val = g.val • x := rfl

/-- The same fixed-point equivalence for a target whose subgroup is only
propositionally identified with the stabilizer. -/
def orbitHomToStabilizerEquivOfEq (H K : Object p G) (x : X)
    (hK : K.subgroup = MulAction.stabilizer G x) :
    (toOrbit.obj H ⟶ toOrbit.obj K) ≃ FixedOrbit H x := by
  rcases K with ⟨K, hp⟩
  dsimp at hK
  subst K
  exact orbitHomToStabilizerEquiv H x hp

@[simp]
theorem orbitHomToStabilizerEquivOfEq_map (H K : Object p G) (x : X)
    (hK : K.subgroup = MulAction.stabilizer G x) (g : H ⟶ K) :
    (orbitHomToStabilizerEquivOfEq H K x hK (toOrbit.map g)).val = g.val • x := by
  rcases K with ⟨K, hp⟩
  dsimp at hK
  subst K
  rfl

end Sharpness.AtomicGroupOrbit
