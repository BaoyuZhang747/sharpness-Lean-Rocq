import Sharpness.Saturation
import Mathlib.GroupTheory.Sylow

/-! The actual fusion system induced by an ambient group on any subgroup.
Saturation is not built into this construction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
universe u
namespace Sharpness
variable {G : Type u} [Group G]

/-- One ambient group element induces the whole subgroup homomorphism.
The left-conjugation convention agrees with native normalizer actions. -/
def finiteGroupFusionIsHom (S : Subgroup G) {P Q : Subgroup S} (f : P →* Q) : Prop :=
  ∃ g : G, ∀ x : P, ((f x).val : G) = g * (x.val : G) * g⁻¹

def finiteGroupFusion (S : Subgroup G) : FusionSystem S where
  IsHom := finiteGroupFusionIsHom S
  injective f hf := by
    obtain ⟨g, hg⟩ := hf
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    have hc := congrArg (fun z => (z.val : G)) h
    rw [hg x, hg y] at hc
    exact (MulAut.conj g).injective hc
  id_mem P := by
    refine ⟨1, ?_⟩
    intro x
    simp
  comp_mem f h hf hh := by
    obtain ⟨a, ha⟩ := hf
    obtain ⟨b, hb⟩ := hh
    refine ⟨b*a, ?_⟩
    intro x
    change ((h (f x)).val : G) = _
    rw [hb, ha]
    group
  inclusion_mem h := by
    refine ⟨1, ?_⟩
    intro x
    simp [subgroupInclusion]
  conjugation_mem P Q s h := by
    refine ⟨(s : G)⁻¹, ?_⟩
    intro x
    simp only [subgroupConjugation, MonoidHom.coe_mk, OneHom.coe_mk,
      Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
  inverse_mem e he := by
    obtain ⟨g, hg⟩ := he
    refine ⟨g⁻¹, ?_⟩
    intro y
    have hc := hg (e.symm y)
    simp only [MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply] at hc
    have hi := congrArg (fun z : G => g⁻¹*z*g) hc
    simpa [mul_assoc] using hi.symm
  codomain_restrict_mem f hf hRQ h he := by
    obtain ⟨g, hg⟩ := hf
    refine ⟨g, ?_⟩
    intro x
    have hx := congrArg (fun a => ((a x).val : G)) he
    change ((h x).val : G) = ((f x).val : G) at hx
    exact hx.trans (hg x)

@[simp]
theorem finiteGroupFusion_isHom_iff (S : Subgroup G) {P Q : Subgroup S} (f : P →* Q) :
    (finiteGroupFusion S).IsHom f ↔
      ∃ g : G, ∀ x : P, ((f x).val : G) = g * (x.val : G) * g⁻¹ := Iff.rfl

/-- The ambient subgroup corresponding to an actual subgroup of S. -/
abbrev finiteGroupAmbientSubgroup (S : Subgroup G) (P : Subgroup S) : Subgroup G :=
  P.map S.subtype

def finiteGroupAmbientEquiv (S : Subgroup G) (P : Subgroup S) :
    P ≃* finiteGroupAmbientSubgroup S P :=
  P.equivMapOfInjective S.subtype Subtype.coe_injective

@[simp]
theorem finiteGroupAmbientEquiv_apply (S : Subgroup G) (P : Subgroup S) (x : P) :
    (finiteGroupAmbientEquiv S P x).val = (x.val : G) := rfl

end Sharpness
