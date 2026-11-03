import Sharpness.CentralAutomorphisms

/-! Actual automorphisms of an actual group quotient. The kernel is proved
to be a normal p-group using the injective delta map. -/
set_option autoImplicit false
noncomputable section
universe u v
namespace Sharpness
variable {P : Type u} [Group P] {A : Type v} [Group A]
    (action : A →* MulAut P) (Z : Subgroup P) [Z.Normal]
    (fixZ : ∀ a : A, ∀ z : Z, action a z.val = z.val)

include fixZ

theorem action_preserves_subgroup (a : A) : Z.map (action a).toMonoidHom = Z := by
  apply le_antisymm
  · rintro _ ⟨z, hz, rfl⟩
    change action a z ∈ Z
    have he : action a z = z := fixZ a ⟨z, hz⟩
    rw [he]
    exact hz
  · intro z hz
    exact ⟨z, hz, fixZ a ⟨z, hz⟩⟩

def quotientAutomorphismAction : A →* MulAut (P ⧸ Z) where
  toFun a := QuotientGroup.congr Z Z (action a) (action_preserves_subgroup action Z fixZ a)
  map_one' := by
    apply MulEquiv.ext
    intro q
    refine QuotientGroup.induction_on q fun x => ?_
    change QuotientGroup.mk (action 1 x) = QuotientGroup.mk x
    rw [map_one]
    rfl
  map_mul' a b := by
    apply MulEquiv.ext
    intro q
    refine QuotientGroup.induction_on q fun x => ?_
    change QuotientGroup.mk (action (a*b) x) = QuotientGroup.mk (action a (action b x))
    rw [map_mul]
    rfl

theorem quotient_kernel_modZ
    (a : (quotientAutomorphismAction action Z fixZ).ker) (x : P) :
    x⁻¹ * action a.val x ∈ Z := by
  have he := DFunLike.congr_fun a.property (QuotientGroup.mk x)
  change QuotientGroup.mk (action a.val x) = QuotientGroup.mk x at he
  exact QuotientGroup.eq.mp he.symm

theorem quotient_kernel_iff (a : A) :
    a ∈ (quotientAutomorphismAction action Z fixZ).ker ↔
      ∀ x : P, x⁻¹ * action a x ∈ Z := by
  constructor
  · intro ha
    exact quotient_kernel_modZ action Z fixZ ⟨a, ha⟩
  · intro ha
    change quotientAutomorphismAction action Z fixZ a = 1
    apply MulEquiv.ext
    intro q
    refine QuotientGroup.induction_on q fun x => ?_
    change QuotientGroup.mk (action a x) = QuotientGroup.mk x
    exact (QuotientGroup.eq.mpr (ha x)).symm

theorem quotient_kernel_isPGroup (p : ℕ) [Fact p.Prime] [Finite P]
    (hZ : IsPGroup p Z) (faithful : Function.Injective action) :
    IsPGroup p (quotientAutomorphismAction action Z fixZ).ker := by
  apply subgroup_isPGroup_of_delta action _ Z
    (fun a z => fixZ a.val z) (quotient_kernel_modZ action Z fixZ) p hZ faithful

end Sharpness
