import Sharpness.FusionQuotientKernel

/-! Transport of the actual minimal simple module along fusion-orbit
isomorphisms. This supplies all minimal-class values for Lemma 3.3 Step 2. -/
set_option autoImplicit false
noncomputable section
universe u v w
namespace Sharpness
open CategoryTheory

namespace MackeyModule
variable {R : Type u} [Ring R] {C : Type v} [Category.{v} C] {B : MackeyShape C}
    (M : MackeyModule.{u,v,w} R C B)

theorem push_inv_apply {P Q : C} (e : P ≅ Q) (x : M.Value P) :
    M.push e.inv (M.push e.hom x) = x := by
  rw [← LinearMap.comp_apply, ← M.push_comp, e.hom_inv_id, M.push_id]
  rfl

theorem push_hom_apply {P Q : C} (e : P ≅ Q) (x : M.Value Q) :
    M.push e.hom (M.push e.inv x) = x := by
  rw [← LinearMap.comp_apply, ← M.push_comp, e.inv_hom_id, M.push_id]
  rfl

def isoLinearEquiv {P Q : C} (e : P ≅ Q) : M.Value P ≃ₗ[R] M.Value Q :=
  { M.push e.hom with
    invFun := M.push e.inv
    left_inv := M.push_inv_apply e
    right_inv := M.push_hom_apply e }

end MackeyModule

namespace FusionSystem
variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)
    {k : Type u} [Field k] (M : MackeyModule.{u,u,u} k F.Orbit F.mackeyShape)
    (label : F.SimpleLabel M)

def SimpleLabel.transport {L : F.Orbit} (e : label.Q ≅ L) : F.SimpleLabel M where
  Q := L
  simple := label.simple
  nonzero := by
    obtain ⟨x, hx⟩ := label.nonzero
    refine ⟨M.push e.hom x, ?_⟩
    intro h
    apply hx
    apply (M.isoLinearEquiv e).injective
    exact h.trans (map_zero _).symm
  small_zero P hP := label.small_zero P
    (hP.trans_eq (le_antisymm (F.orbitOrder_mono e.inv) (F.orbitOrder_mono e.hom)))
  simple_at_Q A invariant := by
    let f := M.push e.hom
    let pre := A.comap f
    have stable : ∀ a : Aut label.Q, ∀ x ∈ pre, M.automorphismAction label.Q a x ∈ pre := by
      intro a x hx
      let b : Aut L := (e.symm.trans a).trans e
      have hb := invariant b (M.push e.hom x) hx
      change M.push e.hom (M.push a.hom x) ∈ A
      convert hb using 1
      change M.push e.hom (M.push a.hom x) = M.push b.hom (M.push e.hom x)
      rw [← LinearMap.comp_apply, ← M.push_comp, ← LinearMap.comp_apply, ← M.push_comp]
      congr 1
      simp [b, Category.assoc]
    have surj : Function.Surjective f := (M.isoLinearEquiv e).surjective
    have reconstruct : pre.map f = A := Submodule.map_comap_eq_of_surjective surj A
    rcases label.simple_at_Q pre stable with hbot | htop
    · left
      rw [hbot, Submodule.map_bot] at reconstruct
      exact reconstruct.symm
    · right
      rw [htop] at reconstruct
      rw [← reconstruct]
      rw [Submodule.map_top]
      exact LinearMap.range_eq_top.mpr surj

/-- The actual normal quotient kernel acts trivially at every subgroup in
the minimal fusion class, by the proved transport of simple labels. -/
theorem central_kernel_trivial_on_conjugate (p : ℕ) [Fact p.Prime] [CharP k p]
    (hS : IsPGroup p S) {Z : Subgroup S} (hZ : F.CentralSubgroup Z)
    (hZQ : Z ≤ label.Q.as.subgroup) (L : Subgroup S)
    (e : label.Q ≅ F.toOrbit.obj ⟨L⟩) :
    letI := F.central_subgroupOf_normal hZ (F.toOrbit.obj ⟨L⟩).as.subgroup
    let hZL := (F.central_containment_iff hZ (F.groupEquivOfOrbitIso e)
      (F.groupEquivOfOrbitIso_allowed e)).mp hZQ
    ∀ a : F.Gamma hZ hZL,
      M.push (F.automorphismToOrbitAut L a.val).hom = LinearMap.id := by
  letI := F.central_subgroupOf_normal hZ L
  exact F.central_kernel_trivial_on_minimal hZ p hS M (SimpleLabel.transport F M label e) _

end FusionSystem
end Sharpness
