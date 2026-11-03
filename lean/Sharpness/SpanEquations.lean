import Sharpness.FusionMackey
import Sharpness.MackeyPullback

/-! Pointwise equations for the actual intersection spans. These equations
are used to compare representatives without adding coherence assumptions. -/
set_option autoImplicit false
noncomputable section
universe u w
namespace Sharpness.FusionSystem
open CategoryTheory
variable {S : Type u} [Group S] (F : FusionSystem S)
    {P Q T : F.Object} (f : P ⟶ T) (g : Q ⟶ T) (u : T.subgroup)

theorem mem_spanApex_iff (x : S) : x ∈ (F.spanApex f g u).subgroup ↔
    ∃ xP : P.subgroup, xP.val = x ∧
      ∃ y : Q.subgroup, g.val y = u⁻¹ * f.val xP * u := by
  constructor
  · rintro ⟨xP, hxP, rfl⟩
    exact ⟨xP, rfl, hxP⟩
  · rintro ⟨xP, rfl, hxP⟩
    exact ⟨xP, hxP, rfl⟩

theorem concreteSpan_right_comp : (F.concreteSpan f g u).right ≫ g =
    F.spanConjugate f g u := by
  have hg : g = (F.imageIso g).hom ≫ F.inclusion (F.image_le g) :=
    (F.image_factorization g).symm
  change (F.spanToImage f g u ≫ (F.imageIso g).inv) ≫ g = _
  conv_lhs =>
    rhs
    rw [hg]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  apply Subtype.ext
  apply MonoidHom.ext
  intro x
  rfl

theorem concreteSpan_right_equation (x : (F.spanApex f g u).subgroup) :
    g.val ((F.concreteSpan f g u).right.val x) =
      u⁻¹ * f.val ((F.spanLeft f g u).val x) * u :=
  congrArg (fun t : F.spanApex f g u ⟶ T => t.val x)
    (F.concreteSpan_right_comp f g u)

end Sharpness.FusionSystem

namespace Sharpness.MackeyModule
open CategoryTheory
variable {R : Type u} [Ring R] {C : Type u} [Category.{u} C]
    {B : MackeyShape C} (M : MackeyModule.{u,u,w} R C B)

theorem span_operator_of_iso {P Q : C} (s t : MackeySpan C P Q)
    (e : s.apex ≅ t.apex) (hl : s.left = e.hom ≫ t.left)
    (hr : s.right = e.hom ≫ t.right) :
    (M.push s.left).comp (M.pull s.right) =
      (M.push t.left).comp (M.pull t.right) := by
  rw [hl, hr, M.push_comp, M.pull_comp]
  apply LinearMap.ext
  intro x
  change M.push t.left (M.push e.hom (M.pull e.hom (M.pull t.right x))) = _
  have h := LinearMap.congr_fun (M.push_pull_iso e) (M.pull t.right x)
  change M.push e.hom (M.pull e.hom (M.pull t.right x)) = M.pull t.right x at h
  rw [h]
  rfl

end Sharpness.MackeyModule
