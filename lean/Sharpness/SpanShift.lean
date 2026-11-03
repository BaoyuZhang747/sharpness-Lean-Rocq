import Sharpness.SpanEquations

/-! Actual apex isomorphisms when a double-coset representative changes
from u to f(a) u g(b). No representative-independence is assumed. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem
open CategoryTheory
variable {S : Type u} [Group S] (F : FusionSystem S)
    {P Q T : F.Object} (f : P ⟶ T) (g : Q ⟶ T) (u : T.subgroup)
    (a : P.subgroup) (b : Q.subgroup)

def shiftedRepresentative : T.subgroup := f.val a * u * g.val b

theorem shiftedRepresentative_inverse :
    F.shiftedRepresentative f g (F.shiftedRepresentative f g u a b) a⁻¹ b⁻¹ = u := by
  dsimp [shiftedRepresentative]
  rw [map_inv, map_inv]
  group

theorem span_shift_mem (x : (F.spanApex f g u).subgroup) :
    a.val * x.val * a.val⁻¹ ∈
      (F.spanApex f g (F.shiftedRepresentative f g u a b)).subgroup := by
  let xP := (F.spanLeft f g u).val x
  let y := (F.concreteSpan f g u).right.val x
  apply (F.mem_spanApex_iff f g _ _).mpr
  refine ⟨a * xP * a⁻¹, rfl, b⁻¹ * y * b, ?_⟩
  have hy : g.val y = u⁻¹ * f.val xP * u := F.concreteSpan_right_equation f g u x
  simp only [map_mul, map_inv]
  rw [hy]
  dsimp [shiftedRepresentative]
  group

def spanShiftHom : F.spanApex f g u ⟶
    F.spanApex f g (F.shiftedRepresentative f g u a b) := by
  have hm : ∀ x ∈ (F.spanApex f g u).subgroup,
      (a.val⁻¹)⁻¹ * x * a.val⁻¹ ∈
        (F.spanApex f g (F.shiftedRepresentative f g u a b)).subgroup := by
    intro x hx
    rw [inv_inv]
    exact F.span_shift_mem f g u a b ⟨x, hx⟩
  exact ⟨subgroupConjugation _ _ a.val⁻¹ hm, F.conjugation_mem _ _ _ hm⟩

def spanShiftInv : F.spanApex f g (F.shiftedRepresentative f g u a b) ⟶
    F.spanApex f g u := by
  have hm : ∀ x ∈ (F.spanApex f g (F.shiftedRepresentative f g u a b)).subgroup,
      a.val⁻¹ * x * a.val ∈ (F.spanApex f g u).subgroup := by
    intro x hx
    have h := F.span_shift_mem f g (F.shiftedRepresentative f g u a b) a⁻¹ b⁻¹ ⟨x, hx⟩
    rw [F.shiftedRepresentative_inverse] at h
    simpa only [Subgroup.coe_inv, inv_inv] using h
  exact ⟨subgroupConjugation _ _ a.val hm, F.conjugation_mem _ _ _ hm⟩

def spanShiftIso : F.spanApex f g u ≅
    F.spanApex f g (F.shiftedRepresentative f g u a b) where
  hom := F.spanShiftHom f g u a b
  inv := F.spanShiftInv f g u a b
  hom_inv_id := by
    apply Subtype.ext
    apply MonoidHom.ext
    intro x
    apply Subtype.ext
    change a.val⁻¹ * ((a.val⁻¹)⁻¹ * x.val * a.val⁻¹) * a.val = x.val
    group
  inv_hom_id := by
    apply Subtype.ext
    apply MonoidHom.ext
    intro x
    apply Subtype.ext
    change (a.val⁻¹)⁻¹ * (a.val⁻¹ * x.val * a.val) * a.val⁻¹ = x.val
    group

theorem spanShift_left_square :
    F.spanLeft f g u ≫ F.inner P a⁻¹ =
      (F.spanShiftIso f g u a b).hom ≫
        F.spanLeft f g (F.shiftedRepresentative f g u a b) := by
  apply Subtype.ext
  apply MonoidHom.ext
  intro x
  apply Subtype.ext
  rfl

theorem spanShift_right_square :
    (F.concreteSpan f g u).right ≫ F.inner Q b =
      (F.spanShiftIso f g u a b).hom ≫
        (F.concreteSpan f g (F.shiftedRepresentative f g u a b)).right := by
  apply Subtype.ext
  apply MonoidHom.ext
  intro x
  apply F.injective g.val g.property
  change g.val (b⁻¹ * (F.concreteSpan f g u).right.val x * b) =
    g.val ((F.concreteSpan f g (F.shiftedRepresentative f g u a b)).right.val
      ((F.spanShiftIso f g u a b).hom.val x))
  rw [map_mul, map_mul, map_inv, F.concreteSpan_right_equation,
    F.concreteSpan_right_equation]
  have hx : (F.spanLeft f g (F.shiftedRepresentative f g u a b)).val
      ((F.spanShiftIso f g u a b).hom.val x) = a * (F.spanLeft f g u).val x * a⁻¹ := by
    apply Subtype.ext
    change (a.val⁻¹)⁻¹ * x.val * a.val⁻¹ = a.val * x.val * a.val⁻¹
    rw [inv_inv]
  rw [hx, map_mul, map_mul, map_inv]
  dsimp [shiftedRepresentative]
  group

end Sharpness.FusionSystem
