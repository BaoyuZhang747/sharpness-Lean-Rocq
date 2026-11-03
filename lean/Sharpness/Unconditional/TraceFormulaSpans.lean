import Sharpness.NormalizerAction
import Sharpness.RawMackey

/-! Concrete intersection geometry for the minimal-simple trace formula. -/

set_option autoImplicit false
noncomputable section
universe u

namespace Sharpness.FusionSystem
open CategoryTheory

variable {S : Type u} [Group S] (F : FusionSystem S)
    {L K T : Subgroup S} (hLT : L ≤ T) (hKT : K ≤ T)

theorem mem_inclusion_spanApex_iff (t : T) (x : S) :
    x ∈ (F.spanApex (F.inclusion hLT) (F.inclusion hKT) t).subgroup ↔
      x ∈ L ∧ t.val⁻¹ * x * t.val ∈ K := by
  rw [F.mem_spanApex_iff]
  constructor
  · rintro ⟨a, rfl, b, hb⟩
    refine ⟨a.property, ?_⟩
    have he := congrArg Subtype.val hb
    change b.val = t.val⁻¹ * a.val * t.val at he
    exact he ▸ b.property
  · rintro ⟨hxL, hxK⟩
    refine ⟨⟨x, hxL⟩, rfl, ⟨t.val⁻¹ * x * t.val, hxK⟩, ?_⟩
    apply Subtype.ext
    rfl

theorem inclusion_spanApex_le (t : T) :
    (F.spanApex (F.inclusion hLT) (F.inclusion hKT) t).subgroup ≤ L :=
  lifted_le _ _

theorem inclusion_spanApex_eq_iff (t : T) :
    (F.spanApex (F.inclusion hLT) (F.inclusion hKT) t).subgroup = L ↔
      ∀ x ∈ L, t.val⁻¹ * x * t.val ∈ K := by
  constructor
  · intro h x hx
    have hx' : x ∈ (F.spanApex (F.inclusion hLT) (F.inclusion hKT) t).subgroup :=
      h.symm ▸ hx
    exact ((F.mem_inclusion_spanApex_iff hLT hKT t x).mp hx').2
  · intro h
    apply le_antisymm (F.inclusion_spanApex_le hLT hKT t)
    intro x hx
    exact (F.mem_inclusion_spanApex_iff hLT hKT t x).mpr ⟨hx, h x hx⟩

theorem inclusion_spanApex_eq_of_normalizer (t : F.relativeNormalizer T L) :
    (F.spanApex (F.inclusion hLT) (F.inclusion hLT)
      (⟨t.val, t.property.2⟩ : T)).subgroup = L := by
  apply (F.inclusion_spanApex_eq_iff hLT hLT _).mpr
  intro x hx
  exact (Subgroup.mem_normalizer_iff''.mp t.property.1 x).mp hx

variable [Finite S]

theorem inclusion_spanApex_eq_of_order (t : T)
    (heq : F.orbitOrder (F.toOrbit.obj
      (F.spanApex (F.inclusion hLT) (F.inclusion hKT) t)) =
      F.orbitOrder (F.toOrbit.obj ⟨L⟩)) :
    (F.spanApex (F.inclusion hLT) (F.inclusion hKT) t).subgroup = L := by
  apply Subgroup.eq_of_le_of_card_ge (F.inclusion_spanApex_le hLT hKT t)
  exact heq.ge

theorem inclusion_self_spanApex_eq_iff_normalizer (t : T) :
    (F.spanApex (F.inclusion hLT) (F.inclusion hLT) t).subgroup = L ↔
      t.val ∈ Subgroup.normalizer (L : Set S) := by
  rw [F.inclusion_spanApex_eq_iff]
  constructor
  · intro h
    let c : L →* L := subgroupConjugation L L t.val h
    have hinj : Function.Injective c := by
      intro a b hab
      apply Subtype.ext
      have he := congrArg Subtype.val hab
      change t.val⁻¹ * a.val * t.val = t.val⁻¹ * b.val * t.val at he
      exact mul_left_cancel (mul_right_cancel he)
    have hsurj := Finite.surjective_of_injective hinj
    apply Subgroup.mem_normalizer_iff''.mpr
    intro x
    constructor
    · exact h x
    · intro hx
      obtain ⟨y, hy⟩ := hsurj ⟨t.val⁻¹ * x * t.val, hx⟩
      have he := congrArg Subtype.val hy
      change t.val⁻¹ * y.val * t.val = t.val⁻¹ * x * t.val at he
      have hyx : y.val = x := mul_left_cancel (mul_right_cancel he)
      exact hyx ▸ y.property
  · intro ht x hx
    exact (Subgroup.mem_normalizer_iff''.mp ht x).mp hx

variable {k : Type u} [Field k]
    (M : MackeyModule.{u,u,u} k F.Orbit F.mackeyShape)

/-- A surviving self-intersection summand is precisely the automorphism
induced by the normalizer representative. -/
theorem rawSpanOperator_inclusion_normalizer (t : F.relativeNormalizer T L) :
    F.rawSpanOperator (F.inclusion hLT) (F.inclusion hLT) M
        (⟨t.val, t.property.2⟩ : T) =
      M.push (F.normalizerToOrbitAut L ⟨t.val, t.property.1⟩).hom := by
  let tT : T := ⟨t.val, t.property.2⟩
  let a : Aut (F.toOrbit.obj ⟨L⟩) :=
    F.normalizerToOrbitAut L ⟨t.val, t.property.1⟩
  let e := F.subgroupEqualityIso (F.inclusion_spanApex_eq_of_normalizer hLT t)
  let s : MackeySpan F.Orbit (F.toOrbit.obj ⟨L⟩) (F.toOrbit.obj ⟨L⟩) :=
    { apex := F.toOrbit.obj ⟨L⟩, left := 𝟙 _, right := a.inv }
  have hl : (F.concreteOrbitSpan (F.inclusion hLT) (F.inclusion hLT) tT).left =
      (F.toOrbit.mapIso e).hom ≫ s.left := by
    simp only [s, Category.comp_id]
    apply congrArg (fun z => F.toOrbit.map z)
    apply Subtype.ext
    ext x
    rfl
  have hr : (F.concreteOrbitSpan (F.inclusion hLT) (F.inclusion hLT) tT).right =
      (F.toOrbit.mapIso e).hom ≫ s.right := by
    change F.toOrbit.map _ = F.toOrbit.map _ ≫ F.toOrbit.map _
    rw [← F.toOrbit.map_comp]
    apply congrArg (fun z => F.toOrbit.map z)
    apply Subtype.ext
    ext x
    have hx := F.concreteSpan_right_equation (F.inclusion hLT) (F.inclusion hLT) tT x
    change ((F.concreteSpan (F.inclusion hLT) (F.inclusion hLT) tT).right.val x).val =
      t.val⁻¹ * x.val * (t.val⁻¹)⁻¹
    rw [inv_inv]
    exact congrArg (fun z : T => z.val) hx
  have he := M.span_operator_of_iso
    (F.concreteOrbitSpan (F.inclusion hLT) (F.inclusion hLT) tT) s
    (F.toOrbit.mapIso e) hl hr
  change F.rawSpanOperator (F.inclusion hLT) (F.inclusion hLT) M tT = _ at he
  rw [he]
  change (M.push (𝟙 _)).comp (M.pull a.inv) = M.push a.hom
  rw [M.push_id, LinearMap.id_comp, M.pull_iso]
  congr 1
  exact (IsIso.eq_inv_of_hom_inv_id a.inv_hom_id).symm

end Sharpness.FusionSystem
