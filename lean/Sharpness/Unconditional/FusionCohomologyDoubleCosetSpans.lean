import Sharpness.Unconditional.FusionCohomologyDoubleCosetIndices

/-! The actual intersection in native coinduction is the concrete fusion
span apex at the inverted representative. Both group-homomorphism legs
commute under the explicit multiplicative equivalence. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness.FusionSystem
open CategoryTheory OrdinaryCohomology.MackeyDecomposition
variable {S : Type u} [Group S] (F : FusionSystem S)
    {P Q T : F.Object} (hP : P.subgroup ≤ T.subgroup) (hQ : Q.subgroup ≤ T.subgroup)

theorem mem_inclusionSpanApex_inv_iff (x : T.subgroup) (y : S) :
    y ∈ (F.spanApex (F.inclusion hP) (F.inclusion hQ) x⁻¹).subgroup ↔
      y ∈ P.subgroup ∧ (x : S) * y * (x : S)⁻¹ ∈ Q.subgroup := by
  rw [F.mem_spanApex_iff]
  constructor
  · rintro ⟨p, rfl, q, hq⟩
    refine ⟨p.2, ?_⟩
    have he : (q : S) = (x : S) * (p : S) * (x : S)⁻¹ := by
      simpa [inclusion, subgroupInclusion] using congrArg Subtype.val hq
    exact he ▸ q.2
  · rintro ⟨hp, hq⟩
    refine ⟨⟨y, hp⟩, rfl, ⟨(x : S) * y * (x : S)⁻¹, hq⟩, ?_⟩
    apply Subtype.ext
    simp only [inv_inv]
    rfl

/-- The native coinduction intersection, inside the actual subgroup P of T. -/
abbrev inclusionNativeIntersection (x : T.subgroup) :=
  intersection (Q.subgroup.subgroupOf T.subgroup) (P.subgroup.subgroupOf T.subgroup) x

/-- This map simply removes the nested subgroup wrappers; its image is
proved to be exactly the manuscript's concrete span apex. -/
def inclusionNativeIntersectionEquiv (x : T.subgroup) :
    F.inclusionNativeIntersection (P := P) (Q := Q) x ≃*
      (F.spanApex (F.inclusion hP) (F.inclusion hQ) x⁻¹).subgroup where
  toFun y := ⟨(y.val.val : S),
    (F.mem_inclusionSpanApex_inv_iff hP hQ x _).mpr ⟨y.val.2, y.2⟩⟩
  invFun y :=
    let hy := (F.mem_inclusionSpanApex_inv_iff hP hQ x y.val).mp y.2
    ⟨⟨⟨y.val, hP hy.1⟩, hy.1⟩, hy.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

@[simp] theorem inclusionNativeIntersectionEquiv_apply (x : T.subgroup)
    (y : F.inclusionNativeIntersection (P := P) (Q := Q) x) :
    ((F.inclusionNativeIntersectionEquiv hP hQ x y :
      (F.spanApex (F.inclusion hP) (F.inclusion hQ) x⁻¹).subgroup) : S) =
      (y.val.val : S) := rfl

/-- The conjugation leg expressed directly in the original subgroup Q. -/
def inclusionNativeConjugation (x : T.subgroup) :
    F.inclusionNativeIntersection (P := P) (Q := Q) x →* Q.subgroup where
  toFun y := ⟨(x : S) * (y.val.val : S) * (x : S)⁻¹, y.2⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' a b := by apply Subtype.ext; simp [mul_assoc]

/-- The left leg is exactly the subgroup inclusion after removing wrappers. -/
theorem inclusionNativeIntersectionEquiv_left (x : T.subgroup) :
    (F.concreteSpan (F.inclusion hP) (F.inclusion hQ) x⁻¹).left.val.comp
        (F.inclusionNativeIntersectionEquiv hP hQ x).toMonoidHom =
      (Subgroup.subgroupOfEquivOfLe hP).toMonoidHom.comp
        (F.inclusionNativeIntersection (P := P) (Q := Q) x).subtype := by
  ext y
  rfl

/-- The right leg is exactly k ↦ x*k*x⁻¹, with codomain Q. -/
theorem inclusionNativeIntersectionEquiv_right (x : T.subgroup) :
    (F.concreteSpan (F.inclusion hP) (F.inclusion hQ) x⁻¹).right.val.comp
        (F.inclusionNativeIntersectionEquiv hP hQ x).toMonoidHom =
      F.inclusionNativeConjugation (P := P) (Q := Q) x := by
  ext y
  have he := F.concreteSpan_right_equation (F.inclusion hP) (F.inclusion hQ) x⁻¹
    (F.inclusionNativeIntersectionEquiv hP hQ x y)
  have he' := congrArg Subtype.val he
  simp only [inv_inv] at he'
  exact he'

end Sharpness.FusionSystem
