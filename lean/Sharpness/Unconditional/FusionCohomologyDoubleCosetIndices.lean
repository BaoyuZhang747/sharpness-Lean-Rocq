import Sharpness.Unconditional.InclusionMackeyBridgeDoubleCosets
import Sharpness.Unconditional.GroupCohomologyMackeyDecomposition

/-! Actual inversion and reindexing between the native coinduction convention
H\G/K and the fusion span convention K\G/H. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v w

namespace Sharpness.OrdinaryCohomology.MackeyDecomposition
variable {G : Type v} [Group G] (H K : Subgroup G)

def inverseDoubleCosetMap : DoubleCoset.Quotient (H : Set G) K →
    DoubleCoset.Quotient (K : Set G) H :=
  Quotient.map Inv.inv (by
    intro x y h
    obtain ⟨a, ha, b, hb, rfl⟩ := DoubleCoset.rel_iff.mp h
    exact DoubleCoset.rel_iff.mpr
      ⟨b⁻¹, K.inv_mem hb, a⁻¹, H.inv_mem ha, by simp [mul_assoc]⟩)

/-- Inversion reverses the two actual double-coset subgroups. -/
def inverseDoubleCosetEquiv : DoubleCoset.Quotient (H : Set G) K ≃
    DoubleCoset.Quotient (K : Set G) H where
  toFun := inverseDoubleCosetMap H K
  invFun := inverseDoubleCosetMap K H
  left_inv d := Quotient.inductionOn d (fun x => by
    change DoubleCoset.mk H K x⁻¹⁻¹ = DoubleCoset.mk H K x
    rw [inv_inv])
  right_inv d := Quotient.inductionOn d (fun x => by
    change DoubleCoset.mk K H x⁻¹⁻¹ = DoubleCoset.mk K H x
    rw [inv_inv])

@[simp] theorem inverseDoubleCosetEquiv_mk (x : G) :
    inverseDoubleCosetEquiv H K (DoubleCoset.mk H K x) =
      DoubleCoset.mk K H x⁻¹ := rfl

theorem inverseDoubleCosetEquiv_out (d : DoubleCoset.Quotient (H : Set G) K) :
    inverseDoubleCosetEquiv H K d = DoubleCoset.mk K H d.out⁻¹ := by
  conv_lhs => rw [← DoubleCoset.out_eq' H K d]
  rfl

end Sharpness.OrdinaryCohomology.MackeyDecomposition

namespace Sharpness.FusionSystem
open CategoryTheory OrdinaryCohomology.MackeyDecomposition
open scoped BigOperators
variable {S : Type u} [Group S] (F : FusionSystem S)
    {P Q T : F.Object} (hP : P.subgroup ≤ T.subgroup) (hQ : Q.subgroup ≤ T.subgroup)

theorem inclusion_range_subgroupOf : (F.inclusion hP).val.range =
    P.subgroup.subgroupOf T.subgroup := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact y.2
  · intro hx
    exact ⟨⟨x.val, hx⟩, Subtype.ext rfl⟩

/-- The native index set maps to the actual raw fusion index set by inversion. -/
def inclusionNativeDoubleCosetEquiv :
    DoubleCoset.Quotient (Q.subgroup.subgroupOf T.subgroup : Set T.subgroup)
      (P.subgroup.subgroupOf T.subgroup) ≃
    F.RawDoubleCosetTerm (F.inclusion hP) (F.inclusion hQ) where
  toFun := Quotient.map Inv.inv (by
    intro x y h
    obtain ⟨a, ha, b, hb, rfl⟩ := DoubleCoset.rel_iff.mp h
    apply DoubleCoset.rel_iff.mpr
    refine ⟨b⁻¹, ?_, a⁻¹, ?_, by simp [mul_assoc]⟩
    · rw [F.inclusion_range_subgroupOf hP]
      exact (P.subgroup.subgroupOf T.subgroup).inv_mem hb
    · rw [F.inclusion_range_subgroupOf hQ]
      exact (Q.subgroup.subgroupOf T.subgroup).inv_mem ha)
  invFun := Quotient.map Inv.inv (by
    intro x y h
    obtain ⟨a, ha, b, hb, rfl⟩ := DoubleCoset.rel_iff.mp h
    rw [F.inclusion_range_subgroupOf hP] at ha
    rw [F.inclusion_range_subgroupOf hQ] at hb
    exact DoubleCoset.rel_iff.mpr
      ⟨b⁻¹, (Q.subgroup.subgroupOf T.subgroup).inv_mem hb,
        a⁻¹, (P.subgroup.subgroupOf T.subgroup).inv_mem ha, by simp [mul_assoc]⟩)
  left_inv d := Quotient.inductionOn d (fun x => by
    change Quotient.mk'' x⁻¹⁻¹ = Quotient.mk'' x
    rw [inv_inv])
  right_inv d := Quotient.inductionOn d (fun x => by
    change Quotient.mk'' x⁻¹⁻¹ = Quotient.mk'' x
    rw [inv_inv])

@[simp] theorem inclusionNativeDoubleCosetEquiv_mk (x : T.subgroup) :
    F.inclusionNativeDoubleCosetEquiv hP hQ
      (DoubleCoset.mk (Q.subgroup.subgroupOf T.subgroup)
        (P.subgroup.subgroupOf T.subgroup) x) =
    DoubleCoset.mk (F.inclusion hP).val.range (F.inclusion hQ).val.range x⁻¹ := rfl

theorem inclusionNativeDoubleCosetEquiv_out
    (d : DoubleCoset.Quotient (Q.subgroup.subgroupOf T.subgroup : Set T.subgroup)
      (P.subgroup.subgroupOf T.subgroup)) :
    F.inclusionNativeDoubleCosetEquiv hP hQ d =
      DoubleCoset.mk (F.inclusion hP).val.range (F.inclusion hQ).val.range d.out⁻¹ := by
  conv_lhs => rw [← DoubleCoset.out_eq' _ _ d]
  exact F.inclusionNativeDoubleCosetEquiv_mk hP hQ d.out

variable [Finite S] {R : Type u} [Ring R] (E : MackeyFunctorData.{u,w} R F.Orbit)

/-- Actual quotient-invariant span operators evaluate at the inverted native representative. -/
theorem functorDataDoubleCosetOperator_native
    (d : DoubleCoset.Quotient (Q.subgroup.subgroupOf T.subgroup : Set T.subgroup)
      (P.subgroup.subgroupOf T.subgroup)) :
    F.functorDataDoubleCosetOperator E (F.inclusion hP) (F.inclusion hQ)
      (F.inclusionNativeDoubleCosetEquiv hP hQ d) =
    F.functorDataSpanOperator E (F.inclusion hP) (F.inclusion hQ) d.out⁻¹ := by
  rw [F.inclusionNativeDoubleCosetEquiv_out]
  rfl

/-- Reindexing does not require a Mackey formula for the functor data. -/
theorem functorDataDoubleCosetOperator_sum_native
    [Fintype (DoubleCoset.Quotient
      (Q.subgroup.subgroupOf T.subgroup : Set T.subgroup)
      (P.subgroup.subgroupOf T.subgroup))] :
    (∑ i : F.RawDoubleCosetTerm (F.inclusion hP) (F.inclusion hQ),
      F.functorDataDoubleCosetOperator E (F.inclusion hP) (F.inclusion hQ) i) =
    ∑ d : DoubleCoset.Quotient (Q.subgroup.subgroupOf T.subgroup : Set T.subgroup)
      (P.subgroup.subgroupOf T.subgroup),
      F.functorDataSpanOperator E (F.inclusion hP) (F.inclusion hQ) d.out⁻¹ := by
  rw [← (F.inclusionNativeDoubleCosetEquiv hP hQ).sum_comp]
  exact Finset.sum_congr rfl (fun d _ => F.functorDataDoubleCosetOperator_native hP hQ E d)

end Sharpness.FusionSystem
