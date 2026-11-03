import Sharpness.Unconditional.GroupCohomologyTransferUnit

/-! The actual subgroup transfer along a reflexive inclusion is identity. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness.OrdinaryCohomology
open CategoryTheory

variable {R G A : Type u} [CommRing R] [Group G] [Finite G]
  [AddCommGroup A] [Module R A]

theorem subgroupTransfer_self (P : Subgroup G) (n : ℕ) :
    subgroupTransfer (R := R) (A := A) P P le_rfl n = LinearMap.id := by
  have he : (Subgroup.subgroupOfEquivOfLe (le_rfl : P ≤ P)).toMonoidHom =
      (P.subgroupOf P).subtype := by
    ext x
    rfl
  have hP : P.subgroupOf P = ⊤ := by
    apply le_antisymm le_top
    intro x _
    exact x.property
  unfold subgroupTransfer
  rw [he, pull_transfer]
  simp only [hP, Subgroup.index_top, one_smul]
  rfl

end Sharpness.OrdinaryCohomology
