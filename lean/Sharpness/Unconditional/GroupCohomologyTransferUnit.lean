import Sharpness.Unconditional.GroupCohomologyTransferConstruction
import Sharpness.Unconditional.GroupCohomologyShapiroMap
import Sharpness.Unconditional.GroupCohomologyFunctor

/-! Restriction is the coinduction unit followed by the actual Shapiro map.
Consequently restriction followed by transfer is multiplication by the index. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness.OrdinaryCohomology
open CategoryTheory

variable {R G A : Type u} [CommRing R] [Group G]
  [AddCommGroup A] [Module R A]

/-- Native restriction is induced by the actual coinduction unit and Shapiro. -/
theorem restriction_eq_unit_shapiro (H : Subgroup G) (V : Rep.{u} R G) (n : ℕ) :
    groupCohomology.map H.subtype (𝟙 (Rep.res H.subtype V)) n =
      groupCohomology.map (MonoidHom.id G)
          ((Rep.resCoindAdjunction.{u} R H.subtype).unit.app V) n ≫
        (groupCohomology.coindIso (Rep.res H.subtype V) n).hom := by
  rw [coindIso_hom_eq_map]
  rw [← groupCohomology.map_comp]
  rw [(Rep.resCoindAdjunction.{u} R H.subtype).left_triangle_components V]
  rfl

/-- The representation trace after its coinduction unit is index times identity. -/
theorem coinductionTrace_unit (H : Subgroup G) [H.FiniteIndex] (V : Rep.{u} R G) :
    (Rep.resCoindAdjunction.{u} R H.subtype).unit.app V ≫ coinductionTrace H V =
      H.index • 𝟙 V := by
  apply Rep.hom_ext
  ext a
  exact coinductionTrace_unit_apply H V a

/-- The native restriction/corestriction composite is multiplication by the index,
for every representation and every degree, including degree zero. -/
theorem restriction_corestriction (H : Subgroup G) [H.FiniteIndex]
    (V : Rep.{u} R G) (n : ℕ) :
    groupCohomology.map H.subtype (𝟙 (Rep.res H.subtype V)) n ≫ corestriction H V n =
      H.index • 𝟙 (groupCohomology V n) := by
  rw [restriction_eq_unit_shapiro, corestriction]
  rw [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← groupCohomology.map_id_comp, coinductionTrace_unit]
  change (groupCohomology.functor R G n).map (H.index • 𝟙 V) = _
  rw [Functor.map_nsmul, (groupCohomology.functor R G n).map_id V]
  rfl

/-- The same formula on the native pullbacks and transfers of trivial modules. -/
theorem pull_transfer (H : Subgroup G) [H.FiniteIndex] (n : ℕ) :
    pull (R := R) (A := A) H.subtype n ≫ transfer H n =
      H.index • 𝟙 (value R G A n) :=
  restriction_corestriction H (Rep.trivial R G A) n

end Sharpness.OrdinaryCohomology
