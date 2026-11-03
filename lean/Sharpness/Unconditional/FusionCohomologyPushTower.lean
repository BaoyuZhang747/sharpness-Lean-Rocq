import Sharpness.Unconditional.FusionCohomologyPushFactorization
import Sharpness.Unconditional.GroupCohomologyNativeTransferTower

/-! Composition with literal subgroup inclusions for actual native
fusion cohomology pushforward. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness.FusionSystem
open CategoryTheory

variable {R S A : Type u} [CommRing R] [Group S] [Finite S]
  [AddCommGroup A] [Module R A] (F : FusionSystem S)

theorem nativeGroupCohomologyRawPush_postcomp_inclusion {P Q T : F.Object}
    (f : P ⟶ Q) (h : Q.subgroup ≤ T.subgroup) (n : ℕ) :
    F.groupCohomologyRawPush (nativeGroupCohomologyTransfer (R := R) (S := S) (A := A) n)
        (f ≫ F.inclusion h) =
      (OrdinaryCohomology.subgroupTransfer Q.subgroup T.subgroup h n).comp
        (F.groupCohomologyRawPush
          (nativeGroupCohomologyTransfer (R := R) (S := S) (A := A) n) f) := by
  have hf : f ≫ F.inclusion h = (F.imageIso f).hom ≫
      F.inclusion ((F.image_le f).trans h) := by
    rw [← F.image_factorization f, Category.assoc]
    rfl
  rw [hf, F.nativeGroupCohomologyRawPush_iso_inclusion]
  change (OrdinaryCohomology.subgroupTransfer (F.imageSubgroup f) T.subgroup
      ((F.image_le f).trans h) n).comp (F.groupCohomologyRawPull (F.imageIso f).inv n) =
    (OrdinaryCohomology.subgroupTransfer Q.subgroup T.subgroup h n).comp
      ((OrdinaryCohomology.subgroupTransfer (F.imageSubgroup f) Q.subgroup
        (F.image_le f) n).comp (F.groupCohomologyRawPull (F.imageIso f).inv n))
  rw [← LinearMap.comp_assoc, OrdinaryCohomology.subgroupTransfer_comp]

end Sharpness.FusionSystem
