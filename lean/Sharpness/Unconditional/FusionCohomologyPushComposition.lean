import Sharpness.Unconditional.FusionCohomologyPushTower
import Sharpness.Unconditional.GroupCohomologyTransferSquare

/-! The manuscript's covariant cohomology maps compose, using the
actual native transfer tower and its group-isomorphism covariance. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness.FusionSystem
open CategoryTheory

variable {R S A : Type u} [CommRing R] [Group S] [Finite S]
  [AddCommGroup A] [Module R A] (F : FusionSystem S)

omit [Finite S] in
/-- A fusion isomorphism as a group equivalence, retaining its given inverse. -/
def cohomologyMulEquivOfIso {P Q : F.Object} (e : P ≅ Q) : P.subgroup ≃* Q.subgroup where
  toFun := e.hom.val
  invFun := e.inv.val
  left_inv x := congrArg (fun f : P ⟶ P => f.val x) e.hom_inv_id
  right_inv x := congrArg (fun f : Q ⟶ Q => f.val x) e.inv_hom_id
  map_mul' := e.hom.val.map_mul

theorem nativeGroupCohomologyRawPush_inclusion_iso {P Q T : F.Object}
    (h : P.subgroup ≤ Q.subgroup) (e : Q ≅ T) (n : ℕ) :
    F.groupCohomologyRawPush (nativeGroupCohomologyTransfer (R := R) (S := S) (A := A) n)
        (F.inclusion h ≫ e.hom) =
      (F.groupCohomologyRawPull e.inv n).comp
        (OrdinaryCohomology.subgroupTransfer P.subgroup Q.subgroup h n) := by
  let f := F.inclusion h ≫ e.hom
  have hs : (Subgroup.inclusion (F.image_le f)).comp
      (F.cohomologyMulEquivOfIso (F.imageIso f)).toMonoidHom =
      (F.cohomologyMulEquivOfIso e).toMonoidHom.comp (Subgroup.inclusion h) := by
    exact congrArg (fun k : P ⟶ T => k.val) (F.image_factorization f)
  exact (OrdinaryCohomology.subgroupTransfer_mulEquiv_square
    P.subgroup Q.subgroup (F.imageSubgroup f) T.subgroup h (F.image_le f)
    (F.cohomologyMulEquivOfIso (F.imageIso f)) (F.cohomologyMulEquivOfIso e) hs n).symm

theorem nativeGroupCohomologyRawPush_postcomp_iso {P Q T : F.Object}
    (f : P ⟶ Q) (e : Q ≅ T) (n : ℕ) :
    F.groupCohomologyRawPush (nativeGroupCohomologyTransfer (R := R) (S := S) (A := A) n)
        (f ≫ e.hom) =
      (F.groupCohomologyRawPull e.inv n).comp
        (F.groupCohomologyRawPush
          (nativeGroupCohomologyTransfer (R := R) (S := S) (A := A) n) f) := by
  have hf : f ≫ e.hom = (F.imageIso f).hom ≫ (F.inclusion (F.image_le f) ≫ e.hom) := by
    rw [← Category.assoc]
    exact congrArg (fun k : P ⟶ Q => k ≫ e.hom) (F.image_factorization f).symm
  rw [hf, F.nativeGroupCohomologyRawPush_precomp_iso,
    F.nativeGroupCohomologyRawPush_inclusion_iso, LinearMap.comp_assoc]
  rfl

theorem nativeGroupCohomologyRawPush_comp {P Q T : F.Object}
    (f : P ⟶ Q) (g : Q ⟶ T) (n : ℕ) :
    F.groupCohomologyRawPush (nativeGroupCohomologyTransfer (R := R) (S := S) (A := A) n)
        (f ≫ g) =
      (F.groupCohomologyRawPush
        (nativeGroupCohomologyTransfer (R := R) (S := S) (A := A) n) g).comp
        (F.groupCohomologyRawPush
          (nativeGroupCohomologyTransfer (R := R) (S := S) (A := A) n) f) := by
  have hg : f ≫ g = (f ≫ (F.imageIso g).hom) ≫ F.inclusion (F.image_le g) := by
    rw [Category.assoc]
    exact congrArg (fun k : Q ⟶ T => f ≫ k) (F.image_factorization g).symm
  rw [hg, F.nativeGroupCohomologyRawPush_postcomp_inclusion,
    F.nativeGroupCohomologyRawPush_postcomp_iso, ← LinearMap.comp_assoc]
  rfl

end Sharpness.FusionSystem
