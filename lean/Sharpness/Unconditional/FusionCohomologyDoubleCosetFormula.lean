import Sharpness.Unconditional.FusionCohomologyDoubleCosetTerms
import Sharpness.Unconditional.GroupCohomologyTransferSquare

/-! The native cohomological double-coset formula transported through the
actual subgroup charts to the manuscript's concrete fusion spans. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness.FusionSystem
open CategoryTheory OrdinaryCohomology OrdinaryCohomology.MackeyDecomposition
open scoped BigOperators
variable {S R A : Type u} [Group S] [Finite S] [CommRing R]
    [AddCommGroup A] [Module R A] (F : FusionSystem S)
    {P Q T : F.Object} (hP : P.subgroup ≤ T.subgroup) (hQ : Q.subgroup ≤ T.subgroup)

/-- Covariance of the native transfer under the explicit intersection chart. -/
theorem inclusionNativeIntersection_transfer (x : T.subgroup) (n : ℕ) :
    (pullLinear (R := R) (A := A) (Subgroup.subgroupOfEquivOfLe hP).symm.toMonoidHom n).comp
      (transfer (F.inclusionNativeIntersection (P := P) (Q := Q) x) n).hom =
    (subgroupTransfer
      (F.spanApex (F.inclusion hP) (F.inclusion hQ) x⁻¹).subgroup P.subgroup
      (lifted_le _ _) n).comp
        (pullLinear (F.inclusionNativeIntersectionEquiv hP hQ x).symm.toMonoidHom n) := by
  let D := (F.spanApex (F.inclusion hP) (F.inclusion hQ) x⁻¹).subgroup
  let hd : D ≤ P.subgroup := lifted_le _ _
  let a := Subgroup.subgroupOfEquivOfLe hd
  let eA := F.inclusionNativeIntersectionEquiv hP hQ x
  let eP := Subgroup.subgroupOfEquivOfLe hP
  let eH := eA.trans a.symm
  have hs : (D.subgroupOf P.subgroup).subtype.comp eH.toMonoidHom =
      eP.toMonoidHom.comp (F.inclusionNativeIntersection (P := P) (Q := Q) x).subtype := by
    ext y
    rfl
  have hh := transfer_mulEquiv_square (R := R) (A := A)
    (F.inclusionNativeIntersection (P := P) (Q := Q) x)
    (D.subgroupOf P.subgroup) eP eH hs n
  have he : eH.symm.toMonoidHom = eA.symm.toMonoidHom.comp a.toMonoidHom := rfl
  rw [he, pull_comp, Category.assoc] at hh
  exact congrArg (fun f : value R (F.inclusionNativeIntersection (P := P) (Q := Q) x) A n ⟶
    value R P.subgroup A n => f.hom) hh

/-- A native cohomological term, charted back to the original P and Q. -/
def nativeInclusionDoubleCosetTerm (x : T.subgroup) (n : ℕ) :
    value R Q.subgroup A n →ₗ[R] value R P.subgroup A n :=
  (pullLinear (Subgroup.subgroupOfEquivOfLe hP).symm.toMonoidHom n).comp
    ((transfer (F.inclusionNativeIntersection (P := P) (Q := Q) x) n).hom.comp
      (pullLinear (F.inclusionNativeConjugation (P := P) (Q := Q) x) n))

theorem inclusion_rawPull_native (n : ℕ) :
    F.groupCohomologyRawPull (R := R) (A := A) (F.inclusion hP) n =
      (pullLinear (Subgroup.subgroupOfEquivOfLe hP).symm.toMonoidHom n).comp
        (pullLinear (P.subgroup.subgroupOf T.subgroup).subtype n) := by
  have he : (P.subgroup.subgroupOf T.subgroup).subtype.comp
      (Subgroup.subgroupOfEquivOfLe hP).symm.toMonoidHom = (F.inclusion hP).val := by
    ext y
    rfl
  change pullLinear _ n = _
  rw [← he, pullLinear_comp]

variable (n : ℕ)
    (hcomp : ∀ {P Q T : F.Object} (f : P ⟶ Q) (g : Q ⟶ T),
      F.groupCohomologyRawPush (nativeGroupCohomologyTransfer (R := R) (A := A) n) (f ≫ g) =
        (F.groupCohomologyRawPush (nativeGroupCohomologyTransfer n) g).comp
          (F.groupCohomologyRawPush (nativeGroupCohomologyTransfer n) f))

/-- Each genuine native double-coset term equals the corresponding concrete
fusion span operator; no term equality is supplied as an assumption. -/
theorem cohomologyFunctorDataOfPush_inclusionSpan_native (x : T.subgroup) :
    F.functorDataSpanOperator (F.cohomologyFunctorDataOfPush n hcomp)
      (F.inclusion hP) (F.inclusion hQ) x⁻¹ =
    F.nativeInclusionDoubleCosetTerm (R := R) (A := A) hP x n := by
  rw [F.cohomologyFunctorDataOfPush_inclusionSpan]
  exact (congrArg (fun m => m.comp
    (pullLinear (R := R) (A := A) (F.inclusionNativeConjugation (P := P) (Q := Q) x) n))
      (F.inclusionNativeIntersection_transfer (R := R) (A := A) hP hQ x n)).symm

end Sharpness.FusionSystem
