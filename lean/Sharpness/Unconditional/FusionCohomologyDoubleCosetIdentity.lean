import Sharpness.Unconditional.FusionCohomologyDoubleCosetFormula
import Sharpness.Unconditional.InclusionMackeyBridge

/-! The actual inclusion Mackey identity on the native cohomology functor
data, obtained by reindexing the proved native cohomological identity. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness.FusionSystem
open CategoryTheory OrdinaryCohomology OrdinaryCohomology.MackeyDecomposition
open scoped BigOperators
variable {S R A : Type u} [Group S] [Finite S] [CommRing R]
    [AddCommGroup A] [Module R A] (F : FusionSystem S)

local instance nativeFusionDoubleCosetFintype (H K : Subgroup S) :
    Fintype (DoubleCoset.Quotient (H : Set S) K) := by
  unfold DoubleCoset.Quotient
  exact Fintype.ofFinite _

variable {P Q T : F.Object} (hP : P.subgroup ≤ T.subgroup) (hQ : Q.subgroup ≤ T.subgroup)

/-- The genuine native cohomology identity, with its inputs and output
transported to the literal manuscript subgroups P and Q. -/
theorem nativeInclusionDoubleCosetFormula (n : ℕ) :
    (F.groupCohomologyRawPull (R := R) (A := A) (F.inclusion hP) n).comp
      (F.groupCohomologyRawPush (nativeGroupCohomologyTransfer n) (F.inclusion hQ)) =
    ∑ d : DoubleCoset.Quotient (Q.subgroup.subgroupOf T.subgroup : Set T.subgroup)
      (P.subgroup.subgroupOf T.subgroup),
      F.nativeInclusionDoubleCosetTerm (Q := Q) hP d.out n := by
  let H := Q.subgroup.subgroupOf T.subgroup
  let K := P.subgroup.subgroupOf T.subgroup
  let eP := Subgroup.subgroupOfEquivOfLe hP
  let eQ := Subgroup.subgroupOfEquivOfLe hQ
  have hn := congrArg (fun f : value R H A n ⟶ value R K A n => f.hom)
    (transfer_pull_doubleCoset (R := R) (A := A) H K n)
  simp only [ModuleCat.hom_comp, ModuleCat.hom_sum] at hn
  rw [F.nativeGroupCohomologyRawPush_inclusion, F.inclusion_rawPull_native]
  apply LinearMap.ext
  intro z
  have hh := LinearMap.congr_fun hn (pullLinear eQ.toMonoidHom n z)
  have hh' := congrArg (pullLinear (R := R) (A := A) eP.symm.toMonoidHom n) hh
  refine hh'.trans ?_
  simp only [LinearMap.sum_apply, LinearMap.comp_apply, map_sum]
  apply Finset.sum_congr rfl
  intro d _
  change pullLinear eP.symm.toMonoidHom n
      ((transfer (intersection H K d.out) n).hom
        (pullLinear (intersectionConjugation H K d.out) n (pullLinear eQ.toMonoidHom n z))) =
    pullLinear eP.symm.toMonoidHom n
      ((transfer (intersection H K d.out) n).hom
        (pullLinear (F.inclusionNativeConjugation (P := P) (Q := Q) d.out) n z))
  rw [F.inclusionNativeConjugation_eq hQ d.out, pullLinear_comp]
  rfl

variable (n : ℕ)
    (hcomp : ∀ {P Q T : F.Object} (f : P ⟶ Q) (g : Q ⟶ T),
      F.groupCohomologyRawPush (nativeGroupCohomologyTransfer (R := R) (A := A) n) (f ≫ g) =
        (F.groupCohomologyRawPush (nativeGroupCohomologyTransfer n) g).comp
          (F.groupCohomologyRawPush (nativeGroupCohomologyTransfer n) f))

/-- Inclusion Mackey holds for the native functor data. The intermediate
parameter only certifies composition of the actual push maps. -/
theorem cohomologyFunctorDataOfPush_hasInclusionMackeyFormula :
    F.HasInclusionMackeyFormula (F.cohomologyFunctorDataOfPush n hcomp) := by
  intro P Q T hP hQ
  rw [F.cohomologyFunctorDataOfPush_pull_raw, F.cohomologyFunctorDataOfPush_push_raw,
    F.functorDataDoubleCosetOperator_sum_native hP hQ,
    F.nativeInclusionDoubleCosetFormula hP hQ n]
  exact Finset.sum_congr rfl (fun d _ =>
    (F.cohomologyFunctorDataOfPush_inclusionSpan_native hP hQ n hcomp d.out).symm)

end Sharpness.FusionSystem
