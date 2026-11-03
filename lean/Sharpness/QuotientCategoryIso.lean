import Sharpness.QuotientActualCollection
import Mathlib.CategoryTheory.IsoCat

/-! The strict category isomorphism stated in Lemma 3.1. The two
previous fully faithful comparisons are also bijective on their actual
objects, and hence have strict inverses. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem
open CategoryTheory
variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)
    {Z : Subgroup S} [Z.Normal] (hZ : F.CentralSubgroup Z)
    (p : ℕ) [Fact p.Prime] (hS : IsPGroup p S) (sat : F.Saturated p)
    (I : F.AKOQuotientInput (p := p) hZ hS sat)

theorem quotientLiftToCollection_obj_bijective :
    Function.Bijective (F.quotientLiftToCollection hZ p hS sat I).obj := by
  constructor
  · rintro ⟨⟨A⟩,hA⟩ ⟨⟨B⟩,hB⟩ h
    have hp : F.quotientPreimage Z A = F.quotientPreimage Z B :=
      congrArg (fun P : (F.quotientComparisonCollection p hS sat hZ I).Orbit => P.obj.as.subgroup) h
    have hab : A = B :=
      (F.quotientPreimage_image A).symm.trans
        ((congrArg (fun P : Subgroup S => P.map (QuotientGroup.mk' Z)) hp).trans
          (F.quotientPreimage_image B))
    cases hab
    rfl
  · rintro ⟨⟨⟨P⟩⟩,hP⟩
    refine ⟨⟨⟨P.map (QuotientGroup.mk' Z)⟩,hP.2⟩, ?_⟩
    apply ObjectProperty.FullSubcategory.ext
    change F.toOrbit.obj ⟨F.quotientPreimage Z (P.map (QuotientGroup.mk' Z))⟩ = F.toOrbit.obj ⟨P⟩
    rw [F.quotientPreimage_map hP.1]

instance quotientLiftToCollection_isIso : (F.quotientLiftToCollection hZ p hS sat I).IsIso where
  bijective_obj := F.quotientLiftToCollection_obj_bijective hZ p hS sat I

theorem quotientCentricFunctor_obj_injective :
    Function.Injective (F.quotientCentricFunctor hZ p hS sat I).obj := by
  rintro ⟨⟨A⟩,hA⟩ ⟨⟨B⟩,hB⟩ h
  have hab : A = B := congrArg (fun P : I.system.CentricOrbit => P.obj.as.subgroup) h
  cases hab
  rfl

instance quotientCentricFunctor_isIso : (F.quotientCentricFunctor hZ p hS sat I).IsIso where
  bijective_obj := ⟨F.quotientCentricFunctor_obj_injective hZ p hS sat I,
    F.quotientCentricFunctor_obj_surjective hZ p hS sat I⟩

def quotientActualCentricIsoCat :
    IsoCat (F.quotientComparisonCollection p hS sat hZ I).Orbit I.system.CentricOrbit :=
  (F.quotientLiftToCollection hZ p hS sat I).asIsomorphism.symm.trans
    (F.quotientCentricFunctor hZ p hS sat I).asIsomorphism

/-- On every actual full preimage, the forward functor is precisely
the already constructed quotient functor, with its induced morphisms. -/
theorem quotientActualCentricIsoCat_forward :
    F.quotientLiftToCollection hZ p hS sat I ⋙ (F.quotientActualCentricIsoCat hZ p hS sat I).functor =
      F.quotientCentricFunctor hZ p hS sat I := by
  let J := F.quotientLiftToCollection hZ p hS sat I
  let q := F.quotientCentricFunctor hZ p hS sat I
  change J ⋙ (J.strictInv ⋙ q) = q
  exact (CategoryTheory.Functor.assoc J J.strictInv q).symm.trans
    ((congrArg (fun K => K ⋙ q) J.asIsomorphism.unit_eq.symm).trans
      (CategoryTheory.Functor.id_comp q))

end Sharpness.FusionSystem
