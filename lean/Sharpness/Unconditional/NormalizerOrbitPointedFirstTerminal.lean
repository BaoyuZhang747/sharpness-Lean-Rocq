import Sharpness.Unconditional.NormalizerOrbitPointedFirstImages
import Sharpness.Unconditional.NerveAdjunctionChains

/-! The actual terminal singleton in the isomorphism subcategory of the
first-entry undercategory. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
universe u

namespace Sharpness.FusionSystem
open CategoryTheory CategoryTheory.Limits
variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)
  (P : F.CentricOrbit) (A : F.NormalizerPointedSubgroup P)

def normalizerPointedFirstIsoPointArrow (X : F.NormalizerPointedFirstIso P A) :
    X ⟶ F.normalizerPointedFirstIsoBase P A := by
  letI : IsIso X.obj.hom := X.property
  let d := NormalizerPointedSubgroup.extensionData (inv X.obj.hom)
  have hi : (fun x : d.extension.carrier => (d.extension.extension.val x).val) ''
      {x | x.val ∈ X.obj.right.obj.right.chain.subgroup 0} = (A.subgroup : Set S) := by
    exact d.extension.carrier_image_eq.trans
      (congrArg (fun H : Subgroup S => (H : Set S))
        (NormalizerPointedSubgroup.arrowImage_eq_target_of_isIso (inv X.obj.hom)))
  let f := F.normalizerOrbitPointedToSingleton P A d.raw d.point_comm d.extension hi
  exact ObjectProperty.homMk (StructuredArrow.homMk f (Subsingleton.elim _ _))

def normalizerPointedFirstIsoBase_isTerminal : IsTerminal (F.normalizerPointedFirstIsoBase P A) :=
  IsTerminal.ofUniqueHom (F.normalizerPointedFirstIsoPointArrow P A) (by
    intro X f
    apply ObjectProperty.hom_ext
    exact Subsingleton.elim _ _)

def normalizerPointedFirstPointAdjunction :
    Functor.star.{u} (F.NormalizerPointedFirstIso P A) ⊣
      Functor.fromPUnit (F.normalizerPointedFirstIsoBase P A) :=
  Adjunction.mkOfHomEquiv {
    homEquiv := fun X Y => {
      toFun := fun _ => F.normalizerPointedFirstIsoPointArrow P A X
      invFun := fun _ => eqToHom (Subsingleton.elim _ _)
      left_inv := fun _ => Subsingleton.elim _ _
      right_inv := fun _ => by
        apply ObjectProperty.hom_ext
        exact Subsingleton.elim _ _ }
    homEquiv_naturality_left_symm := by intros; apply Subsingleton.elim
    homEquiv_naturality_right := by
      intros
      apply (F.normalizerPointedFirstIsoBase_isTerminal P A).hom_ext }

end Sharpness.FusionSystem
