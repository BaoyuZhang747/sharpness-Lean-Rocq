import Sharpness.Unconditional.NormalizerOrbitPointedFirstCategories
import Sharpness.Unconditional.NormalizerOrbitPointedImageCarrier

/-! The actual image law needed by the first-entry comma prefix construction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
universe u

namespace Sharpness.FusionSystem
open CategoryTheory
variable {S : Type u} [Group S] {F : FusionSystem S}

namespace NormalizerChainExtension
variable {P Q : Subgroup S} {τ σ : F.CentricChain}
  {f : (⟨P⟩ : F.Object) ⟶ ⟨Q⟩}

def firstSubgroupExtension (a : F.NormalizerChainExtension τ σ f) :
    F.NormalizerSubgroupExtension (τ.subgroup 0) (σ.subgroup 0) f where
  carrier := a.carrier
  acting_le := a.acting_le
  subgroup_le := (τ.subgroup_mono (Fin.zero_le _)).trans a.chain_le
  extension := a.extension
  onActing := a.onActing
  maps x hx := by
    change (a.extension.val x).val ∈ (σ.subgroup 0 : Set S)
    rw [← a.images 0]
    exact ⟨x,τ.subgroup_mono (Fin.zero_le _) hx,rfl⟩

end NormalizerChainExtension

variable [Finite S] (F) (p : ℕ) [Fact p.Prime] (hS : IsPGroup p S)
  (sat : F.Saturated p) (P : F.CentricOrbit)

include hS sat

theorem normalizerPointedFirst_image_eq_extension {X Y : F.NormalizerOrbitPointed P}
    (f : X ⟶ Y) (g : X.obj.right.centric.obj.as ⟶ Y.obj.right.centric.obj.as)
    (hg : F.toOrbit.map g = f.hom.right.val.hom)
    (a : F.NormalizerChainExtension X.obj.right.chain Y.obj.right.chain g) :
    NormalizerPointedSubgroup.arrowImage ((F.normalizerOrbitPointedFirst P).map f) =
      a.firstSubgroupExtension.image := by
  refine NormalizerPointedSubgroup.arrowImage_eq_extension
    (A := (F.normalizerOrbitPointedFirst P).obj X)
    (B := (F.normalizerOrbitPointedFirst P).obj Y)
    p hS sat ((F.normalizerOrbitPointedFirst P).map f) g ?_ a.firstSubgroupExtension
  change X.obj.hom ≫ ObjectProperty.homMk (F.toOrbit.map g) = Y.obj.hom
  have he : (ObjectProperty.homMk (F.toOrbit.map g) : X.obj.right.centric ⟶ Y.obj.right.centric) =
      f.hom.right.val := by
    apply ObjectProperty.hom_ext
    exact hg
  rw [he]
  exact StructuredArrow.w f.hom

theorem normalizerPointedFirst_under_carrier_image
    {A : F.NormalizerPointedSubgroup P}
    (Y : F.NormalizerPointedFirstIso P A) (X : F.NormalizerPointedFirstUnder P A)
    (f : Y.obj ⟶ X)
    (g : Y.obj.right.obj.right.centric.obj.as ⟶ X.right.obj.right.centric.obj.as)
    (hg : F.toOrbit.map g = f.right.hom.right.val.hom)
    (a : F.NormalizerChainExtension Y.obj.right.obj.right.chain X.right.obj.right.chain g) :
    (fun x : a.carrier => (a.extension.val x).val) ''
      {x | x.val ∈ Y.obj.right.obj.right.chain.subgroup 0} =
        (NormalizerPointedSubgroup.arrowImage X.hom : Set S) := by
  letI : IsIso Y.obj.hom := Y.property
  have hi : NormalizerPointedSubgroup.arrowImage X.hom = a.firstSubgroupExtension.image := by
    rw [← StructuredArrow.w f,
      NormalizerPointedSubgroup.arrowImage_comp_of_isIso p hS sat]
    exact F.normalizerPointedFirst_image_eq_extension p hS sat P f.right g hg a
  exact a.firstSubgroupExtension.carrier_image_eq.trans (congrArg (fun H : Subgroup S => (H : Set S)) hi.symm)

end Sharpness.FusionSystem
