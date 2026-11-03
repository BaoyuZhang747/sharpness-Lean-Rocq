import Sharpness.Unconditional.NormalizerOrbitPointedSubgroups
import Sharpness.Unconditional.NormalizerOrbitCommaImageCoreflection

/-! Actual first-entry evaluation from pointed normalized chains to pointed
normalized subgroups. Its cofinality is a separate comparison. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness.FusionSystem
open CategoryTheory
variable {S : Type u} [Group S] (F : FusionSystem S) (P : F.CentricOrbit)

def normalizerOrbitPointedFirst :
    F.NormalizerOrbitPointed P ⥤ F.NormalizerPointedSubgroup P where
  obj X := {
    centric := X.obj.right.centric
    point := by
      letI : IsIso X.obj.hom := X.property
      exact asIso X.obj.hom
    subgroup := X.obj.right.chain.subgroup 0
    subgroup_centric := X.obj.right.chain.centric 0
    normalizes := X.obj.right.normalizes 0 }
  map {X Y} f := by
    refine homOfLE ⟨f.hom.right.val,StructuredArrow.w f.hom,?_⟩
    obtain ⟨g,hg,⟨a⟩⟩ := f.hom.right.property
    refine ⟨g,hg,⟨{
      carrier := a.carrier
      acting_le := a.acting_le
      subgroup_le := (X.obj.right.chain.subgroup_mono (Fin.zero_le _)).trans a.chain_le
      extension := a.extension
      onActing := a.onActing
      maps := ?_ }⟩⟩
    intro x hx
    change (a.extension.val x).val ∈ (_ : Set S)
    rw [← a.images 0]
    exact ⟨x,X.obj.right.chain.subgroup_mono (Fin.zero_le _) hx,rfl⟩

end Sharpness.FusionSystem
