import Sharpness.Unconditional.RealizationAttachmentHomotopy
import Mathlib.Topology.Homotopy.Equiv

/-! A boundary-fixed deformation retraction descends through an actual
attachment pushout. All homotopies are continuous on the actual pushout. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness.AttachmentHomotopy
open CategoryTheory CategoryTheory.Limits

variable {A N X P : TopCat.{u}} {a : A ⟶ N} {l : A ⟶ X} {r : N ⟶ P} {b : X ⟶ P}
    (h : IsPushout a l r b) (q : N ⟶ A) (hq : a ≫ q = 𝟙 A)

def attachmentRetraction : P ⟶ X :=
  h.desc (q ≫ l) (𝟙 X) (by rw [← Category.assoc, hq, Category.id_comp, Category.comp_id])

@[reassoc] theorem attachmentRetraction_inl :
    r ≫ attachmentRetraction h q hq = q ≫ l := h.inl_desc _ _ _

@[reassoc] theorem attachmentRetraction_inr :
    b ≫ attachmentRetraction h q hq = 𝟙 X := h.inr_desc _ _ _

def attachmentDeformation
    (H : TopCat.Homotopy (𝟙 N) (q ≫ a))
    (hfix : ∀ (s : unitInterval) (x : A), H (s, a x) = a x) :
    TopCat.Homotopy (𝟙 P) (attachmentRetraction h q hq ≫ b) := by
  let HB : TopCat.Homotopy (r ≫ 𝟙 P) (r ≫ attachmentRetraction h q hq ≫ b) :=
    { toFun := fun p => r (H p)
      continuous_toFun := r.hom.continuous.comp H.continuous
      map_zero_left := fun x => congrArg r (H.map_zero_left x)
      map_one_left := by
        intro x
        have hH : H (1, x) = a (q x) := H.map_one_left x
        rw [hH]
        have hr := ConcreteCategory.congr_hom (attachmentRetraction_inl h q hq) x
        have hw := ConcreteCategory.congr_hom h.w (q x)
        change r (a (q x)) = b (attachmentRetraction h q hq (r x))
        change attachmentRetraction h q hq (r x) = l (q x) at hr
        rw [hr]
        exact hw }
  let HC : TopCat.Homotopy (b ≫ 𝟙 P) (b ≫ attachmentRetraction h q hq ≫ b) :=
    { toFun := fun p => b p.2
      continuous_toFun := b.hom.continuous.comp continuous_snd
      map_zero_left := fun _ => rfl
      map_one_left := by
        intro x
        have hb := ConcreteCategory.congr_hom (attachmentRetraction_inr h q hq) x
        exact congrArg b hb.symm }
  exact pushoutHomotopy h HB HC (by
    intro s x
    change r (H (s, a x)) = b (l x)
    rw [hfix]
    exact ConcreteCategory.congr_hom h.w x)

def attachmentHomotopyEquiv
    (H : TopCat.Homotopy (𝟙 N) (q ≫ a))
    (hfix : ∀ (s : unitInterval) (x : A), H (s, a x) = a x) :
    ContinuousMap.HomotopyEquiv X P where
  toFun := b.hom
  invFun := (attachmentRetraction h q hq).hom
  left_inv := by
    change (b ≫ attachmentRetraction h q hq).hom.Homotopic (ContinuousMap.id X)
    rw [attachmentRetraction_inr]
    exact ContinuousMap.Homotopic.refl _
  right_inv := ⟨(attachmentDeformation h q hq H hfix).symm⟩

end Sharpness.AttachmentHomotopy
