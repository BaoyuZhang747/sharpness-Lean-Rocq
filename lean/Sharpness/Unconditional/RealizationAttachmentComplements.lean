import Sharpness.Unconditional.RealizationAttachmentNeighborhood

/-! Actual homeomorphisms on the complementary opens and their intersections
with the attachment neighborhoods. Their forward maps are the pushout leg. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
universe u
namespace Sharpness.AttachmentHomotopy
open CategoryTheory CategoryTheory.Limits Topology

variable {A N B X Y : TopCat.{u}} {i : A ⟶ B} {l : A ⟶ X} {r : B ⟶ Y} {b : X ⟶ Y}
    (h : IsPushout i l r b) (hi : IsClosedEmbedding i)

def attachmentComplementHomeo : ↥((Set.range i)ᶜ) ≃ₜ ↥((Set.range b)ᶜ) :=
  RealizationSeparation.pushoutComplementHomeo h.flip hi

@[simp] theorem attachmentComplementHomeo_apply_val (x : ↥((Set.range i)ᶜ)) :
    (attachmentComplementHomeo h hi x).val = r x.val := rfl

include h hi in
theorem attachmentComplement_mapsTo : Set.MapsTo r (Set.range i)ᶜ (Set.range b)ᶜ :=
  fun x hx => (attachmentComplementHomeo h hi ⟨x, hx⟩).property

variable (a : A ⟶ N) (e : N ⟶ B) (w : a ≫ e = i) (he : IsOpenEmbedding e)

def attachmentComplementIntersectionHomeo :
    ↥((Set.range i)ᶜ ∩ Set.range e) ≃ₜ
      ↥((Set.range b)ᶜ ∩ attachmentNeighborhood h a e w) where
  toFun x := ⟨r x.val, attachmentComplement_mapsTo h hi x.property.1,
    attachmentNeighborhood_mapsTo h a e w he x.property.2⟩
  invFun y :=
    let z := (attachmentComplementHomeo h hi).symm ⟨y.val, y.property.1⟩
    ⟨z.val, z.property, by
      rw [← attachmentNeighborhood_preimage h a e w he]
      have hz : r z.val = y.val := congrArg Subtype.val
        ((attachmentComplementHomeo h hi).apply_symm_apply ⟨y.val, y.property.1⟩)
      change r z.val ∈ attachmentNeighborhood h a e w
      rw [hz]
      exact y.property.2⟩
  left_inv x := by
    apply Subtype.ext
    exact congrArg (fun z : ↥((Set.range i)ᶜ) => z.val)
      ((attachmentComplementHomeo h hi).symm_apply_apply ⟨x.val, x.property.1⟩)
  right_inv y := by
    apply Subtype.ext
    exact congrArg (fun z : ↥((Set.range b)ᶜ) => z.val)
      ((attachmentComplementHomeo h hi).apply_symm_apply ⟨y.val, y.property.1⟩)
  continuous_toFun := (r.hom.continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.comp
    ((attachmentComplementHomeo h hi).symm.continuous.comp
      (continuous_subtype_val.subtype_mk (fun y => y.property.1)))).subtype_mk _

@[simp] theorem attachmentComplementIntersectionHomeo_apply_val
    (x : ↥((Set.range i)ᶜ ∩ Set.range e)) :
    (attachmentComplementIntersectionHomeo h hi a e w he x).val = r x.val := rfl

end Sharpness.AttachmentHomotopy
