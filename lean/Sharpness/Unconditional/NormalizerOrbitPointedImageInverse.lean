import Sharpness.Unconditional.NormalizerOrbitPointedImageBasic
import Sharpness.Unconditional.CentralizerConstruction

/-! A subgroup extension with bijective acting map restricts to an actual
isomorphism of the source join with the target acting/image join. Its inverse
is again a genuine subgroup-extension witness. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
universe u

namespace Sharpness.FusionSystem.NormalizerSubgroupExtension
open CategoryTheory
variable {S : Type u} [Group S] {F : FusionSystem S}
  {P Q R T : Subgroup S} {f : (⟨P⟩ : F.Object) ⟶ ⟨Q⟩}
  (a : F.NormalizerSubgroupExtension R T f)

def joinHom : (⟨P ⊔ R⟩ : F.Object) ⟶ ⟨Q ⊔ a.image⟩ := by
  let g₀ := F.inclusion (sup_le a.acting_le a.subgroup_le) ≫ a.extension
  have hm : ∀ x, (g₀.val x).val ∈ Q ⊔ a.image := by
    apply join_image_mem g₀.val ((Q ⊔ a.image).subgroupOf ⊤)
    · intro x
      change (a.extension.val ⟨x.val, a.acting_le x.property⟩).val ∈ Q ⊔ a.image
      rw [a.onActing x]
      exact Subgroup.mem_sup_left (f.val x).property
    · intro x
      apply Subgroup.mem_sup_right
      exact (a.mem_image_iff _).mpr ⟨x, rfl⟩
  let g : (P ⊔ R : Subgroup S) →* (Q ⊔ a.image : Subgroup S) :=
    { toFun x := ⟨(g₀.val x).val, hm x⟩
      map_one' := by
        apply Subtype.ext
        exact congrArg (fun z : (⊤ : Subgroup S) => z.val) g₀.val.map_one
      map_mul' x y := by
        apply Subtype.ext
        exact congrArg (fun z : (⊤ : Subgroup S) => z.val) (g₀.val.map_mul x y) }
  exact ⟨g, F.codomain_restrict_mem g₀.val g₀.property le_top g (by ext x; rfl)⟩

theorem joinHom_onActing (x : P) :
    (a.joinHom.val ⟨x.val, Subgroup.mem_sup_left x.property⟩).val = (f.val x).val :=
  a.onActing x

theorem joinHom_onSubgroup (x : R) :
    (a.joinHom.val ⟨x.val, Subgroup.mem_sup_right x.property⟩).val =
      (a.extension.val ⟨x.val, a.subgroup_le x.property⟩).val := rfl

theorem joinHom_surjective (hf : Function.Surjective f.val) :
    Function.Surjective a.joinHom.val := by
  apply MonoidHom.range_eq_top.mp
  apply top_unique
  rw [← Subgroup.subgroupOf_self (Q ⊔ a.image),
    Subgroup.subgroupOf_sup (show Q ≤ Q ⊔ a.image from le_sup_left)
      (show a.image ≤ Q ⊔ a.image from le_sup_right)]
  apply sup_le
  · intro x hx
    obtain ⟨y, hy⟩ := hf ⟨x.val, hx⟩
    exact ⟨⟨y.val, Subgroup.mem_sup_left y.property⟩,
      Subtype.ext ((a.joinHom_onActing y).trans (congrArg Subtype.val hy))⟩
  · intro x hx
    obtain ⟨y, hy⟩ := (a.mem_image_iff x.val).mp hx
    exact ⟨⟨y.val, Subgroup.mem_sup_right y.property⟩, Subtype.ext hy⟩

def joinEquiv (hf : Function.Surjective f.val) :
    (P ⊔ R : Subgroup S) ≃* (Q ⊔ a.image : Subgroup S) :=
  MulEquiv.ofBijective a.joinHom.val ⟨F.injective _ a.joinHom.property, a.joinHom_surjective hf⟩

def actingEquiv (_a : F.NormalizerSubgroupExtension R T f)
    (hf : Function.Surjective f.val) : P ≃* Q :=
  MulEquiv.ofBijective f.val ⟨F.injective _ f.property, hf⟩

def inverseActing (hf : Function.Surjective f.val) : (⟨Q⟩ : F.Object) ⟶ ⟨P⟩ :=
  ⟨(a.actingEquiv hf).symm.toMonoidHom, F.inverse_mem (a.actingEquiv hf) f.property⟩

def inverse (hf : Function.Surjective f.val) :
    F.NormalizerSubgroupExtension a.image R (a.inverseActing hf) where
  carrier := Q ⊔ a.image
  acting_le := le_sup_left
  subgroup_le := le_sup_right
  extension := ⟨(a.joinEquiv hf).symm.toMonoidHom,
    F.inverse_mem (a.joinEquiv hf) a.joinHom.property⟩ ≫ F.inclusion le_top
  onActing y := by
    let x := (a.actingEquiv hf).symm y
    have he : a.joinEquiv hf ⟨x.val, Subgroup.mem_sup_left x.property⟩ =
        ⟨y.val, Subgroup.mem_sup_left y.property⟩ := by
      apply Subtype.ext
      exact (a.joinHom_onActing x).trans (congrArg Subtype.val ((a.actingEquiv hf).apply_symm_apply y))
    change ((a.joinEquiv hf).symm ⟨y.val, Subgroup.mem_sup_left y.property⟩).val = x.val
    rw [← he, MulEquiv.symm_apply_apply]
  maps z hz := by
    obtain ⟨x, hx⟩ := (a.mem_image_iff z.val).mp hz
    have he : a.joinEquiv hf ⟨x.val, Subgroup.mem_sup_right x.property⟩ = z := Subtype.ext hx
    change ((a.joinEquiv hf).symm z).val ∈ R
    rw [← he, MulEquiv.symm_apply_apply]
    exact x.property

end Sharpness.FusionSystem.NormalizerSubgroupExtension
