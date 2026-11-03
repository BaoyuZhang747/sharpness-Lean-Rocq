import Sharpness.Unconditional.NormalizerOrbitExtensions

/-! A pointed normalized-subgroup enlargement category. Extensions need only
carry the chosen subgroup into the target. Its arrows retain the actual
fusion-extension existence condition. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness.FusionSystem
open CategoryTheory
variable {S : Type u} [Group S] (F : FusionSystem S)

structure NormalizerSubgroupExtension {P Q : Subgroup S} (R T : Subgroup S)
    (f : (⟨P⟩ : F.Object) ⟶ ⟨Q⟩) where
  carrier : Subgroup S
  acting_le : P ≤ carrier
  subgroup_le : R ≤ carrier
  extension : (⟨carrier⟩ : F.Object) ⟶ ⟨⊤⟩
  onActing : ∀ x : P, (extension.val ⟨x.val,acting_le x.property⟩).val = (f.val x).val
  maps : ∀ x : carrier, x.val ∈ R → (extension.val x).val ∈ T

namespace NormalizerSubgroupExtension
variable {F} {P Q U R T V : Subgroup S}

def identity (P R : Subgroup S) : F.NormalizerSubgroupExtension R R (𝟙 (⟨P⟩ : F.Object)) where
  carrier := P ⊔ R
  acting_le := le_sup_left
  subgroup_le := le_sup_right
  extension := F.inclusion le_top
  onActing _ := rfl
  maps _ h := h

def comp {f : (⟨P⟩ : F.Object) ⟶ ⟨Q⟩} {g : (⟨Q⟩ : F.Object) ⟶ ⟨U⟩}
    (a : F.NormalizerSubgroupExtension R T f) (b : F.NormalizerSubgroupExtension T V g) :
    F.NormalizerSubgroupExtension R V (f ≫ g) where
  carrier := F.extensionPreimage a.extension b.carrier
  acting_le := by
    intro x hx
    apply (F.extensionPreimage_mem a.extension b.carrier ⟨x,a.acting_le hx⟩).mpr
    rw [a.onActing ⟨x,hx⟩]
    exact b.acting_le (f.val ⟨x,hx⟩).property
  subgroup_le := by
    intro x hx
    exact (F.extensionPreimage_mem a.extension b.carrier ⟨x,a.subgroup_le hx⟩).mpr
      (b.subgroup_le (a.maps _ hx))
  extension := F.extensionPreimageMap a.extension b.carrier ≫ b.extension
  onActing x := by
    change (b.extension.val ((F.extensionPreimageMap a.extension b.carrier).val _)).val = _
    have he : (F.extensionPreimageMap a.extension b.carrier).val
        ⟨x.val,by
          apply (F.extensionPreimage_mem a.extension b.carrier ⟨x.val,a.acting_le x.property⟩).mpr
          rw [a.onActing x]
          exact b.acting_le (f.val x).property⟩ =
        ⟨(f.val x).val,b.acting_le (f.val x).property⟩ := by
      apply Subtype.ext
      exact a.onActing x
    rw [he]
    exact b.onActing (f.val x)
  maps x hx := b.maps _ (a.maps
    ⟨x.val,F.extensionPreimage_le a.extension b.carrier x.property⟩ hx)

end NormalizerSubgroupExtension

structure NormalizerPointedSubgroup (P : F.CentricOrbit) where
  centric : F.CentricOrbit
  point : P ≅ centric
  subgroup : Subgroup S
  subgroup_centric : F.IsCentric subgroup
  normalizes : centric.obj.as.subgroup ≤ Subgroup.normalizer (subgroup : Set S)

namespace NormalizerPointedSubgroup
variable {F} {P : F.CentricOrbit}

def Related (A B : F.NormalizerPointedSubgroup P) : Prop :=
  ∃ f : A.centric ⟶ B.centric, A.point.hom ≫ f = B.point.hom ∧
    ∃ g : A.centric.obj.as ⟶ B.centric.obj.as,
      F.toOrbit.map g = f.hom ∧ Nonempty (F.NormalizerSubgroupExtension A.subgroup B.subgroup g)

theorem related_refl (A : F.NormalizerPointedSubgroup P) : Related A A :=
  ⟨𝟙 _,Category.comp_id _,𝟙 _,F.toOrbit.map_id _,⟨NormalizerSubgroupExtension.identity _ _⟩⟩

theorem related_trans {A B C : F.NormalizerPointedSubgroup P}
    (h : Related A B) (k : Related B C) : Related A C := by
  obtain ⟨f,hf,f₀,hf₀,⟨a⟩⟩ := h
  obtain ⟨g,hg,g₀,hg₀,⟨b⟩⟩ := k
  refine ⟨f ≫ g,?_,f₀ ≫ g₀,?_,⟨a.comp b⟩⟩
  · rw [← Category.assoc,hf,hg]
  · rw [F.toOrbit.map_comp,hf₀,hg₀]
    rfl

instance : Preorder (F.NormalizerPointedSubgroup P) where
  le := Related
  le_refl := related_refl
  le_trans _ _ _ := related_trans

instance : SmallCategory (F.NormalizerPointedSubgroup P) := Preorder.smallCategory _

end NormalizerPointedSubgroup
end Sharpness.FusionSystem
