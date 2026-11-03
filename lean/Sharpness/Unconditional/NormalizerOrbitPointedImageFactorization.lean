import Sharpness.Unconditional.NormalizerOrbitPointedImageInverse
import Sharpness.Unconditional.NormalizerOrbitPointedImageIndependence
import Sharpness.Unconditional.NormalizerOrbitPointedImageComposition

/-! Genuine image factorization in the pointed normalized-subgroup category. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
universe u

namespace Sharpness.FusionSystem.NormalizerPointedSubgroup
open CategoryTheory
variable {S : Type u} [Group S] {F : FusionSystem S} {P : F.CentricOrbit}
  {A B : F.NormalizerPointedSubgroup P}

structure ExtensionData (f : A ⟶ B) where
  raw : A.centric.obj.as ⟶ B.centric.obj.as
  point_comm : A.point.hom ≫ ObjectProperty.homMk (F.toOrbit.map raw) = B.point.hom
  extension : F.NormalizerSubgroupExtension A.subgroup B.subgroup raw

def extensionData (f : A ⟶ B) : ExtensionData f := Classical.choice (by
  obtain ⟨g, hg, r, hr, ⟨a⟩⟩ := leOfHom f
  have heq : ObjectProperty.homMk (F.toOrbit.map r) = g := by
    apply ObjectProperty.hom_ext
    exact hr
  exact ⟨⟨r, by rw [heq]; exact hg, a⟩⟩)

theorem raw_surjective [Finite S] (A B : F.NormalizerPointedSubgroup P)
    (g : A.centric.obj.as ⟶ B.centric.obj.as) : Function.Surjective g.val := by
  apply ((Nat.bijective_iff_injective_and_card g.val).mpr ⟨F.injective _ g.property, ?_⟩).2
  exact le_antisymm (F.orbitOrder_mono (A.point.symm.trans B.point).hom.hom)
    (F.orbitOrder_mono (B.point.symm.trans A.point).hom.hom)

def arrowImage (f : A ⟶ B) : Subgroup S := (extensionData f).extension.image

theorem arrowImage_le (f : A ⟶ B) : arrowImage f ≤ B.subgroup :=
  (extensionData f).extension.image_le

def imageObject [Finite S] (f : A ⟶ B) : F.NormalizerPointedSubgroup P where
  centric := B.centric
  point := B.point
  subgroup := arrowImage f
  subgroup_centric := (extensionData f).extension.image_centric A.subgroup_centric
  normalizes := (extensionData f).extension.image_normalizes A.normalizes
    (raw_surjective A B (extensionData f).raw)

def toImage [Finite S] (f : A ⟶ B) : A ⟶ imageObject f :=
  homOfLE ⟨ObjectProperty.homMk (F.toOrbit.map (extensionData f).raw),
    (extensionData f).point_comm, (extensionData f).raw, rfl,
    ⟨(extensionData f).extension.toImage⟩⟩

def fromImage [Finite S] (f : A ⟶ B) : imageObject f ⟶ A := by
  let d := extensionData f
  let hf := raw_surjective A B d.raw
  let invRaw := d.extension.inverseActing hf
  let g : B.centric ⟶ A.centric := ObjectProperty.homMk (F.toOrbit.map invRaw)
  have hraw : d.raw ≫ invRaw = 𝟙 A.centric.obj.as := by
    apply Subtype.ext
    apply MonoidHom.ext
    intro x
    exact (d.extension.actingEquiv hf).symm_apply_apply x
  have hg : ObjectProperty.homMk (F.toOrbit.map d.raw) ≫ g = 𝟙 A.centric := by
    apply ObjectProperty.hom_ext
    change F.toOrbit.map d.raw ≫ F.toOrbit.map invRaw = 𝟙 A.centric.obj
    rw [← F.toOrbit.map_comp, hraw, F.toOrbit.map_id]
    rfl
  refine homOfLE ⟨g, ?_, invRaw, rfl, ⟨d.extension.inverse hf⟩⟩
  change B.point.hom ≫ g = A.point.hom
  rw [← d.point_comm, Category.assoc, hg, Category.comp_id]

def imageIso [Finite S] (f : A ⟶ B) : A ≅ imageObject f where
  hom := toImage f
  inv := fromImage f
  hom_inv_id := Subsingleton.elim _ _
  inv_hom_id := Subsingleton.elim _ _

def imageInclusion [Finite S] (f : A ⟶ B) : imageObject f ⟶ B := by
  refine homOfLE ⟨𝟙 B.centric, Category.comp_id _, 𝟙 B.centric.obj.as, F.toOrbit.map_id _, ⟨?_⟩⟩
  exact {
    carrier := B.centric.obj.as.subgroup ⊔ arrowImage f
    acting_le := le_sup_left
    subgroup_le := le_sup_right
    extension := F.inclusion le_top
    onActing := fun _ => rfl
    maps := fun _ hx => arrowImage_le f hx }

theorem image_factorization [Finite S] (f : A ⟶ B) :
    (imageIso f).hom ≫ imageInclusion f = f := Subsingleton.elim _ _

theorem extension_subgroup_card_le [Finite S]
    {Q R T U : Subgroup S} {g : (⟨Q⟩ : F.Object) ⟶ ⟨R⟩}
    (a : F.NormalizerSubgroupExtension T U g) : Nat.card T ≤ Nat.card U := by
  let k : T → U := fun x =>
    ⟨(a.extension.val ⟨x.val, a.subgroup_le x.property⟩).val, a.maps _ x.property⟩
  apply Nat.card_le_card_of_injective k
  intro x y hxy
  apply F.injective _ a.subgroupHom.property
  apply Subtype.ext
  exact congrArg (fun z : U => z.val) hxy

theorem extension_image_card [Finite S]
    {Q R T U : Subgroup S} {g : (⟨Q⟩ : F.Object) ⟶ ⟨R⟩}
    (a : F.NormalizerSubgroupExtension T U g) : Nat.card a.image = Nat.card T := by
  let k : T →* S := (⊤ : Subgroup S).subtype.comp a.subgroupHom.val
  let e := MonoidHom.ofInjective (f := k)
    (Subtype.val_injective.comp (F.injective _ a.subgroupHom.property))
  exact (Nat.card_congr e.toEquiv).symm

theorem arrowImage_eq_target_of_isIso [Finite S] (f : A ⟶ B) [IsIso f] :
    arrowImage f = B.subgroup := by
  apply Subgroup.eq_of_le_of_card_ge (arrowImage_le f)
  change Nat.card B.subgroup ≤ Nat.card (extensionData f).extension.image
  rw [extension_image_card]
  exact extension_subgroup_card_le (extensionData (inv f)).extension

theorem arrowImage_eq_extension [Finite S]
    (p : ℕ) [Fact p.Prime] (hS : IsPGroup p S) (sat : F.Saturated p)
    (f : A ⟶ B) (g : A.centric.obj.as ⟶ B.centric.obj.as)
    (hg : A.point.hom ≫ ObjectProperty.homMk (F.toOrbit.map g) = B.point.hom)
    (a : F.NormalizerSubgroupExtension A.subgroup B.subgroup g) :
    arrowImage f = a.image := by
  have he : ObjectProperty.homMk (F.toOrbit.map (extensionData f).raw) =
      (ObjectProperty.homMk (F.toOrbit.map g) : A.centric ⟶ B.centric) :=
    (cancel_epi A.point.hom).mp ((extensionData f).point_comm.trans hg.symm)
  exact NormalizerSubgroupExtension.image_eq_of_orbitEq p hS sat
    (extensionData f).extension a A.centric.property B.centric.property A.normalizes
    (raw_surjective A B _) (raw_surjective A B _) (congrArg (fun q => q.hom) he)

end Sharpness.FusionSystem.NormalizerPointedSubgroup
