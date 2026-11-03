import Sharpness.Unconditional.NormalizerOrbitPointedImageFactorization

/-! Image-surjectivity detects pointed-subgroup isomorphisms. Precomposing
with an actual isomorphism preserves the literal chosen subgroup image. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
universe u

namespace Sharpness.FusionSystem.NormalizerPointedSubgroup
open CategoryTheory
variable {S : Type u} [Group S] [Finite S] {F : FusionSystem S} {P : F.CentricOrbit}
  {A B C : F.NormalizerPointedSubgroup P}

def imageInclusionIso (f : A ⟶ B) (h : arrowImage f = B.subgroup) : imageObject f ≅ B where
  hom := imageInclusion f
  inv := homOfLE ⟨𝟙 B.centric, Category.comp_id _, 𝟙 B.centric.obj.as, F.toOrbit.map_id _, ⟨{
    carrier := B.centric.obj.as.subgroup ⊔ B.subgroup
    acting_le := le_sup_left
    subgroup_le := le_sup_right
    extension := F.inclusion le_top
    onActing := fun _ => rfl
    maps := by
      intro x hx
      change x.val ∈ arrowImage f
      rw [h]
      exact hx }⟩⟩
  hom_inv_id := Subsingleton.elim _ _
  inv_hom_id := Subsingleton.elim _ _

theorem isIso_of_arrowImage_eq_target (f : A ⟶ B) (h : arrowImage f = B.subgroup) :
    IsIso f := by
  letI : IsIso (imageInclusion f) := (imageInclusionIso f h).isIso_hom
  rw [← image_factorization f]
  infer_instance

theorem isIso_iff_arrowImage_eq_target (f : A ⟶ B) :
    IsIso f ↔ arrowImage f = B.subgroup :=
  ⟨fun _ => arrowImage_eq_target_of_isIso f, isIso_of_arrowImage_eq_target f⟩

theorem arrowImage_comp_of_isIso (p : ℕ) [Fact p.Prime]
    (hS : IsPGroup p S) (sat : F.Saturated p)
    (f : A ⟶ B) [IsIso f] (g : B ⟶ C) :
    arrowImage (f ≫ g) = arrowImage g := by
  let a := extensionData f
  let b := extensionData g
  have heq : (ObjectProperty.homMk (F.toOrbit.map (a.raw ≫ b.raw)) : A.centric ⟶ C.centric) =
      ObjectProperty.homMk (F.toOrbit.map a.raw) ≫ ObjectProperty.homMk (F.toOrbit.map b.raw) := by
    apply ObjectProperty.hom_ext
    exact F.toOrbit.map_comp a.raw b.raw
  have hpoint : A.point.hom ≫ ObjectProperty.homMk (F.toOrbit.map (a.raw ≫ b.raw)) =
      C.point.hom := by
    rw [heq, ← Category.assoc, a.point_comm, b.point_comm]
  rw [arrowImage_eq_extension p hS sat (f ≫ g) (a.raw ≫ b.raw) hpoint (a.extension.comp b.extension)]
  exact NormalizerSubgroupExtension.image_comp_eq_of_image_eq a.extension b.extension
    (arrowImage_eq_target_of_isIso f)

end Sharpness.FusionSystem.NormalizerPointedSubgroup
