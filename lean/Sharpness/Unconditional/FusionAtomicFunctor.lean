import Sharpness.Unconditional.FusionAtomicRepresentability
import Sharpness.Unconditional.AtomicSylowOrbit

/-! The normalizer-preimage functor from outer-automorphism p-orbits to
the centric fusion orbit category. Its maps are the extensions provided
by saturation, uniquely determined in the orbit category by centricity. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness.FusionSystem
open CategoryTheory

variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)
    (Q : Subgroup S) (p : ℕ) [Fact p.Prime]
    (hS : IsPGroup p S) (sat : F.Saturated p) (hQ : F.IsCentric Q)

abbrev AtomicNormalizerOrbit :=
  AtomicGroupOrbit.Below (p := p) (F.normalizerToOrbitAut Q).range

abbrev atomicPreimageInclusion (H : Subgroup (Aut (F.toOrbit.obj ⟨Q⟩))) :=
  F.toOrbit.map (F.inclusion (F.le_atomicNormalizerPreimage Q H))

def atomicTransporterFixed
    {A B : AtomicGroupOrbit.Object p (Aut (F.toOrbit.obj ⟨Q⟩))}
    (hB : B.subgroup ≤ (F.normalizerToOrbitAut Q).range) (g : A ⟶ B) :
    F.AtomicFixedMorphisms Q A.subgroup
      (F.toOrbit.obj ⟨F.atomicNormalizerPreimage Q B.subgroup⟩) :=
  ⟨g.val.inv ≫ F.atomicPreimageInclusion Q B.subgroup, by
    intro a ha
    have hb := F.atomicNormalizerPreimage_restriction_fixed Q B.subgroup hB
      (𝟙 (F.toOrbit.obj ⟨F.atomicNormalizerPreimage Q B.subgroup⟩))
      (g.property a ha)
    change (g.val.hom ≫ a.hom ≫ g.val.inv) ≫
      (F.atomicPreimageInclusion Q B.subgroup ≫ 𝟙 _) =
      F.atomicPreimageInclusion Q B.subgroup ≫ 𝟙 _ at hb
    have hh := congrArg (fun z => g.val.inv ≫ z) hb
    change a.hom ≫ (g.val.inv ≫ F.atomicPreimageInclusion Q B.subgroup) =
      g.val.inv ≫ F.atomicPreimageInclusion Q B.subgroup
    simpa only [Category.comp_id, Category.assoc, Iso.inv_hom_id_assoc] using hh⟩

def atomicTransporterExtension
    {A B : AtomicGroupOrbit.Object p (Aut (F.toOrbit.obj ⟨Q⟩))}
    (hA : A.subgroup ≤ (F.normalizerToOrbitAut Q).range)
    (hB : B.subgroup ≤ (F.normalizerToOrbitAut Q).range) (g : A ⟶ B) :
    F.toOrbit.obj ⟨F.atomicNormalizerPreimage Q A.subgroup⟩ ⟶
      F.toOrbit.obj ⟨F.atomicNormalizerPreimage Q B.subgroup⟩ :=
  (F.atomicFixedRestrictionEquiv Q A.subgroup p hS sat hQ hA _).symm
    (F.atomicTransporterFixed Q p hB g)

theorem atomicTransporterExtension_spec
    {A B : AtomicGroupOrbit.Object p (Aut (F.toOrbit.obj ⟨Q⟩))}
    (hA : A.subgroup ≤ (F.normalizerToOrbitAut Q).range)
    (hB : B.subgroup ≤ (F.normalizerToOrbitAut Q).range) (g : A ⟶ B) :
    F.atomicPreimageInclusion Q A.subgroup ≫
        F.atomicTransporterExtension Q p hS sat hQ hA hB g =
      g.val.inv ≫ F.atomicPreimageInclusion Q B.subgroup :=
  congrArg Subtype.val
    ((F.atomicFixedRestrictionEquiv Q A.subgroup p hS sat hQ hA _).apply_symm_apply _)

theorem atomicTransporterExtension_id
    (A : AtomicGroupOrbit.Object p (Aut (F.toOrbit.obj ⟨Q⟩)))
    (hA : A.subgroup ≤ (F.normalizerToOrbitAut Q).range) :
    F.atomicTransporterExtension Q p hS sat hQ hA hA (𝟙 A) = 𝟙 _ := by
  apply F.atomicFixedRestriction_injective Q A.subgroup p hS sat hQ hA _
  apply Subtype.ext
  change F.atomicPreimageInclusion Q A.subgroup ≫ _ = _
  rw [F.atomicTransporterExtension_spec]
  change 𝟙 _ ≫ _ = _ ≫ 𝟙 _
  simp

theorem atomicTransporterExtension_comp
    {A B C : AtomicGroupOrbit.Object p (Aut (F.toOrbit.obj ⟨Q⟩))}
    (hA : A.subgroup ≤ (F.normalizerToOrbitAut Q).range)
    (hB : B.subgroup ≤ (F.normalizerToOrbitAut Q).range)
    (hC : C.subgroup ≤ (F.normalizerToOrbitAut Q).range) (f : A ⟶ B) (g : B ⟶ C) :
    F.atomicTransporterExtension Q p hS sat hQ hA hC (f ≫ g) =
      F.atomicTransporterExtension Q p hS sat hQ hA hB f ≫
        F.atomicTransporterExtension Q p hS sat hQ hB hC g := by
  apply F.atomicFixedRestriction_injective Q A.subgroup p hS sat hQ hA _
  apply Subtype.ext
  change F.atomicPreimageInclusion Q A.subgroup ≫ _ =
    F.atomicPreimageInclusion Q A.subgroup ≫ (_ ≫ _)
  rw [F.atomicTransporterExtension_spec, ← Category.assoc,
    F.atomicTransporterExtension_spec, Category.assoc,
    F.atomicTransporterExtension_spec]
  exact Category.assoc _ _ _

theorem atomicTransporterExtension_eq_of_relation
    {A B : AtomicGroupOrbit.Object p (Aut (F.toOrbit.obj ⟨Q⟩))}
    (hA : A.subgroup ≤ (F.normalizerToOrbitAut Q).range)
    (hB : B.subgroup ≤ (F.normalizerToOrbitAut Q).range) (f g : A ⟶ B)
    (hfg : AtomicGroupOrbit.targetRelation f g) :
    F.atomicTransporterExtension Q p hS sat hQ hA hB f =
      F.atomicTransporterExtension Q p hS sat hQ hA hB g := by
  obtain ⟨b, hb⟩ := hfg
  apply F.atomicFixedRestriction_injective Q A.subgroup p hS sat hQ hA _
  apply Subtype.ext
  change F.atomicPreimageInclusion Q A.subgroup ≫ _ =
    F.atomicPreimageInclusion Q A.subgroup ≫ _
  rw [F.atomicTransporterExtension_spec, F.atomicTransporterExtension_spec, hb]
  have hk := F.atomicNormalizerPreimage_restriction_fixed Q B.subgroup hB
    (𝟙 (F.toOrbit.obj ⟨F.atomicNormalizerPreimage Q B.subgroup⟩))
    (B.subgroup.inv_mem b.property)
  change b.val.inv ≫ (_ ≫ 𝟙 _) = _ ≫ 𝟙 _ at hk
  simp only [Category.comp_id] at hk
  change f.val.inv ≫ _ = (f.val.inv ≫ b.val.inv) ≫ _
  rw [Category.assoc, hk]

def atomicOrbitRepresentative
    {A B : AtomicGroupOrbit.Orbit (p := p) (G := Aut (F.toOrbit.obj ⟨Q⟩))}
    (f : A ⟶ B) : A.as ⟶ B.as :=
  (AtomicGroupOrbit.toOrbit.map_surjective f).choose

theorem atomicOrbitRepresentative_map
    {A B : AtomicGroupOrbit.Orbit (p := p) (G := Aut (F.toOrbit.obj ⟨Q⟩))}
    (f : A ⟶ B) :
    AtomicGroupOrbit.toOrbit.map (F.atomicOrbitRepresentative Q p f) = f :=
  (AtomicGroupOrbit.toOrbit.map_surjective f).choose_spec

def atomicNormalizerFunctor : F.AtomicNormalizerOrbit Q p ⥤ F.CentricOrbit where
  obj A := ⟨F.toOrbit.obj ⟨F.atomicNormalizerPreimage Q A.obj.as.subgroup⟩,
    F.atomicNormalizerPreimage_centric Q A.obj.as.subgroup hQ⟩
  map {A B} f := ObjectProperty.homMk
    (F.atomicTransporterExtension Q p hS sat hQ A.property B.property
      (F.atomicOrbitRepresentative Q p f.hom))
  map_id A := by
    apply ObjectProperty.hom_ext
    change F.atomicTransporterExtension Q p hS sat hQ A.property A.property _ = 𝟙 _
    rw [← F.atomicTransporterExtension_id Q p hS sat hQ A.obj.as A.property]
    apply F.atomicTransporterExtension_eq_of_relation
    apply (AtomicGroupOrbit.orbit_map_eq_iff _ _).mp
    rw [F.atomicOrbitRepresentative_map, AtomicGroupOrbit.toOrbit.map_id]
    rfl
  map_comp {A B C} f g := by
    apply ObjectProperty.hom_ext
    change F.atomicTransporterExtension Q p hS sat hQ A.property C.property _ =
      F.atomicTransporterExtension Q p hS sat hQ A.property B.property _ ≫
        F.atomicTransporterExtension Q p hS sat hQ B.property C.property _
    rw [← F.atomicTransporterExtension_comp]
    apply F.atomicTransporterExtension_eq_of_relation
    apply (AtomicGroupOrbit.orbit_map_eq_iff _ _).mp
    rw [F.atomicOrbitRepresentative_map, AtomicGroupOrbit.toOrbit.map_comp,
      F.atomicOrbitRepresentative_map, F.atomicOrbitRepresentative_map]
    rfl

theorem atomicNormalizerFunctor_map_spec {A B : F.AtomicNormalizerOrbit Q p}
    (f : A ⟶ B) :
    F.atomicPreimageInclusion Q A.obj.as.subgroup ≫
        ((F.atomicNormalizerFunctor Q p hS sat hQ).map f).hom =
      (F.atomicOrbitRepresentative Q p f.hom).val.inv ≫
        F.atomicPreimageInclusion Q B.obj.as.subgroup :=
  F.atomicTransporterExtension_spec Q p hS sat hQ A.property B.property _

end Sharpness.FusionSystem
