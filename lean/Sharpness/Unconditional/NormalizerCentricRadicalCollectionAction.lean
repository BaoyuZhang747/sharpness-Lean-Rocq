import Sharpness.Unconditional.FusionSystemGroupTransportFinite
import Sharpness.Unconditional.FusionAtomicNormalizer

/-! The ambient normalizer acts onto the actual orbit automorphism group
for fusion induced on the literal source of an injective embedding. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
universe u v
namespace Sharpness
open CategoryTheory
variable {A : Type u} {G : Type v} [Group A] [Group G]

def embeddedSubgroupEquiv (i : A →* G) (hi : Function.Injective i) (P : Subgroup A) :
    P ≃* P.map i := P.equivMapOfInjective i hi

@[simp] theorem embeddedSubgroupEquiv_symm_apply (i : A →* G) (hi : Function.Injective i)
    (P : Subgroup A) (x : P.map i) :
    i ((embeddedSubgroupEquiv i hi P).symm x).val = x.val :=
  congrArg Subtype.val ((embeddedSubgroupEquiv i hi P).apply_symm_apply x)

def embeddedNormalizerAction (i : A →* G) (hi : Function.Injective i) (P : Subgroup A) :
    Subgroup.normalizer (P.map i : Set G) →* MulAut P where
  toFun n := (embeddedSubgroupEquiv i hi P).trans
    (((P.map i).normalizerMonoidHom n).trans (embeddedSubgroupEquiv i hi P).symm)
  map_one' := by ext x; simp
  map_mul' a b := by ext x; simp

@[simp] theorem embeddedNormalizerAction_apply (i : A →* G) (hi : Function.Injective i)
    (P : Subgroup A) (n : Subgroup.normalizer (P.map i : Set G)) (x : P) :
    i (embeddedNormalizerAction i hi P n x).val = n.val * i x.val * n.val⁻¹ := by
  change i ((embeddedSubgroupEquiv i hi P).symm
    ((P.map i).normalizerMonoidHom n (embeddedSubgroupEquiv i hi P x))).val = _
  rw [embeddedSubgroupEquiv_symm_apply]
  rfl

theorem embeddedNormalizerAction_allowed (i : A →* G) (hi : Function.Injective i)
    (P : Subgroup A) (n : Subgroup.normalizer (P.map i : Set G)) :
    (finiteGroupFusionAlong i hi).IsHom (embeddedNormalizerAction i hi P n).toMonoidHom :=
  (finiteGroupFusionAlong_isHom_iff i hi _).mpr ⟨n.val, embeddedNormalizerAction_apply i hi P n⟩

theorem embedded_automorphism_witness_normalizes (i : A →* G) (hi : Function.Injective i)
    (P : Subgroup A) (a : P ≃* P) (g : G)
    (hg : ∀ x : P, i (a x).val = g * i x.val * g⁻¹) :
    g ∈ Subgroup.normalizer (P.map i : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  apply le_antisymm
  · rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨(a ⟨x, hx⟩).val, (a ⟨x, hx⟩).property, hg ⟨x, hx⟩⟩
  · rintro _ ⟨x, hx, rfl⟩
    let y := a.symm ⟨x, hx⟩
    refine ⟨i y.val, ⟨y.val, y.property, rfl⟩, ?_⟩
    change g * i y.val * g⁻¹ = i x
    rw [← hg y]
    exact congrArg (fun z : P => i z.val) (a.apply_symm_apply ⟨x, hx⟩)

variable [Finite A]

def embeddedNormalizerToAut (i : A →* G) (hi : Function.Injective i) (P : Subgroup A) :
    Subgroup.normalizer (P.map i : Set G) →* (finiteGroupFusionAlong i hi).automorphismSubgroup P :=
  (embeddedNormalizerAction i hi P).codRestrict _ (embeddedNormalizerAction_allowed i hi P)

theorem embeddedNormalizerToAut_surjective (i : A →* G) (hi : Function.Injective i)
    (P : Subgroup A) : Function.Surjective (embeddedNormalizerToAut i hi P) := by
  intro a
  obtain ⟨g, hg⟩ := (finiteGroupFusionAlong_isHom_iff i hi _).mp a.property
  refine ⟨⟨g, embedded_automorphism_witness_normalizes i hi P a.val g hg⟩, ?_⟩
  apply Subtype.ext
  ext x
  apply hi
  exact (embeddedNormalizerAction_apply i hi P _ x).trans (hg x).symm

def embeddedNormalizerToOrbitAut (i : A →* G) (hi : Function.Injective i) (P : Subgroup A) :
    Subgroup.normalizer (P.map i : Set G) →*
      Aut ((finiteGroupFusionAlong i hi).toOrbit.obj ⟨P⟩) :=
  ((finiteGroupFusionAlong i hi).automorphismToOrbitAut P).comp (embeddedNormalizerToAut i hi P)

theorem embeddedNormalizerToOrbitAut_surjective (i : A →* G) (hi : Function.Injective i)
    (P : Subgroup A) : Function.Surjective (embeddedNormalizerToOrbitAut i hi P) :=
  ((finiteGroupFusionAlong i hi).automorphismToOrbitAut_surjective P).comp
    (embeddedNormalizerToAut_surjective i hi P)

theorem embeddedNormalizerToOrbitAut_inner (i : A →* G) (hi : Function.Injective i)
    (P : Subgroup A) (n : Subgroup.normalizer (P : Set A))
    (hn : i n.val ∈ Subgroup.normalizer (P.map i : Set G)) :
    embeddedNormalizerToOrbitAut i hi P ⟨i n.val, hn⟩ =
      (finiteGroupFusionAlong i hi).normalizerToOrbitAut P n := by
  apply Iso.ext
  change (finiteGroupFusionAlong i hi).toOrbit.map _ = (finiteGroupFusionAlong i hi).toOrbit.map _
  congr 1
  apply Subtype.ext
  ext x
  apply hi
  change i (embeddedNormalizerAction i hi P ⟨i n.val, hn⟩ x).val =
    i (P.normalizerMonoidHom n x).val
  rw [embeddedNormalizerAction_apply]
  change i n.val * i x.val * (i n.val)⁻¹ = i (n.val * x.val * n.val⁻¹)
  simp

end Sharpness
