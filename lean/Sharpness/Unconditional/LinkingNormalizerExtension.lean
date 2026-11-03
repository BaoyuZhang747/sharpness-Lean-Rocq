import Sharpness.Unconditional.NormalizerHigherLimitComparisonGroupsRepresentatives
import Sharpness.Unconditional.FusionAtomicExtension

/-! Exact extensions of a prescribed linking automorphism. Saturation supplies
an ambient fusion extension, and the central-fibre axiom corrects its lift. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness.FusionSystem.CentricLinkingSystem
open CategoryTheory
variable {S : Type u} [Group S] [Finite S] {F : FusionSystem S}
    (L : F.CentricLinkingSystem)

theorem normalizerToLinkingAut_inclusion_square {P Q : L.Object}
    (hPQ : P.as.val ≤ Q.as.val)
    (hQN : Q.as.val ≤ Subgroup.normalizer (P.as.val : Set S)) (x : Q.as.val) :
    (L.normalizerToLinkingAut P ⟨x.val, hQN x.property⟩).hom ≫ L.inclusionLift hPQ =
      L.inclusionLift hPQ ≫ (L.distinguished Q x).hom := by
  apply L.cancel_right _ _ (L.topInclusionLift Q)
  rw [Category.assoc, L.inclusionLift_comp_top]
  change (L.normalizerAutOverTop P _).hom ≫ _ = _
  rw [L.normalizerAutOverTop_square, Category.assoc, L.commutation,
    ← Category.assoc, L.inclusionLift_comp_top]
  rw [L.projection_topInclusionLift]
  rfl

/-- A prescribed linking automorphism extends whenever its actual
conjugation sends each source normalizer element to a target element. -/
theorem exists_linking_normalizer_extension (p : ℕ) (sat : F.Saturated p)
    {P Q T : L.Object} (hPQ : P.as.val ≤ Q.as.val) (hPT : P.as.val ≤ T.as.val)
    (hQN : Q.as.val ≤ Subgroup.normalizer (P.as.val : Set S))
    (hTN : T.as.val ≤ Subgroup.normalizer (P.as.val : Set S))
    (a : Aut P)
    (witness : ∀ x : Q.as.val, ∃ y : T.as.val,
      L.normalizerToLinkingAut P ⟨y.val, hTN y.property⟩ =
        a * L.normalizerToLinkingAut P ⟨x.val, hQN x.property⟩ * a⁻¹) :
    ∃ b : Q ⟶ T, L.inclusionLift hPQ ≫ b = a.hom ≫ L.inclusionLift hPT := by
  let f : (⟨P.as.val⟩ : F.Object) ⟶ ⟨T.as.val⟩ :=
    L.projection.map a.hom ≫ F.inclusion hPT
  have hw : ∀ x : Q.as.val, ∃ y : T.as.val, ∀ z : P.as.val,
      (f.val (P.as.val.normalizerMonoidHom ⟨x.val, hQN x.property⟩ z)).val =
        y.val * (f.val z).val * y.val⁻¹ := by
    intro x
    obtain ⟨y, hy⟩ := witness x
    refine ⟨y, fun z => ?_⟩
    have ha : a * L.normalizerToLinkingAut P ⟨x.val, hQN x.property⟩ =
        L.normalizerToLinkingAut P ⟨y.val, hTN y.property⟩ * a := by
      rw [hy]
      group
    have hp := congrArg (L.linkingAutProjection P) ha
    rw [map_mul, map_mul, L.normalizerToLinkingAut_projection,
      L.normalizerToLinkingAut_projection] at hp
    exact congrArg (fun t : F.automorphismSubgroup P.as.val => (t.val z).val) hp
  obtain ⟨g, hg, hext⟩ := F.centric_normalizer_extension p sat hPQ hQN P.as.property f hw
  obtain ⟨b, hb⟩ := L.projection_surjective Q T ⟨g, hg⟩
  have hp : L.projection.map (L.inclusionLift hPQ ≫ b) =
      L.projection.map (a.hom ≫ L.inclusionLift hPT) := by
    rw [L.projection.map_comp, L.projection.map_comp,
      L.projection_inclusionLift, L.projection_inclusionLift, hb]
    apply Subtype.ext
    apply MonoidHom.ext
    intro x
    apply Subtype.ext
    exact hext x
  obtain ⟨z, hz, _⟩ := (L.central_fiber (L.inclusionLift hPQ ≫ b)
    (a.hom ≫ L.inclusionLift hPT)).mp hp
  refine ⟨(L.distinguished Q ⟨z.val.val, hPQ z.val.property⟩).hom ≫ b, ?_⟩
  calc
    _ = (L.inclusionLift hPQ ≫ (L.distinguished Q
        (subgroupInclusion _ _ hPQ z.val)).hom) ≫ b := (Category.assoc _ _ _).symm
    _ = ((L.distinguished P z.val).hom ≫ L.inclusionLift hPQ) ≫ b :=
      congrArg (fun t => t ≫ b) (L.inclusionLift_distinguished hPQ z.val).symm
    _ = _ := (Category.assoc _ _ _).trans hz

/-- A genuine extension square determines conjugation on every source element. -/
theorem linking_normalizer_extension_conjugation {P Q T : L.Object}
    (hPQ : P.as.val ≤ Q.as.val) (hPT : P.as.val ≤ T.as.val)
    (hQN : Q.as.val ≤ Subgroup.normalizer (P.as.val : Set S))
    (hTN : T.as.val ≤ Subgroup.normalizer (P.as.val : Set S))
    (a : Aut P) (b : Q ⟶ T)
    (hb : L.inclusionLift hPQ ≫ b = a.hom ≫ L.inclusionLift hPT)
    (x : Q.as.val) :
    L.normalizerToLinkingAut P
        ⟨((L.projection.map b).val x).val, hTN ((L.projection.map b).val x).property⟩ =
      a * L.normalizerToLinkingAut P ⟨x.val, hQN x.property⟩ * a⁻¹ := by
  let y := (L.projection.map b).val x
  have he : L.normalizerToLinkingAut P ⟨y.val, hTN y.property⟩ * a =
      a * L.normalizerToLinkingAut P ⟨x.val, hQN x.property⟩ := by
    apply Iso.ext
    apply L.cancel_right _ _ (L.inclusionLift hPT)
    change (a.hom ≫ (L.normalizerToLinkingAut P _).hom) ≫ _ =
      ((L.normalizerToLinkingAut P _).hom ≫ a.hom) ≫ _
    rw [Category.assoc, L.normalizerToLinkingAut_inclusion_square hPT hTN,
      ← Category.assoc, ← hb, Category.assoc, ← L.commutation,
      ← Category.assoc, ← L.normalizerToLinkingAut_inclusion_square hPQ hQN,
      Category.assoc, hb, ← Category.assoc]
  calc
    _ = (L.normalizerToLinkingAut P ⟨y.val, hTN y.property⟩ * a) * a⁻¹ := by dsimp [y]; group
    _ = _ := by rw [he]

end Sharpness.FusionSystem.CentricLinkingSystem


