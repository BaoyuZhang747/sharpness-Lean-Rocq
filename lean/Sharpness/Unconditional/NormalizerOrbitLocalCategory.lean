import Sharpness.Unconditional.NormalizerOrbitPairCategory
import Sharpness.Unconditional.NormalizerOrbitLocalExtensions
import Sharpness.Unconditional.NormalizerHigherLimitComparisonLocalCollection
import Sharpness.SubsystemCentric

/-! The local ambient-centric orbit category maps into the actual full
subcategory of the pair category with a fixed literal chain. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness.FusionSystem
open CategoryTheory
variable {S : Type u} [Group S] [Finite S] {F : FusionSystem S}

abbrev NormalizerOrbitAtChain (σ : F.CentricChain) :=
  ObjectProperty.FullSubcategory (fun A : F.NormalizerOrbitPair => A.chain = σ)

theorem normalizerChainExtension_self_iff_normalizerExtension
    {P Q : Subgroup S} (σ : F.CentricChain) (f : (⟨P⟩ : F.Object) ⟶ ⟨Q⟩) :
    Nonempty (F.NormalizerChainExtension σ σ f) ↔ σ.NormalizerExtension f.val := by
  rw [F.normalizerChainExtension_self_iff_topJoin,σ.normalizerExtension_iff_images]
  constructor
  · rintro ⟨g,hP,hC⟩
    exact ⟨g.val,g.property,hC,hP⟩
  · rintro ⟨g,hg,hC,hP⟩
    exact ⟨⟨g,hg⟩,hP,hC⟩

namespace CentricLinkingSystem
variable (L : F.CentricLinkingSystem) (p : ℕ) [Fact p.Prime]
  (hS : IsPGroup p S) (sat : F.Saturated p) (σ : F.CentricChain)

def chainNormalizerSubsystemEmbedding :
    F.SubsystemEmbedding σ.normalizerSubgroup (L.chainNormalizerFusion σ) where
  hom_mem f hf := σ.normalizerExtension_allowed _
    ((L.chainNormalizerFusion_isHom_iff p sat σ f).mp hf)

def normalizerLocalToPair :
    (L.normalizerAmbientCollection p hS sat σ).Orbit ⥤ F.NormalizerOrbitAtChain σ where
  obj P := ⟨{
    centric := ⟨(F.subsystemOrbitFunctor σ.normalizerSubgroup (L.chainNormalizerFusion σ)
      (L.chainNormalizerSubsystemEmbedding p sat σ)).obj P.obj,P.property⟩
    chain := σ
    normalizes := fun i x hx =>
      (σ.mem_normalizerSubgroup x).mp (σ.normalizerAmbientSubgroup_le P.obj.as.subgroup hx) i },rfl⟩
  map f := by
    let O := F.subsystemOrbitFunctor σ.normalizerSubgroup (L.chainNormalizerFusion σ)
      (L.chainNormalizerSubsystemEmbedding p sat σ)
    refine ObjectProperty.homMk ⟨ObjectProperty.homMk (O.map f.hom),?_⟩
    obtain ⟨g,hg⟩ := (L.chainNormalizerFusion σ).toOrbit.map_surjective f.hom
    let g₀ := (F.subsystemRawFunctor σ.normalizerSubgroup (L.chainNormalizerFusion σ)
      (L.chainNormalizerSubsystemEmbedding p sat σ)).map g
    refine ⟨g₀,?_,?_⟩
    · rw [← hg]
      rfl
    · apply (normalizerChainExtension_self_iff_normalizerExtension σ g₀).mpr
      exact (L.chainNormalizerFusion_isHom_iff p sat σ g.val).mp g.property
  map_id P := by
    apply InducedCategory.hom_ext
    apply Subtype.ext
    apply InducedCategory.hom_ext
    exact (F.subsystemOrbitFunctor σ.normalizerSubgroup (L.chainNormalizerFusion σ)
      (L.chainNormalizerSubsystemEmbedding p sat σ)).map_id P.obj
  map_comp f g := by
    apply InducedCategory.hom_ext
    apply Subtype.ext
    apply InducedCategory.hom_ext
    exact (F.subsystemOrbitFunctor σ.normalizerSubgroup (L.chainNormalizerFusion σ)
      (L.chainNormalizerSubsystemEmbedding p sat σ)).map_comp f.hom g.hom

instance normalizerLocalToPair_faithful :
    (L.normalizerLocalToPair p hS sat σ).Faithful where
  map_injective := by
    intro P Q f g h
    apply InducedCategory.hom_ext
    apply (F.subsystemOrbitFunctor σ.normalizerSubgroup (L.chainNormalizerFusion σ)
      (L.chainNormalizerSubsystemEmbedding p sat σ)).map_injective
    exact congrArg (fun t => t.hom.val.hom) h

end CentricLinkingSystem
end Sharpness.FusionSystem
