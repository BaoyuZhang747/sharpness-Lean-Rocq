import Sharpness.Unconditional.NormalizerOrbitLocalCategory

/-! The actual ambient-centric orbit category of the chain normalizer is
equivalent to the full subcategory of pairs with that literal chain. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness.FusionSystem.CentricChain
variable {S : Type u} [Group S] [Finite S] {F : FusionSystem S}
  (σ : F.CentricChain)

def normalizerLocalHom {P Q : Subgroup σ.normalizerSubgroup}
    (f : σ.normalizerAmbientSubgroup P →* σ.normalizerAmbientSubgroup Q) : P →* Q :=
  (σ.normalizerAmbientEquiv Q).symm.toMonoidHom.comp
    (f.comp (σ.normalizerAmbientEquiv P).toMonoidHom)

theorem normalizerAmbientHom_localHom {P Q : Subgroup σ.normalizerSubgroup}
    (f : σ.normalizerAmbientSubgroup P →* σ.normalizerAmbientSubgroup Q) :
    σ.normalizerAmbientHom (σ.normalizerLocalHom f) = f := by
  apply MonoidHom.ext
  intro x
  simp only [normalizerAmbientHom,normalizerLocalHom,MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom,MulEquiv.apply_symm_apply]

end Sharpness.FusionSystem.CentricChain

namespace Sharpness.FusionSystem.CentricLinkingSystem
open CategoryTheory
variable {S : Type u} [Group S] [Finite S] {F : FusionSystem S}
  (L : F.CentricLinkingSystem) (p : ℕ) [Fact p.Prime]
  (hS : IsPGroup p S) (sat : F.Saturated p) (σ : F.CentricChain)

instance normalizerLocalToPair_full : (L.normalizerLocalToPair p hS sat σ).Full where
  map_surjective := by
    intro P Q f
    obtain ⟨g,hg,⟨a⟩⟩ := f.hom.property
    let g' := σ.normalizerLocalHom g.val
    have hg' : (L.chainNormalizerFusion σ).IsHom g' := by
      apply (L.chainNormalizerFusion_isHom_iff p sat σ g').mpr
      rw [show σ.normalizerAmbientHom g' = g.val from σ.normalizerAmbientHom_localHom g.val]
      exact (normalizerChainExtension_self_iff_normalizerExtension σ g).mp ⟨a⟩
    let h : P ⟶ Q := ObjectProperty.homMk ((L.chainNormalizerFusion σ).toOrbit.map ⟨g',hg'⟩)
    refine ⟨h,?_⟩
    apply InducedCategory.hom_ext
    apply Subtype.ext
    apply InducedCategory.hom_ext
    change F.toOrbit.map ((F.subsystemRawFunctor σ.normalizerSubgroup
      (L.chainNormalizerFusion σ) (L.chainNormalizerSubsystemEmbedding p sat σ)).map ⟨g',hg'⟩) = _
    have he : (F.subsystemRawFunctor σ.normalizerSubgroup
        (L.chainNormalizerFusion σ) (L.chainNormalizerSubsystemEmbedding p sat σ)).map ⟨g',hg'⟩ = g := by
      apply Subtype.ext
      exact σ.normalizerAmbientHom_localHom g.val
    rw [he]
    exact hg

theorem normalizerLocalToPair_obj_surjective :
    Function.Surjective (L.normalizerLocalToPair p hS sat σ).obj := by
  intro A
  have hN : A.obj.centric.obj.as.subgroup ≤ σ.normalizerSubgroup := by
    intro x hx
    apply (σ.mem_normalizerSubgroup x).mpr
    intro i
    have hn := A.obj.normalizes
    rw [A.property] at hn
    exact hn i hx
  let P : Subgroup σ.normalizerSubgroup := A.obj.centric.obj.as.subgroup.subgroupOf σ.normalizerSubgroup
  have hP : σ.normalizerAmbientSubgroup P = A.obj.centric.obj.as.subgroup :=
    Subgroup.map_subgroupOf_eq_of_le hN
  let B : (L.normalizerAmbientCollection p hS sat σ).Orbit :=
    ⟨(L.chainNormalizerFusion σ).toOrbit.obj ⟨P⟩,by
      change F.IsCentric (σ.normalizerAmbientSubgroup P)
      rw [hP]
      exact A.obj.centric.property⟩
  refine ⟨B,?_⟩
  apply ObjectProperty.FullSubcategory.ext
  have hC : ((L.normalizerLocalToPair p hS sat σ).obj B).obj.centric = A.obj.centric := by
    apply ObjectProperty.FullSubcategory.ext
    change F.toOrbit.obj ⟨σ.normalizerAmbientSubgroup P⟩ = A.obj.centric.obj
    rw [hP]
    cases A.obj.centric.obj
    rfl
  have hchain : ((L.normalizerLocalToPair p hS sat σ).obj B).obj.chain = A.obj.chain :=
    A.property.symm
  generalize hLeft : ((L.normalizerLocalToPair p hS sat σ).obj B).obj = X at hC hchain ⊢
  generalize hRight : A.obj = Y at hC hchain ⊢
  cases X
  cases Y
  cases hC
  cases hchain
  rfl

instance normalizerLocalToPair_essSurj : (L.normalizerLocalToPair p hS sat σ).EssSurj :=
  Functor.essSurj_of_surj (L.normalizerLocalToPair_obj_surjective p hS sat σ)

instance normalizerLocalToPair_isEquivalence : (L.normalizerLocalToPair p hS sat σ).IsEquivalence where

def normalizerLocalPairEquivalence :
    (L.normalizerAmbientCollection p hS sat σ).Orbit ≌ F.NormalizerOrbitAtChain σ :=
  (L.normalizerLocalToPair p hS sat σ).asEquivalence

end Sharpness.FusionSystem.CentricLinkingSystem
