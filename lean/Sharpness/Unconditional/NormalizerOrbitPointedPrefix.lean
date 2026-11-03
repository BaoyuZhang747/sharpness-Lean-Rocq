import Sharpness.Unconditional.NormalizerOrbitPointedSubgroupEvaluation
import Sharpness.Unconditional.NormalizerSubdivisionEvaluationPrefix

/-! Actual prefix maps for pointed normalizer chains. A supplied literal
first-subgroup image equality is used to extend the selected index map. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness.FusionSystem
open CategoryTheory
variable {S : Type u} [Group S] {F : FusionSystem S}

namespace NormalizerChainExtension
variable {P Q : Subgroup S} {τ σ : F.CentricChain}
  {f : (⟨P⟩ : F.Object) ⟶ ⟨Q⟩}
  (a : F.NormalizerChainExtension τ σ f) (I : F.CentricSubgroup)
  (hI : I.val < σ.subgroup 0)
  (hImage : (fun x : a.carrier => (a.extension.val x).val) ''
    {x | x.val ∈ τ.subgroup 0} = (I.val : Set S))

include hI hImage in
theorem prepend_index_pos : 0 < a.indices 0 := by
  apply lt_of_le_of_ne (Fin.zero_le _)
  intro he
  have hm := a.images 0
  rw [← he] at hm
  have hEq : I.val = σ.subgroup 0 := SetLike.coe_injective (hImage.symm.trans hm)
  exact hI.ne hEq

def prependIndices : Fin (σ.length + 1 + 1) ↪o Fin (τ.length + 1) :=
  OrderEmbedding.ofStrictMono (Fin.cases 0 a.indices) (by
    intro i j hij
    cases i using Fin.cases with
    | zero =>
      cases j using Fin.cases with
      | zero => exact (lt_irrefl 0 hij).elim
      | succ j =>
        exact (a.prepend_index_pos I hI hImage).trans_le
          (a.indices.monotone (Fin.zero_le j))
    | succ i =>
      cases j using Fin.cases with
      | zero => exact (Fin.not_lt_zero _ hij).elim
      | succ j => exact a.indices.strictMono (Fin.succ_lt_succ_iff.mp hij))

def prepend : F.NormalizerChainExtension τ (σ.prepend I hI) f where
  indices := a.prependIndices I hI hImage
  carrier := a.carrier
  acting_le := a.acting_le
  chain_le := a.chain_le
  extension := a.extension
  onActing := a.onActing
  images i := by
    cases i using Fin.cases with
    | zero => exact hImage
    | succ i => exact a.images i

def prependDeletion (P : Subgroup S) (σ : F.CentricChain) (I : F.CentricSubgroup)
    (hI : I.val < σ.subgroup 0) :
    F.NormalizerChainExtension (σ.prepend I hI) σ (𝟙 (⟨P⟩ : F.Object)) where
  indices := Fin.succAboveOrderEmb 0
  carrier := P ⊔ σ.topSubgroup
  acting_le := le_sup_left
  chain_le := le_sup_right
  extension := F.inclusion le_top
  onActing _ := rfl
  images i := by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact hx
    · intro hy
      exact ⟨⟨y,Subgroup.mem_sup_right (σ.subgroup_mono (Fin.le_last _) hy)⟩,hy,rfl⟩

end NormalizerChainExtension

variable (F) (P : F.CentricOrbit)

def normalizerOrbitPointedPrepend (X : F.NormalizerOrbitPointed P)
    (I : F.CentricSubgroup) (hI : I.val < X.obj.right.chain.subgroup 0)
    (hN : X.obj.right.centric.obj.as.subgroup ≤ Subgroup.normalizer (I.val : Set S)) :
    F.NormalizerOrbitPointed P := by
  let B : F.NormalizerOrbitPair := {
    centric := X.obj.right.centric
    chain := X.obj.right.chain.prepend I hI
    normalizes := by
      intro i
      cases i using Fin.cases with
      | zero => exact hN
      | succ i => exact X.obj.right.normalizes i }
  exact ⟨StructuredArrow.mk (Y := B) X.obj.hom,X.property⟩

def normalizerOrbitPointedPrependDeletion (X : F.NormalizerOrbitPointed P)
    (I : F.CentricSubgroup) (hI : I.val < X.obj.right.chain.subgroup 0)
    (hN : X.obj.right.centric.obj.as.subgroup ≤ Subgroup.normalizer (I.val : Set S)) :
    F.normalizerOrbitPointedPrepend P X I hI hN ⟶ X :=
  ObjectProperty.homMk (StructuredArrow.homMk
    (NormalizerOrbitPair.homMk (𝟙 X.obj.right.centric.obj.as)
      (NormalizerChainExtension.prependDeletion _ X.obj.right.chain I hI)) (by
        change X.obj.hom ≫ 𝟙 X.obj.right.centric = X.obj.hom
        exact Category.comp_id _))

def normalizerOrbitPointedPrependLift {Y X : F.NormalizerOrbitPointed P}
    (f : Y ⟶ X) (I : F.CentricSubgroup) (hI : I.val < X.obj.right.chain.subgroup 0)
    (hN : X.obj.right.centric.obj.as.subgroup ≤ Subgroup.normalizer (I.val : Set S))
    (g : Y.obj.right.centric.obj.as ⟶ X.obj.right.centric.obj.as)
    (hg : F.toOrbit.map g = f.hom.right.val.hom)
    (a : F.NormalizerChainExtension Y.obj.right.chain X.obj.right.chain g)
    (hImage : (fun x : a.carrier => (a.extension.val x).val) ''
      {x | x.val ∈ Y.obj.right.chain.subgroup 0} = (I.val : Set S)) :
    Y ⟶ F.normalizerOrbitPointedPrepend P X I hI hN :=
  ObjectProperty.homMk (StructuredArrow.homMk
    ⟨f.hom.right.val,g,hg,⟨a.prepend I hI hImage⟩⟩ (StructuredArrow.w f.hom))

theorem normalizerOrbitPointedPrependLift_deletion {Y X : F.NormalizerOrbitPointed P}
    (f : Y ⟶ X) (I : F.CentricSubgroup) (hI : I.val < X.obj.right.chain.subgroup 0)
    (hN : X.obj.right.centric.obj.as.subgroup ≤ Subgroup.normalizer (I.val : Set S))
    (g : Y.obj.right.centric.obj.as ⟶ X.obj.right.centric.obj.as)
    (hg : F.toOrbit.map g = f.hom.right.val.hom)
    (a : F.NormalizerChainExtension Y.obj.right.chain X.obj.right.chain g)
    (hImage : (fun x : a.carrier => (a.extension.val x).val) ''
      {x | x.val ∈ Y.obj.right.chain.subgroup 0} = (I.val : Set S)) :
    F.normalizerOrbitPointedPrependLift P f I hI hN g hg a hImage ≫
      F.normalizerOrbitPointedPrependDeletion P X I hI hN = f := by
  apply ObjectProperty.hom_ext
  exact F.normalizerOrbitPointed_source_hom_ext P Y X.obj _ _

end Sharpness.FusionSystem
