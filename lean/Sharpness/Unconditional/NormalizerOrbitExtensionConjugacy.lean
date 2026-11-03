import Sharpness.Unconditional.NormalizerOrbitExtensions

/-! Each simultaneous extension yields the actual fusion conjugacy between
its selected source subchain and its target chain. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness.FusionSystem.NormalizerChainExtension
open CategoryTheory
variable {S : Type u} [Group S] {F : FusionSystem S}
  {P Q : Subgroup S} {σ τ : F.CentricChain}
  {f : (⟨P⟩ : F.Object) ⟶ ⟨Q⟩} (a : F.NormalizerChainExtension σ τ f)

def chainHom : (σ.subchain τ.length a.indices).topRawObject ⟶ τ.topRawObject := by
  let g : (σ.subchain τ.length a.indices).topSubgroup →* τ.topSubgroup :=
    { toFun x := ⟨(a.extension.val ⟨x.val,a.chain_le x.property⟩).val,by
        change (a.extension.val ⟨x.val,a.chain_le x.property⟩).val ∈
          (τ.subgroup (Fin.last τ.length) : Set S)
        rw [← a.images (Fin.last τ.length)]
        exact ⟨⟨x.val,a.chain_le x.property⟩,x.property,rfl⟩⟩
      map_one' := by
        apply Subtype.ext
        exact congrArg (fun z : (⊤ : Subgroup S) => z.val) a.extension.val.map_one
      map_mul' x y := by
        apply Subtype.ext
        exact congrArg (fun z : (⊤ : Subgroup S) => z.val)
          (a.extension.val.map_mul ⟨x.val,a.chain_le x.property⟩
            ⟨y.val,a.chain_le y.property⟩) }
  refine ⟨g,F.codomain_restrict_mem
    (a.extension.val.comp (subgroupInclusion _ _ a.chain_le))
    (F.comp_mem _ _ (F.inclusion_mem _) a.extension.property) le_top g ?_⟩
  ext x
  rfl

theorem chainHom_surjective : Function.Surjective a.chainHom.val := by
  intro y
  have hy : y.val ∈ (τ.subgroup (Fin.last τ.length) : Set S) := y.property
  rw [← a.images (Fin.last τ.length)] at hy
  obtain ⟨x,hx,he⟩ := hy
  exact ⟨⟨x.val,hx⟩,Subtype.ext he⟩

def chainIso : (σ.subchain τ.length a.indices).topRawObject ≅ τ.topRawObject := by
  let e := MulEquiv.ofBijective a.chainHom.val
    ⟨F.injective _ a.chainHom.property,a.chainHom_surjective⟩
  exact
    { hom := a.chainHom
      inv := ⟨e.symm.toMonoidHom,F.inverse_mem e a.chainHom.property⟩
      hom_inv_id := by
        apply Subtype.ext
        apply MonoidHom.ext
        exact e.symm_apply_apply
      inv_hom_id := by
        apply Subtype.ext
        apply MonoidHom.ext
        exact e.apply_symm_apply }

theorem chainIso_image (i : Fin (τ.length + 1)) :
    (fun x : (σ.subchain τ.length a.indices).topSubgroup => (a.chainIso.hom.val x).val) ''
      {x | x.val ∈ σ.subgroup (a.indices i)} = (τ.subgroup i : Set S) := by
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    rw [← a.images i]
    exact ⟨⟨x.val,a.chain_le x.property⟩,hx,rfl⟩
  · intro hy
    rw [← a.images i] at hy
    obtain ⟨x,hx,he⟩ := hy
    refine ⟨⟨x.val,σ.subgroup_mono (a.indices.monotone (Fin.le_last _)) hx⟩,hx,?_⟩
    exact he

def chainConjugacy : CentricChain.Conjugacy (σ.subchain τ.length a.indices) τ :=
  CentricChain.Conjugacy.ofTopIso rfl a.chainIso a.chainIso_image

include a in
theorem isSubconjugate : CentricChain.IsSubconjugate σ τ :=
  ⟨τ.length,a.indices,⟨a.chainConjugacy⟩⟩

end Sharpness.FusionSystem.NormalizerChainExtension
