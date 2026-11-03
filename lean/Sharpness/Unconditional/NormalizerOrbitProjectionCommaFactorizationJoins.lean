import Sharpness.Unconditional.NormalizerOrbitProjectionCommaSelection

/-! Inverting the actual simultaneous extension on its selected chain when
the acting fusion map is an isomorphism. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness.FusionSystem.NormalizerChainExtension
open CategoryTheory
variable {S : Type u} [Group S] {F : FusionSystem S}
    {P Q : Subgroup S} {σ τ : F.CentricChain}
    {f : (⟨P⟩ : F.Object) ⟶ ⟨Q⟩} (a : F.NormalizerChainExtension σ τ f)

def onSelectedChain : F.NormalizerChainExtension (σ.subchain τ.length a.indices) τ f where
  indices := (OrderIso.refl _).toOrderEmbedding
  carrier := a.carrier
  acting_le := a.acting_le
  chain_le := a.chain_le
  extension := a.extension
  onActing := a.onActing
  images := a.images

theorem joinHom_surjective [IsIso f] : Function.Surjective a.joinHom.val := by
  have hf : Function.Surjective f.val := by
    intro y
    exact ⟨(inv f).val y, congrArg (fun k => k.val y) (IsIso.inv_hom_id f)⟩
  apply MonoidHom.range_eq_top.mp
  apply top_unique
  rw [← Subgroup.subgroupOf_self (Q ⊔ τ.topSubgroup),
    Subgroup.subgroupOf_sup (show Q ≤ Q ⊔ τ.topSubgroup from le_sup_left)
      (show τ.topSubgroup ≤ Q ⊔ τ.topSubgroup from le_sup_right)]
  apply sup_le
  · intro x hx
    obtain ⟨y, hy⟩ := hf ⟨x.val, hx⟩
    refine ⟨⟨y.val, Subgroup.mem_sup_left y.property⟩, ?_⟩
    apply Subtype.ext
    exact (a.joinHom_onActing y).trans (congrArg Subtype.val hy)
  · intro x hx
    have hm := a.joinHom_images (Fin.last τ.length)
    have hx' : x.val ∈ (τ.subgroup (Fin.last τ.length) : Set S) := hx
    rw [← hm] at hx'
    obtain ⟨y, hy, he⟩ := hx'
    exact ⟨y, Subtype.ext he⟩

def joinIso [IsIso f] :
    (⟨P ⊔ σ.subgroup (a.indices (Fin.last τ.length))⟩ : F.Object) ≅
      ⟨Q ⊔ τ.topSubgroup⟩ := by
  let e := MulEquiv.ofBijective a.joinHom.val
    ⟨F.injective _ a.joinHom.property, a.joinHom_surjective⟩
  exact {
    hom := a.joinHom
    inv := ⟨e.symm.toMonoidHom, F.inverse_mem e a.joinHom.property⟩
    hom_inv_id := by
      apply Subtype.ext
      apply MonoidHom.ext
      exact e.symm_apply_apply
    inv_hom_id := by
      apply Subtype.ext
      apply MonoidHom.ext
      exact e.apply_symm_apply }

theorem joinIso_inv_onActing [IsIso f] (x : Q) :
    (a.joinIso.inv.val ⟨x.val, Subgroup.mem_sup_left x.property⟩).val = ((inv f).val x).val := by
  let z : (P ⊔ σ.subgroup (a.indices (Fin.last τ.length)) : Subgroup S) :=
    ⟨((inv f).val x).val, Subgroup.mem_sup_left ((inv f).val x).property⟩
  have hz : a.joinIso.hom.val z = ⟨x.val, Subgroup.mem_sup_left x.property⟩ := by
    apply Subtype.ext
    exact (a.joinHom_onActing ((inv f).val x)).trans
      (congrArg (fun k => (k.val x).val) (IsIso.inv_hom_id f))
  rw [← hz]
  exact congrArg (fun k => (k.val z).val) a.joinIso.hom_inv_id

theorem joinIso_inv_images [IsIso f] (i : Fin (τ.length + 1)) :
    (fun x : (Q ⊔ τ.topSubgroup : Subgroup S) => (a.joinIso.inv.val x).val) ''
      {x | x.val ∈ τ.subgroup i} = (σ.subgroup (a.indices i) : Set S) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : x.val ∈ (τ.subgroup i : Set S) := hx
    rw [← a.joinHom_images i] at hx'
    obtain ⟨z, hz, he⟩ := hx'
    have he' : a.joinIso.hom.val z = x := Subtype.ext he
    have hinv : a.joinIso.inv.val x = z := by
      rw [← he']
      exact congrArg (fun k => k.val z) a.joinIso.hom_inv_id
    change (a.joinIso.inv.val x).val ∈ σ.subgroup (a.indices i)
    rw [hinv]
    exact hz
  · intro hy
    let z : (P ⊔ σ.subgroup (a.indices (Fin.last τ.length)) : Subgroup S) :=
      ⟨y, Subgroup.mem_sup_right (σ.subgroup_mono (a.indices.monotone (Fin.le_last i)) hy)⟩
    refine ⟨a.joinIso.hom.val z, ?_, ?_⟩
    · change (a.joinHom.val z).val ∈ (τ.subgroup i : Set S)
      rw [← a.joinHom_images i]
      exact ⟨z, hy, rfl⟩
    · exact congrArg (fun k => (k.val z).val) a.joinIso.hom_inv_id

def inverseSelected [IsIso f] :
    F.NormalizerChainExtension τ (σ.subchain τ.length a.indices) (inv f) where
  indices := (OrderIso.refl _).toOrderEmbedding
  carrier := Q ⊔ τ.topSubgroup
  acting_le := le_sup_left
  chain_le := le_sup_right
  extension := a.joinIso.inv ≫ F.inclusion le_top
  onActing := a.joinIso_inv_onActing
  images := a.joinIso_inv_images

end Sharpness.FusionSystem.NormalizerChainExtension

