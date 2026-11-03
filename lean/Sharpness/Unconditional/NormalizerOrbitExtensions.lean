import Sharpness.NormalizerChainCategory

/-! Actual simultaneous fusion extensions on selected subchains. Domains are
allowed to be larger than the join of the acting and selected top subgroup;
composition restricts the first domain to the inverse image of the second. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness.FusionSystem
open CategoryTheory
variable {S : Type u} [Group S] (F : FusionSystem S)

def extensionPreimage {P : Subgroup S}
    (f : (⟨P⟩ : F.Object) ⟶ ⟨⊤⟩) (Q : Subgroup S) : Subgroup S :=
  (Q.comap ((⊤ : Subgroup S).subtype.comp f.val)).map P.subtype

theorem extensionPreimage_le {P : Subgroup S}
    (f : (⟨P⟩ : F.Object) ⟶ ⟨⊤⟩) (Q : Subgroup S) :
    F.extensionPreimage f Q ≤ P := by
  rintro x ⟨y,hy,rfl⟩
  exact y.property

theorem extensionPreimage_mem {P : Subgroup S}
    (f : (⟨P⟩ : F.Object) ⟶ ⟨⊤⟩) (Q : Subgroup S) (x : P) :
    x.val ∈ F.extensionPreimage f Q ↔ (f.val x).val ∈ Q := by
  constructor
  · rintro ⟨y,hy,he⟩
    have he' : y = x := Subtype.ext he
    subst y
    exact hy
  · intro hx
    exact ⟨x,hx,rfl⟩

def extensionPreimageMap {P : Subgroup S}
    (f : (⟨P⟩ : F.Object) ⟶ ⟨⊤⟩) (Q : Subgroup S) :
    (⟨F.extensionPreimage f Q⟩ : F.Object) ⟶ ⟨Q⟩ := by
  let g : F.extensionPreimage f Q →* Q :=
    { toFun x := ⟨(f.val ⟨x.val,F.extensionPreimage_le f Q x.property⟩).val,
        (F.extensionPreimage_mem f Q _).mp x.property⟩
      map_one' := by
        apply Subtype.ext
        exact congrArg (fun z : (⊤ : Subgroup S) => z.val) f.val.map_one
      map_mul' x y := by
        apply Subtype.ext
        exact congrArg (fun z : (⊤ : Subgroup S) => z.val)
          (f.val.map_mul ⟨x.val,F.extensionPreimage_le f Q x.property⟩
            ⟨y.val,F.extensionPreimage_le f Q y.property⟩) }
  refine ⟨g, F.codomain_restrict_mem
    (f.val.comp (subgroupInclusion _ _ (F.extensionPreimage_le f Q)))
    (F.comp_mem _ _ (F.inclusion_mem _) f.property) le_top g ?_⟩
  ext x
  rfl

@[simp] theorem extensionPreimageMap_apply {P : Subgroup S}
    (f : (⟨P⟩ : F.Object) ⟶ ⟨⊤⟩) (Q : Subgroup S)
    (x : F.extensionPreimage f Q) :
    ((F.extensionPreimageMap f Q).val x).val =
      (f.val ⟨x.val,F.extensionPreimage_le f Q x.property⟩).val := rfl

/-- A concrete fusion extension, retaining the actual selected chain images. -/
structure NormalizerChainExtension {P Q : Subgroup S}
    (σ τ : F.CentricChain) (f : (⟨P⟩ : F.Object) ⟶ ⟨Q⟩) where
  indices : Fin (τ.length + 1) ↪o Fin (σ.length + 1)
  carrier : Subgroup S
  acting_le : P ≤ carrier
  chain_le : σ.subgroup (indices (Fin.last τ.length)) ≤ carrier
  extension : (⟨carrier⟩ : F.Object) ⟶ ⟨⊤⟩
  onActing : ∀ x : P, (extension.val ⟨x.val,acting_le x.property⟩).val = (f.val x).val
  images : ∀ i : Fin (τ.length + 1),
    (fun x : carrier => (extension.val x).val) ''
      {x : carrier | x.val ∈ σ.subgroup (indices i)} = (τ.subgroup i : Set S)

namespace NormalizerChainExtension
variable {F} {P Q T : Subgroup S} {σ τ υ : F.CentricChain}

def identity (P : Subgroup S) (σ : F.CentricChain) :
    F.NormalizerChainExtension σ σ (𝟙 (⟨P⟩ : F.Object)) where
  indices := (OrderIso.refl _).toOrderEmbedding
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

def comp {f : (⟨P⟩ : F.Object) ⟶ ⟨Q⟩} {g : (⟨Q⟩ : F.Object) ⟶ ⟨T⟩}
    (a : F.NormalizerChainExtension σ τ f) (b : F.NormalizerChainExtension τ υ g) :
    F.NormalizerChainExtension σ υ (f ≫ g) where
  indices := b.indices.trans a.indices
  carrier := F.extensionPreimage a.extension b.carrier
  acting_le := by
    intro x hx
    apply (F.extensionPreimage_mem a.extension b.carrier ⟨x,a.acting_le hx⟩).mpr
    rw [a.onActing ⟨x,hx⟩]
    exact b.acting_le (f.val ⟨x,hx⟩).property
  chain_le := by
    intro x hx
    have hxA := a.chain_le (σ.subgroup_mono (a.indices.monotone (Fin.le_last _)) hx)
    apply (F.extensionPreimage_mem a.extension b.carrier ⟨x,hxA⟩).mpr
    apply b.chain_le
    change (a.extension.val ⟨x,hxA⟩).val ∈ (τ.subgroup (b.indices (Fin.last υ.length)) : Set S)
    rw [← a.images (b.indices (Fin.last υ.length))]
    exact ⟨⟨x,hxA⟩,hx,rfl⟩
  extension := F.extensionPreimageMap a.extension b.carrier ≫ b.extension
  onActing x := by
    change (b.extension.val ((F.extensionPreimageMap a.extension b.carrier).val _)).val = _
    have he : (F.extensionPreimageMap a.extension b.carrier).val
        ⟨x.val, by
          apply (F.extensionPreimage_mem a.extension b.carrier ⟨x.val,a.acting_le x.property⟩).mpr
          rw [a.onActing x]
          exact b.acting_le (f.val x).property⟩ =
        ⟨(f.val x).val,b.acting_le (f.val x).property⟩ := by
      apply Subtype.ext
      exact a.onActing x
    rw [he]
    exact b.onActing (f.val x)
  images i := by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      rw [← b.images i]
      refine ⟨(F.extensionPreimageMap a.extension b.carrier).val x,?_,rfl⟩
      change ((F.extensionPreimageMap a.extension b.carrier).val x).val ∈
        (τ.subgroup (b.indices i) : Set S)
      rw [← a.images (b.indices i)]
      exact ⟨⟨x.val,F.extensionPreimage_le a.extension b.carrier x.property⟩,hx,rfl⟩
    · intro hy
      rw [← b.images i] at hy
      obtain ⟨z,hz,rfl⟩ := hy
      change z.val ∈ (τ.subgroup (b.indices i) : Set S) at hz
      rw [← a.images (b.indices i)] at hz
      obtain ⟨x,hx,he⟩ := hz
      change (a.extension.val x).val = z.val at he
      have hxD : x.val ∈ F.extensionPreimage a.extension b.carrier :=
        (F.extensionPreimage_mem a.extension b.carrier x).mpr (by rw [he]; exact z.property)
      refine ⟨⟨x.val,hxD⟩,hx,?_⟩
      change (b.extension.val ((F.extensionPreimageMap a.extension b.carrier).val _)).val = _
      have he' : (F.extensionPreimageMap a.extension b.carrier).val ⟨x.val,hxD⟩ = z :=
        Subtype.ext he
      rw [he']

end NormalizerChainExtension
end Sharpness.FusionSystem
