import Sharpness.Unconditional.NormalizerOrbitExtensionConjugacy
import Sharpness.Unconditional.CentralizerConstruction

/-! Simultaneous extension witnesses restrict to precisely the joins appearing
in the normalizer definition. The larger-carrier presentation used to compose
witnesses does not enlarge the class of allowed extension morphisms. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness.FusionSystem.NormalizerChainExtension
open CategoryTheory
variable {S : Type u} [Group S] {F : FusionSystem S}
  {P Q : Subgroup S} {σ τ : F.CentricChain}
  {f : (⟨P⟩ : F.Object) ⟶ ⟨Q⟩} (a : F.NormalizerChainExtension σ τ f)

def joinHom :
    (⟨P ⊔ σ.subgroup (a.indices (Fin.last τ.length))⟩ : F.Object) ⟶
      ⟨Q ⊔ τ.topSubgroup⟩ := by
  let hD : P ⊔ σ.subgroup (a.indices (Fin.last τ.length)) ≤ a.carrier :=
    sup_le a.acting_le a.chain_le
  let g₀ := F.inclusion hD ≫ a.extension
  have hm : ∀ x, (g₀.val x).val ∈ Q ⊔ τ.topSubgroup := by
    apply join_image_mem g₀.val ((Q ⊔ τ.topSubgroup).subgroupOf ⊤)
    · intro x
      change (a.extension.val ⟨x.val,a.acting_le x.property⟩).val ∈ Q ⊔ τ.topSubgroup
      rw [a.onActing x]
      exact Subgroup.mem_sup_left (f.val x).property
    · intro x
      change (a.extension.val ⟨x.val,a.chain_le x.property⟩).val ∈ Q ⊔ τ.topSubgroup
      apply Subgroup.mem_sup_right
      change (a.extension.val ⟨x.val,a.chain_le x.property⟩).val ∈
        (τ.subgroup (Fin.last τ.length) : Set S)
      rw [← a.images (Fin.last τ.length)]
      exact ⟨⟨x.val,a.chain_le x.property⟩,x.property,rfl⟩
  let g : (P ⊔ σ.subgroup (a.indices (Fin.last τ.length)) : Subgroup S) →*
      (Q ⊔ τ.topSubgroup : Subgroup S) :=
    { toFun x := ⟨(g₀.val x).val,hm x⟩
      map_one' := by
        apply Subtype.ext
        exact congrArg (fun z : (⊤ : Subgroup S) => z.val) g₀.val.map_one
      map_mul' x y := by
        apply Subtype.ext
        exact congrArg (fun z : (⊤ : Subgroup S) => z.val) (g₀.val.map_mul x y) }
  exact ⟨g,F.codomain_restrict_mem g₀.val g₀.property le_top g (by ext x; rfl)⟩

theorem joinHom_onActing (x : P) :
    (a.joinHom.val ⟨x.val,Subgroup.mem_sup_left x.property⟩).val = (f.val x).val :=
  a.onActing x

theorem joinHom_images (i : Fin (τ.length + 1)) :
    (fun x : (P ⊔ σ.subgroup (a.indices (Fin.last τ.length)) : Subgroup S) =>
      (a.joinHom.val x).val) '' {x | x.val ∈ σ.subgroup (a.indices i)} =
        (τ.subgroup i : Set S) := by
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    rw [← a.images i]
    exact ⟨⟨x.val,(sup_le a.acting_le a.chain_le) x.property⟩,hx,rfl⟩
  · intro hy
    rw [← a.images i] at hy
    obtain ⟨x,hx,he⟩ := hy
    refine ⟨⟨x.val,Subgroup.mem_sup_right
      (σ.subgroup_mono (a.indices.monotone (Fin.le_last _)) hx)⟩,hx,?_⟩
    exact he

end Sharpness.FusionSystem.NormalizerChainExtension

namespace Sharpness.FusionSystem
open CategoryTheory
variable {S : Type u} [Group S] (F : FusionSystem S)

theorem normalizerChainExtension_iff_join {P Q : Subgroup S}
    (σ τ : F.CentricChain) (f : (⟨P⟩ : F.Object) ⟶ ⟨Q⟩) :
    Nonempty (F.NormalizerChainExtension σ τ f) ↔
      ∃ (e : Fin (τ.length + 1) ↪o Fin (σ.length + 1))
        (g : (⟨P ⊔ σ.subgroup (e (Fin.last τ.length))⟩ : F.Object) ⟶
          ⟨Q ⊔ τ.topSubgroup⟩),
        (∀ x : P, (g.val ⟨x.val,Subgroup.mem_sup_left x.property⟩).val = (f.val x).val) ∧
        (∀ i : Fin (τ.length + 1),
          (fun x : (P ⊔ σ.subgroup (e (Fin.last τ.length)) : Subgroup S) =>
            (g.val x).val) '' {x | x.val ∈ σ.subgroup (e i)} = (τ.subgroup i : Set S)) := by
  constructor
  · rintro ⟨a⟩
    exact ⟨a.indices,a.joinHom,a.joinHom_onActing,a.joinHom_images⟩
  · rintro ⟨e,g,hP,hC⟩
    exact ⟨{
      indices := e
      carrier := P ⊔ σ.subgroup (e (Fin.last τ.length))
      acting_le := le_sup_left
      chain_le := le_sup_right
      extension := g ≫ F.inclusion le_top
      onActing := hP
      images := hC }⟩

end Sharpness.FusionSystem
