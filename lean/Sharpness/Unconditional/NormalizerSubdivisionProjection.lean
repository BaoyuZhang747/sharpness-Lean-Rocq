import Sharpness.Unconditional.NormalizerSubdivisionCategory

/-! The actual projection from the linking subdivision to the
fusion-conjugacy poset of centric chains. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness.FusionSystem.CentricLinkingSystem
open CategoryTheory
variable {S : Type u} [Group S] [Finite S] {F : FusionSystem S}
    (L : F.CentricLinkingSystem)

namespace NormalizerSubdivisionHom
variable {L} {σ τ : L.NormalizerSubdivision} (f : σ ⟶ τ)

theorem projection_component_square (i j : Fin (τ.chain.length + 1)) (h : i ≤ j)
    (x : σ.chain.subgroup (f.indices i)) :
    ((L.projection.map (f.component i).hom).val x).val =
      ((L.projection.map (f.component j).hom).val
        ⟨x.val, σ.chain.subgroup_mono (f.indices.monotone h) x.property⟩).val := by
  have hs := congrArg (fun t => L.projection.map t) (f.commutes i j h)
  rw [L.projection.map_comp, L.projection.map_comp] at hs
  change L.projection.map (f.component i).hom ≫ L.projection.map (L.inclusionLift _) =
    L.projection.map (L.inclusionLift _) ≫ L.projection.map (f.component j).hom at hs
  rw [L.projection_inclusionLift, L.projection_inclusionLift] at hs
  exact congrArg (fun t => (t.val x).val) hs

def fusionConjugacy :
    CentricChain.Conjugacy (σ.chain.subchain τ.chain.length f.indices) τ.chain where
  indices := OrderIso.refl _
  topIso := L.projection.mapIso (f.component (Fin.last τ.chain.length))
  maps i x := by
    let t := Fin.last τ.chain.length
    let φ := (L.projection.map (f.component t).hom).val
    change x.val ∈ σ.chain.subgroup (f.indices i) ↔ (φ x).val ∈ τ.chain.subgroup i
    constructor
    · intro hx
      let y : σ.chain.subgroup (f.indices i) := ⟨x.val, hx⟩
      have hs := f.projection_component_square i t (Fin.le_last _) y
      change ((L.projection.map (f.component i).hom).val y).val = (φ x).val at hs
      rw [← hs]
      exact ((L.projection.map (f.component i).hom).val y).property
    · intro hx
      let y : τ.chain.subgroup i := ⟨(φ x).val, hx⟩
      let z : σ.chain.subgroup (f.indices i) := (L.projection.map (f.component i).inv).val y
      have hz : (L.projection.map (f.component i).hom).val z = y :=
        congrArg (fun t => t.val y) (L.projection.mapIso (f.component i)).inv_hom_id
      have hs := f.projection_component_square i t (Fin.le_last _) z
      rw [hz] at hs
      have he : (⟨z.val, σ.chain.subgroup_mono
          (f.indices.monotone (Fin.le_last i)) z.property⟩ :
          σ.chain.subgroup (f.indices t)) = x := by
        apply F.injective (L.projection.map (f.component t).hom).val
          (L.projection.map (f.component t).hom).property
        exact Subtype.ext hs.symm
      have hev : z.val = x.val := congrArg Subtype.val he
      rw [← hev]
      exact z.property

include f in
theorem subconjugate : CentricChain.IsSubconjugate σ.chain τ.chain :=
  ⟨τ.chain.length, f.indices, ⟨f.fusionConjugacy⟩⟩

end NormalizerSubdivisionHom

def normalizerSubdivisionProjection : L.NormalizerSubdivision ⥤ F.NormalizerCategory where
  obj σ := F.normalizerClass σ.chain
  map f := homOfLE f.subconjugate
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

end Sharpness.FusionSystem.CentricLinkingSystem
