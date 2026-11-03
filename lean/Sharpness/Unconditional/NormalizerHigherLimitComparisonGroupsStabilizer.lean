import Sharpness.Unconditional.NormalizerHigherLimitComparisonGroups

/-! The compatible-tuple group is the actual subgroup of top linking
automorphisms preserving each subgroup in the chain. The top-coordinate
map and its inverse are proved, including a prescribed-top lifting lemma. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness.FusionSystem.CentricChain
variable {S : Type u} [Group S] [Finite S] {F : FusionSystem S}

/-- Fusion automorphisms of the top subgroup which preserve the whole chain. -/
def fusionStabilizer (σ : F.CentricChain) : Subgroup (F.automorphismSubgroup σ.topSubgroup) where
  carrier := {a | ∀ (i : Fin (σ.length + 1)) (x : σ.topSubgroup),
    x.val ∈ σ.subgroup i ↔ (a.val x).val ∈ σ.subgroup i}
  one_mem' := fun _ _ => Iff.rfl
  mul_mem' {a b} ha hb := by
    intro i x
    exact (hb i x).trans (ha i (b.val x))
  inv_mem' {a} ha := by
    intro i x
    have h := ha i (a.val.symm x)
    rw [a.val.apply_symm_apply] at h
    exact h.symm

end Sharpness.FusionSystem.CentricChain

namespace Sharpness.FusionSystem.CentricLinkingSystem
open CategoryTheory
variable {S : Type u} [Group S] [Finite S] {F : FusionSystem S}
    (L : F.CentricLinkingSystem)

def chainTopStabilizer (σ : F.CentricChain) :
    Subgroup (Aut (σ.linkingObject L (Fin.last σ.length))) :=
  σ.fusionStabilizer.comap (L.linkingAutProjection (σ.linkingObject L (Fin.last σ.length)))

theorem chainAutTopProjection_injective (σ : F.CentricChain) :
    Function.Injective (L.chainAutProjection σ (Fin.last σ.length)) := by
  intro a b hab
  apply Subtype.ext
  funext i
  apply Iso.ext
  apply L.cancel_right _ _ (L.chainInclusion σ (Fin.le_last i))
  rw [a.property i _ (Fin.le_last i), b.property i _ (Fin.le_last i)]
  exact congrArg (fun t => L.chainInclusion σ (Fin.le_last i) ≫ t.hom) hab

theorem chainAutTopProjection_mem (σ : F.CentricChain) (a : L.ChainAut σ) :
    L.chainAutProjection σ (Fin.last σ.length) a ∈ L.chainTopStabilizer σ := by
  let f : L.normalizerSubdivisionObj σ ⟶ L.normalizerSubdivisionObj σ :=
    { indices := (OrderIso.refl _).toOrderEmbedding
      component := a.val
      commutes := a.property }
  intro i x
  exact f.fusionConjugacy.maps i x

/-- A preserving linking automorphism of the top extends uniquely to
a compatible chain tuple, retaining that prescribed top automorphism. -/
theorem exists_chainAut_with_top (σ : F.CentricChain)
    (t : Aut (σ.linkingObject L (Fin.last σ.length))) (ht : t ∈ L.chainTopStabilizer σ) :
    ∃ a : L.ChainAut σ, L.chainAutProjection σ (Fin.last σ.length) a = t := by
  have exists_component (i : Fin (σ.length + 1)) :
      ∃ a : Aut (σ.linkingObject L i),
        a.hom ≫ L.chainInclusion σ (Fin.le_last i) =
          L.chainInclusion σ (Fin.le_last i) ≫ t.hom := by
    let e := F.restrictRawIso (σ.subgroup_mono (Fin.le_last i))
      (σ.subgroup_mono (Fin.le_last i)) (L.projection.mapIso t) (ht i)
    let a := L.normalizerLinkingIsoLift e
    have hp : L.projection.map (a.hom ≫ L.chainInclusion σ (Fin.le_last i)) =
        L.projection.map (L.chainInclusion σ (Fin.le_last i) ≫ t.hom) := by
      rw [L.projection.map_comp, L.projection.map_comp,
        L.normalizerLinkingIsoLift_projection]
      change e.hom ≫ L.projection.map (L.inclusionLift _) =
        L.projection.map (L.inclusionLift _) ≫ L.projection.map t.hom
      simp only [L.projection_inclusionLift]
      apply Subtype.ext
      apply MonoidHom.ext
      intro x
      apply Subtype.ext
      rfl
    obtain ⟨z, hz, _⟩ := (L.central_fiber
      (a.hom ≫ L.chainInclusion σ (Fin.le_last i))
      (L.chainInclusion σ (Fin.le_last i) ≫ t.hom)).mp hp
    refine ⟨(L.distinguished (σ.linkingObject L i) z.val).trans a, ?_⟩
    exact (Category.assoc _ _ _).trans hz
  choose a ha using exists_component
  have hc : L.ChainCompatible σ a := by
    intro i j hij
    apply L.cancel_right _ _ (L.chainInclusion σ (Fin.le_last j))
    calc
      ((a i).hom ≫ L.chainInclusion σ hij) ≫ L.chainInclusion σ (Fin.le_last j) =
          (a i).hom ≫ L.chainInclusion σ (Fin.le_last i) := by
        rw [Category.assoc, L.chainInclusion_comp]
      _ = L.chainInclusion σ (Fin.le_last i) ≫ t.hom := ha i
      _ = (L.chainInclusion σ hij ≫ L.chainInclusion σ (Fin.le_last j)) ≫ t.hom := by
        rw [L.chainInclusion_comp]
      _ = L.chainInclusion σ hij ≫ ((a j).hom ≫ L.chainInclusion σ (Fin.le_last j)) := by
        rw [Category.assoc, ha j]
      _ = (L.chainInclusion σ hij ≫ (a j).hom) ≫ L.chainInclusion σ (Fin.le_last j) :=
        (Category.assoc _ _ _).symm
  refine ⟨⟨a, hc⟩, ?_⟩
  apply Iso.ext
  change (a (Fin.last σ.length)).hom = t.hom
  have h := ha (Fin.last σ.length)
  simpa only [L.chainInclusion_refl, Category.comp_id, Category.id_comp] using h

def chainAutToTopStabilizer (σ : F.CentricChain) :
    L.ChainAut σ →* L.chainTopStabilizer σ where
  toFun a := ⟨L.chainAutProjection σ (Fin.last σ.length) a, L.chainAutTopProjection_mem σ a⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem chainAutToTopStabilizer_bijective (σ : F.CentricChain) :
    Function.Bijective (L.chainAutToTopStabilizer σ) := by
  constructor
  · intro a b h
    exact L.chainAutTopProjection_injective σ (congrArg Subtype.val h)
  · intro t
    obtain ⟨a, ha⟩ := L.exists_chainAut_with_top σ t.val t.property
    exact ⟨a, Subtype.ext ha⟩

/-- Literal top-coordinate identification of the actual compatible-tuple group. -/
def chainAutTopStabilizerEquiv (σ : F.CentricChain) :
    L.ChainAut σ ≃* L.chainTopStabilizer σ :=
  MulEquiv.ofBijective (L.chainAutToTopStabilizer σ) (L.chainAutToTopStabilizer_bijective σ)

end Sharpness.FusionSystem.CentricLinkingSystem
