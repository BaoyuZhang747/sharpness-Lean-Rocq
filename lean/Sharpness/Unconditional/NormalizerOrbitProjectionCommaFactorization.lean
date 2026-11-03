import Sharpness.Unconditional.NormalizerOrbitProjectionCommaFactorizationJoins
import Sharpness.Unconditional.NormalizerOrbitLocalCategory

/-! Unique factorization through an actual pointing whose acting orbit map
is an isomorphism, with target the same literal centric chain. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness.FusionSystem
open CategoryTheory
variable {S : Type u} [Group S] [Finite S] {F : FusionSystem S}

def NormalizerChainExtension.factorThrough
    {P Q T : Subgroup S} {σ τ : F.CentricChain}
    {f : (⟨P⟩ : F.Object) ⟶ ⟨Q⟩} {g : (⟨P⟩ : F.Object) ⟶ ⟨T⟩}
    (a : F.NormalizerChainExtension σ τ f) (b : F.NormalizerChainExtension σ τ g)
    [IsIso f] : F.NormalizerChainExtension τ τ (inv f ≫ g) := by
  have b' : F.NormalizerChainExtension (σ.subchain τ.length a.indices) τ g := by
    rw [a.indices_unique b]
    exact b.onSelectedChain
  exact a.inverseSelected.comp b'

theorem NormalizerOrbitPair.existsUnique_factorization
    (A : F.NormalizerOrbitPair) {σ : F.CentricChain}
    (B D : F.NormalizerOrbitAtChain σ) (u : A ⟶ B.obj)
    (hu : IsIso (F.normalizerOrbitPairForget.map u)) (f : A ⟶ D.obj) :
    ∃! g : B.obj ⟶ D.obj, u ≫ g = f := by
  letI := hu
  obtain ⟨u₀, hu₀, ⟨a⟩⟩ := u.property
  obtain ⟨f₀, hf₀, ⟨b⟩⟩ := f.property
  have hcard : Nat.card A.centric.obj.as.subgroup = Nat.card B.obj.centric.obj.as.subgroup := by
    exact le_antisymm
      (F.orbitOrder_mono (asIso (F.normalizerOrbitPairForget.map u)).hom.hom)
      (F.orbitOrder_mono (asIso (F.normalizerOrbitPairForget.map u)).inv.hom)
  letI : IsIso u₀ := (F.isoOfEqualOrder u₀ hcard).isIso_hom
  have a' : F.NormalizerChainExtension A.chain σ u₀ := by
    simpa only [B.property] using a
  have b' : F.NormalizerChainExtension A.chain σ f₀ := by
    simpa only [D.property] using b
  have hc : F.NormalizerChainExtension B.obj.chain D.obj.chain (inv u₀ ≫ f₀) := by
    simpa only [B.property, D.property] using a'.factorThrough b'
  let g : B.obj ⟶ D.obj := NormalizerOrbitPair.homMk (inv u₀ ≫ f₀) hc
  have hg : u ≫ g = f := by
    apply NormalizerOrbitPair.hom_ext
    apply InducedCategory.hom_ext
    change u.val.hom ≫ F.toOrbit.map (inv u₀ ≫ f₀) = f.val.hom
    rw [← hu₀, ← hf₀, ← F.toOrbit.map_comp, IsIso.hom_inv_id_assoc]
  refine ⟨g, hg, ?_⟩
  intro g' hg'
  apply F.normalizerOrbitPairForget.map_injective
  apply (cancel_epi (F.normalizerOrbitPairForget.map u)).mp
  rw [← F.normalizerOrbitPairForget.map_comp, hg',
    ← F.normalizerOrbitPairForget.map_comp, hg]

end Sharpness.FusionSystem
