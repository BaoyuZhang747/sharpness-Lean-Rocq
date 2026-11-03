import Sharpness.CentricChains
import Sharpness.CoherentLinkingInclusions

/-! The actual compatible-tuple subgroup of linking automorphisms of
a centric chain. Compatibility is imposed at all comparable indices;
the adjacent-square formulation is identified separately. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness.FusionSystem.CentricLinkingSystem
open CategoryTheory
variable {S : Type u} [Group S] [Finite S] {F : FusionSystem S}
    (L : F.CentricLinkingSystem)

def chainInclusion (σ : F.CentricChain) {i j : Fin (σ.length + 1)} (h : i ≤ j) :
    σ.linkingObject L i ⟶ σ.linkingObject L j := L.inclusionLift (σ.subgroup_mono h)

@[simp] theorem chainInclusion_refl (σ : F.CentricChain) (i : Fin (σ.length + 1)) :
    L.chainInclusion σ (le_refl i) = 𝟙 (σ.linkingObject L i) := L.inclusionLift_refl _

@[simp] theorem chainInclusion_comp (σ : F.CentricChain) {i j k : Fin (σ.length + 1)}
    (hij : i ≤ j) (hjk : j ≤ k) :
    L.chainInclusion σ hij ≫ L.chainInclusion σ hjk =
      L.chainInclusion σ (hij.trans hjk) := L.inclusionLift_comp _ _

def ChainCompatible (σ : F.CentricChain)
    (a : ∀ i : Fin (σ.length + 1), Aut (σ.linkingObject L i)) : Prop :=
  ∀ (i j : Fin (σ.length + 1)) (h : i ≤ j),
    (a i).hom ≫ L.chainInclusion σ h = L.chainInclusion σ h ≫ (a j).hom

theorem chainCompatible_one (σ : F.CentricChain) : L.ChainCompatible σ 1 := by
  intro i j h
  change (𝟙 _) ≫ _ = _ ≫ (𝟙 _)
  simp only [Category.id_comp, Category.comp_id]

theorem chainCompatible_mul (σ : F.CentricChain)
    {a b : ∀ i : Fin (σ.length + 1), Aut (σ.linkingObject L i)}
    (ha : L.ChainCompatible σ a) (hb : L.ChainCompatible σ b) :
    L.ChainCompatible σ (a * b) := by
  intro i j h
  change ((b i).hom ≫ (a i).hom) ≫ L.chainInclusion σ h =
    L.chainInclusion σ h ≫ ((b j).hom ≫ (a j).hom)
  rw [Category.assoc, ha i j h, ← Category.assoc, hb i j h, Category.assoc]

theorem chainCompatible_inv (σ : F.CentricChain)
    {a : ∀ i : Fin (σ.length + 1), Aut (σ.linkingObject L i)}
    (ha : L.ChainCompatible σ a) : L.ChainCompatible σ a⁻¹ := by
  intro i j h
  change (a i).inv ≫ L.chainInclusion σ h = L.chainInclusion σ h ≫ (a j).inv
  apply (cancel_epi (a i).hom).mp
  apply (cancel_mono (a j).hom).mp
  simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id,
    Category.comp_id] using (ha i j h).symm

def chainAutomorphismGroup (σ : F.CentricChain) :
    Subgroup (∀ i : Fin (σ.length + 1), Aut (σ.linkingObject L i)) where
  carrier := L.ChainCompatible σ
  one_mem' := L.chainCompatible_one σ
  mul_mem' := L.chainCompatible_mul σ
  inv_mem' := L.chainCompatible_inv σ

abbrev ChainAut (σ : F.CentricChain) := ↥(L.chainAutomorphismGroup σ)

def chainAutProjection (σ : F.CentricChain) (i : Fin (σ.length + 1)) :
    L.ChainAut σ →* Aut (σ.linkingObject L i) where
  toFun a := a.val i
  map_one' := rfl
  map_mul' _ _ := rfl

theorem chainAutProjection_square (σ : F.CentricChain) (a : L.ChainAut σ)
    (i j : Fin (σ.length + 1)) (h : i ≤ j) :
    (L.chainAutProjection σ i a).hom ≫ L.chainInclusion σ h =
      L.chainInclusion σ h ≫ (L.chainAutProjection σ j a).hom := a.property i j h

end Sharpness.FusionSystem.CentricLinkingSystem
