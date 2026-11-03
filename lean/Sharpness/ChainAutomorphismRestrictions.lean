import Sharpness.ChainAutomorphisms

/-! The manuscript's adjacent-square definition of chain automorphisms
and the actual tuple-deletion homomorphisms for every order-embedded
subchain. Identity and composition retain the specified coordinates. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness.FusionSystem.CentricLinkingSystem
open CategoryTheory
variable {S : Type u} [Group S] [Finite S] {F : FusionSystem S}
    (L : F.CentricLinkingSystem)

theorem chainCompatible_of_adjacent (σ : F.CentricChain)
    (a : ∀ i : Fin (σ.length + 1), Aut (σ.linkingObject L i))
    (ha : ∀ j : Fin σ.length,
      (a j.castSucc).hom ≫ L.chainInclusion σ (le_of_lt j.castSucc_lt_succ) =
        L.chainInclusion σ (le_of_lt j.castSucc_lt_succ) ≫ (a j.succ).hom) :
    L.ChainCompatible σ a := by
  intro i j
  induction j using Fin.induction with
  | zero =>
    intro hij
    have hi : i = 0 := le_antisymm hij (Fin.zero_le i)
    subst i
    simp only [L.chainInclusion_refl, Category.id_comp, Category.comp_id]
  | succ j ih =>
    intro hij
    by_cases heq : i = j.succ
    · subst i
      simp only [L.chainInclusion_refl, Category.id_comp, Category.comp_id]
    · have hij' : i ≤ j.castSucc := by
        have hv : i.val ≠ j.val + 1 := fun h => heq (Fin.ext h)
        have hl : i.val ≤ j.val + 1 := hij
        change i.val ≤ j.val
        omega
      have hstep : j.castSucc ≤ j.succ := le_of_lt j.castSucc_lt_succ
      have hc := L.chainInclusion_comp σ hij' hstep
      calc
        _ = (a i).hom ≫ (L.chainInclusion σ hij' ≫ L.chainInclusion σ hstep) := by
          rw [hc]
        _ = L.chainInclusion σ hij' ≫
            (L.chainInclusion σ hstep ≫ (a j.succ).hom) := by
          rw [← Category.assoc, ih hij', Category.assoc, ha j]
        _ = _ := by rw [← Category.assoc, hc]

theorem chainCompatible_iff_adjacent (σ : F.CentricChain)
    (a : ∀ i : Fin (σ.length + 1), Aut (σ.linkingObject L i)) :
    L.ChainCompatible σ a ↔ ∀ j : Fin σ.length,
      (a j.castSucc).hom ≫ L.chainInclusion σ (le_of_lt j.castSucc_lt_succ) =
        L.chainInclusion σ (le_of_lt j.castSucc_lt_succ) ≫ (a j.succ).hom :=
  ⟨fun ha j => ha j.castSucc j.succ (le_of_lt j.castSucc_lt_succ),
    L.chainCompatible_of_adjacent σ a⟩

def chainAutRestriction (σ : F.CentricChain) (m : ℕ)
    (e : Fin (m + 1) ↪o Fin (σ.length + 1)) :
    L.ChainAut σ →* L.ChainAut (σ.subchain m e) where
  toFun a := ⟨fun i => a.val (e i), fun i j h => a.property (e i) (e j) (e.monotone h)⟩
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] theorem chainAutRestriction_apply (σ : F.CentricChain) (m : ℕ)
    (e : Fin (m + 1) ↪o Fin (σ.length + 1)) (a : L.ChainAut σ) (i : Fin (m + 1)) :
    (L.chainAutRestriction σ m e a).val i = a.val (e i) := rfl

theorem chainAutRestriction_projection (σ : F.CentricChain) (m : ℕ)
    (e : Fin (m + 1) ↪o Fin (σ.length + 1)) (i : Fin (m + 1)) :
    (L.chainAutProjection (σ.subchain m e) i).comp (L.chainAutRestriction σ m e) =
      L.chainAutProjection σ (e i) := by
  apply MonoidHom.ext
  intro a
  rfl

theorem chainAutRestriction_refl (σ : F.CentricChain) :
    L.chainAutRestriction σ σ.length (OrderIso.refl _).toOrderEmbedding =
      MonoidHom.id (L.ChainAut σ) := by
  apply MonoidHom.ext
  intro a
  apply Subtype.ext
  rfl

theorem chainAutRestriction_comp (σ : F.CentricChain) (m k : ℕ)
    (e : Fin (m + 1) ↪o Fin (σ.length + 1)) (d : Fin (k + 1) ↪o Fin (m + 1)) :
    (L.chainAutRestriction (σ.subchain m e) k d).comp (L.chainAutRestriction σ m e) =
      L.chainAutRestriction σ k (d.trans e) := by
  apply MonoidHom.ext
  intro a
  apply Subtype.ext
  rfl

end Sharpness.FusionSystem.CentricLinkingSystem
