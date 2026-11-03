import Sharpness.Unconditional.NormalizerSubdivisionEvaluationImage
import Sharpness.Unconditional.NormalizerSubdivisionCommaTorsor

/-! Prepending a proper initial centric subgroup to an actual strict chain. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness.FusionSystem
open CategoryTheory
variable {S : Type u} [Group S] {F : FusionSystem S}

def CentricChain.prepend (σ : F.CentricChain) (P : F.CentricSubgroup)
    (h : P.val < σ.subgroup 0) : F.CentricChain where
  length := σ.length + 1
  entry := Fin.cases P σ.entry
  strict := by
    intro i j hij
    cases i using Fin.cases with
    | zero =>
      cases j using Fin.cases with
      | zero => exact (lt_irrefl 0 hij).elim
      | succ j => exact h.trans_le (σ.subgroup_mono (Fin.zero_le j))
    | succ i =>
      cases j using Fin.cases with
      | zero => exact (Fin.not_lt_zero _ hij).elim
      | succ j => exact σ.strict (Fin.succ_lt_succ_iff.mp hij)

@[simp] theorem CentricChain.prepend_entry_zero (σ : F.CentricChain)
    (P : F.CentricSubgroup) (h : P.val < σ.subgroup 0) :
    (σ.prepend P h).entry 0 = P := rfl

@[simp] theorem CentricChain.prepend_entry_succ (σ : F.CentricChain)
    (P : F.CentricSubgroup) (h : P.val < σ.subgroup 0) (i : Fin (σ.length + 1)) :
    (σ.prepend P h).entry i.succ = σ.entry i := rfl

namespace CentricLinkingSystem
variable [Finite S] (L : F.CentricLinkingSystem)

def normalizerPrependDeletion (σ : F.CentricChain) (P : L.Object)
    (h : P.as.val < σ.subgroup 0) :
    L.normalizerSubdivisionObj (σ.prepend P.as h) ⟶ L.normalizerSubdivisionObj σ where
  indices := Fin.succAboveOrderEmb 0
  component i := Iso.refl _
  commutes i j hij := by
    change (𝟙 _) ≫ L.inclusionLift _ = L.inclusionLift _ ≫ 𝟙 _
    rw [Category.id_comp, Category.comp_id]

theorem normalizerPrependDeletion_evaluation (σ : F.CentricChain) (P : L.Object)
    (h : P.as.val < σ.subgroup 0) :
    L.normalizerSubdivisionEvaluation.map (L.normalizerPrependDeletion σ P h) =
      L.inclusionLift h.le := by
  change L.inclusionLift _ ≫ (𝟙 _) = _
  rw [Category.comp_id]

theorem normalizerPrependLift_index_pos (τ σ : F.CentricChain) (P : L.Object)
    (h : P.as.val < σ.subgroup 0)
    (f : L.normalizerSubdivisionObj τ ⟶ L.normalizerSubdivisionObj σ)
    (b : τ.linkingObject L 0 ≅ P) : 0 < f.indices 0 := by
  apply lt_of_le_of_ne (Fin.zero_le _)
  intro he
  have hc := F.order_mono (L.projection.map (f.component 0).inv)
  have hb := F.order_mono (L.projection.map b.hom)
  change Nat.card (σ.subgroup 0) ≤ Nat.card (τ.subgroup (f.indices 0)) at hc
  rw [← he] at hc
  exact h.ne (Subgroup.eq_of_le_of_card_ge h.le (hc.trans hb))

def normalizerPrependLiftIndices (τ σ : F.CentricChain) (P : L.Object)
    (h : P.as.val < σ.subgroup 0)
    (f : L.normalizerSubdivisionObj τ ⟶ L.normalizerSubdivisionObj σ)
    (b : τ.linkingObject L 0 ≅ P) :
    Fin (σ.length + 1 + 1) ↪o Fin (τ.length + 1) :=
  OrderEmbedding.ofStrictMono (Fin.cases 0 f.indices) (by
    intro i j hij
    cases i using Fin.cases with
    | zero =>
      cases j using Fin.cases with
      | zero => exact (lt_irrefl 0 hij).elim
      | succ j =>
        exact (L.normalizerPrependLift_index_pos τ σ P h f b).trans_le
          (f.indices.monotone (Fin.zero_le j))
    | succ i =>
      cases j using Fin.cases with
      | zero => exact (Fin.not_lt_zero _ hij).elim
      | succ j => exact f.indices.strictMono (Fin.succ_lt_succ_iff.mp hij))

/-- The unique candidate extending an arrow into the chain obtained by
prepending its image. The source first object is already isomorphic to that image. -/
def normalizerPrependLift (τ σ : F.CentricChain) (P : L.Object)
    (h : P.as.val < σ.subgroup 0)
    (f : L.normalizerSubdivisionObj τ ⟶ L.normalizerSubdivisionObj σ)
    (b : τ.linkingObject L 0 ≅ P)
    (hb : b.hom ≫ L.inclusionLift h.le = L.normalizerSubdivisionEvaluation.map f) :
    L.normalizerSubdivisionObj τ ⟶ L.normalizerSubdivisionObj (σ.prepend P.as h) where
  indices := L.normalizerPrependLiftIndices τ σ P h f b
  component := Fin.cases b f.component
  commutes i j hij := by
    change Fin (σ.length + 1 + 1) at i j
    cases i using Fin.cases with
    | zero =>
      cases j using Fin.cases with
      | zero =>
        change b.hom ≫ L.inclusionLift (le_refl P.as.val) =
          L.inclusionLift (le_refl (τ.subgroup 0)) ≫ b.hom
        rw [L.inclusionLift_refl, L.inclusionLift_refl,
          Category.id_comp, Category.comp_id]
      | succ j =>
        change b.hom ≫ L.inclusionLift _ =
          L.chainInclusion τ (Fin.zero_le (f.indices j)) ≫ (f.component j).hom
        calc
          b.hom ≫ L.inclusionLift _ =
              (b.hom ≫ L.inclusionLift h.le) ≫ L.chainInclusion σ (Fin.zero_le j) := by
            rw [Category.assoc]
            change b.hom ≫ L.inclusionLift _ = b.hom ≫ (L.inclusionLift _ ≫ L.inclusionLift _)
            rw [L.inclusionLift_comp]
          _ = L.normalizerSubdivisionEvaluation.map f ≫ L.chainInclusion σ (Fin.zero_le j) := by rw [hb]
          _ = _ := by
            change (L.chainInclusion τ (Fin.zero_le (f.indices 0)) ≫ (f.component 0).hom) ≫ _ = _
            have hf := f.commutes 0 j (Fin.zero_le j)
            change (f.component 0).hom ≫ L.chainInclusion σ (Fin.zero_le j) =
              L.chainInclusion τ (f.indices.monotone (Fin.zero_le j)) ≫ (f.component j).hom at hf
            exact (Category.assoc _ _ _).trans
              ((congrArg (fun k => L.chainInclusion τ (Fin.zero_le (f.indices 0)) ≫ k) hf).trans
                ((Category.assoc _ _ _).symm.trans
                  (congrArg (fun k => k ≫ (f.component j).hom) (L.chainInclusion_comp τ _ _))))
    | succ i =>
      cases j using Fin.cases with
      | zero => exact (not_le_of_gt (Fin.succ_pos i) hij).elim
      | succ j => exact f.commutes i j (Fin.succ_le_succ_iff.mp hij)

theorem normalizerPrependLift_deletion (τ σ : F.CentricChain) (P : L.Object)
    (h : P.as.val < σ.subgroup 0)
    (f : L.normalizerSubdivisionObj τ ⟶ L.normalizerSubdivisionObj σ)
    (b : τ.linkingObject L 0 ≅ P)
    (hb : b.hom ≫ L.inclusionLift h.le = L.normalizerSubdivisionEvaluation.map f) :
    L.normalizerPrependLift τ σ P h f b hb ≫ L.normalizerPrependDeletion σ P h = f := by
  apply NormalizerSubdivisionHom.ext
  · rfl
  apply heq_of_eq
  funext i
  apply Iso.ext
  exact Category.comp_id _

theorem normalizerPrependLift_evaluation (τ σ : F.CentricChain) (P : L.Object)
    (h : P.as.val < σ.subgroup 0)
    (f : L.normalizerSubdivisionObj τ ⟶ L.normalizerSubdivisionObj σ)
    (b : τ.linkingObject L 0 ≅ P)
    (hb : b.hom ≫ L.inclusionLift h.le = L.normalizerSubdivisionEvaluation.map f) :
    L.normalizerSubdivisionEvaluation.map (L.normalizerPrependLift τ σ P h f b hb) = b.hom := by
  change L.chainInclusion τ (le_refl 0) ≫ b.hom = _
  rw [L.chainInclusion_refl, Category.id_comp]

/-- Deleting the new first vertex is a categorical monomorphism. Its
retained vertices determine all components, including the first one. -/
theorem normalizerPrependDeletion_cancel (τ σ : F.CentricChain) (P : L.Object)
    (h : P.as.val < σ.subgroup 0)
    (f g : L.normalizerSubdivisionObj τ ⟶
      L.normalizerSubdivisionObj (σ.prepend P.as h))
    (hfg : f ≫ L.normalizerPrependDeletion σ P h =
      g ≫ L.normalizerPrependDeletion σ P h) : f = g := by
  have hi := L.normalizerSubdivision_indices_unique f g
  rcases f with ⟨indices, a, ha⟩
  rcases g with ⟨indices', b, hb⟩
  cases hi
  have hs (j : Fin (σ.length + 1)) : (a j.succ).hom = (b j.succ).hom := by
    have hc := congr_arg_heq (fun k : L.normalizerSubdivisionObj τ ⟶
      L.normalizerSubdivisionObj σ => k.component) hfg
    have hj := congrArg (fun k => (k j).hom) (eq_of_heq hc)
    change (a j.succ).hom ≫ 𝟙 _ = (b j.succ).hom ≫ 𝟙 _ at hj
    simpa only [Category.comp_id] using hj
  apply NormalizerSubdivisionHom.ext
  · rfl
  apply heq_of_eq
  funext j
  apply Iso.ext
  cases j using Fin.cases with
  | zero =>
    apply L.cancel_right _ _ (L.chainInclusion (σ.prepend P.as h)
      (Fin.zero_le (Fin.succ (0 : Fin (σ.length + 1)))))
    exact (ha 0 (Fin.succ (0 : Fin (σ.length + 1))) (Fin.zero_le _)).trans
      ((congrArg (fun k => L.chainInclusion τ
        (indices.monotone (Fin.zero_le (Fin.succ (0 : Fin (σ.length + 1))))) ≫ k)
        (hs 0)).trans (hb 0 (Fin.succ (0 : Fin (σ.length + 1))) (Fin.zero_le _)).symm)
  | succ j => exact hs j

end CentricLinkingSystem
end Sharpness.FusionSystem
