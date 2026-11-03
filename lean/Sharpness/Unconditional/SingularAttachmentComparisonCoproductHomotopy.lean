import Sharpness.Unconditional.RealizationAttachmentHomotopy
import Mathlib.Topology.Category.TopCat.Limits.Products

/-! Actual homotopies and open embeddings on arbitrary topological coproducts. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness.SingularAttachmentComparison
open CategoryTheory CategoryTheory.Limits
open Sharpness.AttachmentHomotopy

variable {ι : Type u} {A B : ι → TopCat.{u}}

def topologicalCoproductHomotopy {Y : TopCat.{u}} {f g : (∐ A) ⟶ Y}
    (H : ∀ i, TopCat.Homotopy (Sigma.ι A i ≫ f) (Sigma.ι A i ≫ g)) :
    TopCat.Homotopy f g := by
  let k := Sigma.desc (fun i => homotopyPathMap (H i))
  have hk0 : k ≫ realizationPathEvaluation Y 0 = f := by
    apply Sigma.hom_ext
    intro i
    rw [Sigma.ι_desc_assoc]
    exact homotopyPathMap_zero (H i)
  have hk1 : k ≫ realizationPathEvaluation Y 1 = g := by
    apply Sigma.hom_ext
    intro i
    rw [Sigma.ι_desc_assoc]
    exact homotopyPathMap_one (H i)
  exact
    { toFun := fun p => k p.2 p.1
      continuous_toFun := continuous_eval.comp ((k.hom.continuous.comp continuous_snd).prodMk
        continuous_fst)
      map_zero_left := fun x => ConcreteCategory.congr_hom hk0 x
      map_one_left := fun x => ConcreteCategory.congr_hom hk1 x }

theorem topologicalCoproductHomotopy_inclusion {Y : TopCat.{u}} {f g : (∐ A) ⟶ Y}
    (H : ∀ i, TopCat.Homotopy (Sigma.ι A i ≫ f) (Sigma.ι A i ≫ g))
    (i : ι) (s : unitInterval) (x : A i) :
    topologicalCoproductHomotopy H (s, Sigma.ι A i x) = H i (s, x) := by
  exact congrArg (fun k => k x s) (Sigma.ι_desc (fun i => homotopyPathMap (H i)) i)

def topologicalCoproductMapHomotopy {f g : ∀ i, A i ⟶ B i}
    (H : ∀ i, TopCat.Homotopy (f i) (g i)) :
    TopCat.Homotopy (Limits.Sigma.map f) (Limits.Sigma.map g) :=
  topologicalCoproductHomotopy fun i =>
    { toFun := fun p => Sigma.ι B i (H i p)
      continuous_toFun := (Sigma.ι B i).hom.continuous.comp (H i).continuous
      map_zero_left := fun x => by
        exact (congrArg (Sigma.ι B i) ((H i).map_zero_left x)).trans
          (ConcreteCategory.congr_hom (Sigma.ι_map f i) x).symm
      map_one_left := fun x => by
        exact (congrArg (Sigma.ι B i) ((H i).map_one_left x)).trans
          (ConcreteCategory.congr_hom (Sigma.ι_map g i) x).symm }

theorem topologicalCoproductMapHomotopy_inclusion {f g : ∀ i, A i ⟶ B i}
    (H : ∀ i, TopCat.Homotopy (f i) (g i)) (i : ι) (s : unitInterval) (x : A i) :
    topologicalCoproductMapHomotopy H (s, Sigma.ι A i x) = Sigma.ι B i (H i (s, x)) :=
  topologicalCoproductHomotopy_inclusion _ i s x

theorem topologicalCoproductMap_isOpenEmbedding (f : ∀ i, A i ⟶ B i)
    (hf : ∀ i, Topology.IsOpenEmbedding (f i)) :
    Topology.IsOpenEmbedding (Limits.Sigma.map f) := by
  let a := TopCat.homeoOfIso (TopCat.sigmaIsoSigma A)
  let b := TopCat.homeoOfIso (TopCat.sigmaIsoSigma B)
  have heq : (Limits.Sigma.map f : (∐ A : TopCat) → (∐ B : TopCat)) =
      b.symm ∘ _root_.Sigma.map id (fun i => (f i : A i → B i)) ∘ a := by
    funext x
    obtain ⟨⟨i, y⟩, rfl⟩ := a.symm.surjective x
    simp only [Function.comp_apply, Homeomorph.apply_symm_apply]
    change (Limits.Sigma.map f) ((TopCat.sigmaIsoSigma A).inv ⟨i, y⟩) =
      (TopCat.sigmaIsoSigma B).inv ⟨i, f i y⟩
    rw [TopCat.sigmaIsoSigma_inv_apply, TopCat.sigmaIsoSigma_inv_apply]
    exact ConcreteCategory.congr_hom (Limits.Sigma.ι_map f i) y
  rw [heq]
  exact b.symm.isOpenEmbedding.comp
    (((Topology.isOpenEmbedding_sigmaMap Function.injective_id).mpr hf).comp a.isOpenEmbedding)

end Sharpness.SingularAttachmentComparison
