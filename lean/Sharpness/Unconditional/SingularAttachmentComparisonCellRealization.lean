import Sharpness.Unconditional.SingularAttachmentComparisonCellFamilies
import Sharpness.Unconditional.RealizationSeparationCoproduct

/-! Actual collars for the realization of arbitrary coproducts of simplex
boundaries, with the original realized boundary map as their composite. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
universe u

namespace Sharpness.SingularAttachmentComparison
open CategoryTheory CategoryTheory.Limits Simplicial

variable {ι : Type u} (n : ι → ℕ)

abbrev cellBoundaryFamily : ι → SSet.{u} := fun i => (SSet.boundary.{u} (n i)).toSSet
abbrev cellSimplexFamily : ι → SSet.{u} := fun i => Δ[n i]

def realizedCellCollarBoundary : |(∐ cellBoundaryFamily n)| ⟶ cellFamilyCollar n :=
  (PreservesCoproduct.iso SSet.toTop (cellBoundaryFamily n)).hom ≫ cellFamilyCollarBoundary n

def realizedCellCollarEmbedding : cellFamilyCollar n ⟶ |(∐ cellSimplexFamily n)| :=
  cellFamilyCollarEmbedding n ≫ (PreservesCoproduct.iso SSet.toTop (cellSimplexFamily n)).inv

def realizedCellCollarRetraction : cellFamilyCollar n ⟶ |(∐ cellBoundaryFamily n)| :=
  cellFamilyCollarRetraction n ≫ (PreservesCoproduct.iso SSet.toTop (cellBoundaryFamily n)).inv

theorem realizedCellCollarEmbedding_isOpenEmbedding :
    Topology.IsOpenEmbedding (realizedCellCollarEmbedding n) :=
  (TopCat.homeoOfIso (PreservesCoproduct.iso SSet.toTop (cellSimplexFamily n))).symm.isOpenEmbedding.comp
    (cellFamilyCollarEmbedding_isOpenEmbedding n)

theorem realizedCellBoundary_isClosedEmbedding :
    Topology.IsClosedEmbedding
      (SSet.toTop.map (Limits.Sigma.map (fun i => (SSet.boundary.{u} (n i)).ι))) :=
  RealizationSeparation.mapped_coproduct_isClosedEmbedding SSet.toTop _
    (fun i => RealizationBoundary.boundaryRealizationInclusion_isClosedEmbedding (n i))

theorem realizedCellCollarBoundary_embedding :
    realizedCellCollarBoundary n ≫ realizedCellCollarEmbedding n =
      SSet.toTop.map (Limits.Sigma.map (fun i => (SSet.boundary.{u} (n i)).ι)) := by
  unfold realizedCellCollarBoundary realizedCellCollarEmbedding
  rw [Category.assoc, ← Category.assoc (cellFamilyCollarBoundary n),
    cellFamilyCollarBoundary_embedding]
  let A := cellBoundaryFamily n
  let B := cellSimplexFamily n
  let a := PreservesCoproduct.iso SSet.toTop A
  let b := PreservesCoproduct.iso SSet.toTop B
  apply (isColimitOfHasCoproductOfPreservesColimit SSet.toTop A).hom_ext
  rintro ⟨i⟩
  dsimp
  have ha : SSet.toTop.map (Limits.Sigma.ι A i) ≫ a.hom =
      Limits.Sigma.ι (fun j => SSet.toTop.obj (A j)) i :=
    IsColimit.comp_coconePointUniqueUpToIso_hom
      (isColimitOfHasCoproductOfPreservesColimit SSet.toTop A) (colimit.isColimit _) (Discrete.mk i)
  have hb : Limits.Sigma.ι (fun j => SSet.toTop.obj (B j)) i ≫ b.inv =
      SSet.toTop.map (Limits.Sigma.ι B i) :=
    IsColimit.comp_coconePointUniqueUpToIso_inv
      (isColimitOfHasCoproductOfPreservesColimit SSet.toTop B) (colimit.isColimit _) (Discrete.mk i)
  change SSet.toTop.map (Limits.Sigma.ι A i) ≫
      (a.hom ≫ Limits.Sigma.map (fun i => SSet.toTop.map (SSet.boundary.{u} (n i)).ι)) ≫ b.inv =
    SSet.toTop.map (Limits.Sigma.ι A i) ≫ SSet.toTop.map (Limits.Sigma.map (fun i => (SSet.boundary.{u} (n i)).ι))
  rw [← Category.assoc, ← Category.assoc, ha, Limits.Sigma.ι_map, Category.assoc, hb]
  rw [← SSet.toTop.map_comp, ← SSet.toTop.map_comp, Limits.Sigma.ι_map]

theorem realizedCellCollarBoundary_retraction :
    realizedCellCollarBoundary n ≫ realizedCellCollarRetraction n = 𝟙 _ := by
  unfold realizedCellCollarBoundary realizedCellCollarRetraction
  rw [Category.assoc, ← Category.assoc (cellFamilyCollarBoundary n),
    cellFamilyCollarBoundary_retraction, Category.id_comp, Iso.hom_inv_id]

theorem realizedCellCollarRetraction_boundary :
    realizedCellCollarRetraction n ≫ realizedCellCollarBoundary n =
      cellFamilyCollarRetraction n ≫ cellFamilyCollarBoundary n := by
  simp only [realizedCellCollarRetraction, realizedCellCollarBoundary,
    Category.assoc, Iso.inv_hom_id_assoc]

def realizedCellCollarHomotopy :
    TopCat.Homotopy (𝟙 (cellFamilyCollar n))
      (realizedCellCollarRetraction n ≫ realizedCellCollarBoundary n) :=
  (cellFamilyCollarHomotopy n).cast rfl
    (congrArg TopCat.Hom.hom (realizedCellCollarRetraction_boundary n).symm)

theorem realizedCellCollarHomotopy_fixed (s : unitInterval)
    (x : |(∐ cellBoundaryFamily n)|) :
    realizedCellCollarHomotopy n (s, realizedCellCollarBoundary n x) =
      realizedCellCollarBoundary n x :=
  cellFamilyCollarHomotopy_fixed n s _

end Sharpness.SingularAttachmentComparison

