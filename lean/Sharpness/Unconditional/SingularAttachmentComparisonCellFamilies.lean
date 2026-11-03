import Sharpness.Unconditional.SingularAttachmentComparisonCellCollar
import Sharpness.Unconditional.SingularAttachmentComparisonCoproductHomotopy

/-! Boundary-fixed radial collars for arbitrary families of realized simplices. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness.SingularAttachmentComparison
open CategoryTheory CategoryTheory.Limits Simplicial

variable {ι : Type u} (n : ι → ℕ)

def cellFamilyBoundarySpace : TopCat.{u} :=
  ∐ fun i => SSet.toTop.obj (SSet.boundary.{u} (n i)).toSSet

def cellFamilySpace : TopCat.{u} := ∐ fun i => |(Δ[n i] : SSet.{u})|

def cellFamilyCollar : TopCat.{u} := ∐ fun i => simplexCollar.{u} (n i)

def cellFamilyCollarBoundary : cellFamilyBoundarySpace n ⟶ cellFamilyCollar n :=
  Limits.Sigma.map (fun i => simplexCollarBoundary (n i))

def cellFamilyCollarEmbedding : cellFamilyCollar n ⟶ cellFamilySpace n :=
  Limits.Sigma.map (fun i => simplexCollarEmbedding (n i))

def cellFamilyCollarRetraction : cellFamilyCollar n ⟶ cellFamilyBoundarySpace n :=
  Limits.Sigma.map (fun i => simplexCollarRetraction (n i))

theorem cellFamilyCollarEmbedding_isOpenEmbedding :
    Topology.IsOpenEmbedding (cellFamilyCollarEmbedding n) :=
  topologicalCoproductMap_isOpenEmbedding _ (fun i => simplexCollarEmbedding_isOpenEmbedding (n i))

theorem cellFamilyCollarBoundary_embedding :
    cellFamilyCollarBoundary n ≫ cellFamilyCollarEmbedding n =
      Limits.Sigma.map (fun i => SSet.toTop.map (SSet.boundary (n i)).ι) := by
  unfold cellFamilyCollarBoundary cellFamilyCollarEmbedding
  rw [Sigma.map_comp_map]
  simp only [simplexCollarBoundary_embedding]

theorem cellFamilyCollarBoundary_retraction :
    cellFamilyCollarBoundary n ≫ cellFamilyCollarRetraction n = 𝟙 _ := by
  unfold cellFamilyCollarBoundary cellFamilyCollarRetraction
  rw [Sigma.map_comp_map]
  simp only [simplexCollarBoundary_retraction, Sigma.map_id]
  rfl

def cellFamilyCollarHomotopy :
    TopCat.Homotopy (𝟙 (cellFamilyCollar n))
      (cellFamilyCollarRetraction n ≫ cellFamilyCollarBoundary n) :=
  (topologicalCoproductMapHomotopy (fun i => simplexCollarHomotopy (n i))).cast
    (congrArg TopCat.Hom.hom Sigma.map_id)
    (congrArg TopCat.Hom.hom (Sigma.map_comp_map _ _).symm)

theorem cellFamilyCollarHomotopy_inclusion (i : ι) (s : unitInterval)
    (x : simplexCollar.{u} (n i)) :
    cellFamilyCollarHomotopy n (s, Sigma.ι (fun i => simplexCollar.{u} (n i)) i x) =
      Sigma.ι (fun i => simplexCollar.{u} (n i)) i (simplexCollarHomotopy (n i) (s, x)) :=
  topologicalCoproductMapHomotopy_inclusion (fun i => simplexCollarHomotopy (n i)) i s x

theorem cellFamilyCollarHomotopy_fixed (s : unitInterval) (x : cellFamilyBoundarySpace n) :
    cellFamilyCollarHomotopy n (s, cellFamilyCollarBoundary n x) = cellFamilyCollarBoundary n x := by
  let A := fun i => SSet.toTop.obj (SSet.boundary.{u} (n i)).toSSet
  obtain ⟨⟨i, y⟩, rfl⟩ := (TopCat.homeoOfIso (TopCat.sigmaIsoSigma A)).symm.surjective x
  change cellFamilyCollarHomotopy n
      (s, cellFamilyCollarBoundary n ((TopCat.sigmaIsoSigma A).inv ⟨i, y⟩)) = _
  rw [TopCat.sigmaIsoSigma_inv_apply]
  have ha := ConcreteCategory.congr_hom
    (Sigma.ι_map (fun i => simplexCollarBoundary (n i)) i) y
  change cellFamilyCollarBoundary n (Sigma.ι A i y) =
    Sigma.ι (fun i => simplexCollar.{u} (n i)) i (simplexCollarBoundary (n i) y) at ha
  rw [ha, cellFamilyCollarHomotopy_inclusion, simplexCollarHomotopy_fixed]
  change _ = cellFamilyCollarBoundary n ((TopCat.sigmaIsoSigma A).inv ⟨i, y⟩)
  rw [TopCat.sigmaIsoSigma_inv_apply, ha]

end Sharpness.SingularAttachmentComparison

