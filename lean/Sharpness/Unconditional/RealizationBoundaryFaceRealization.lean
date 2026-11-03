import Sharpness.Unconditional.RealizationBoundaryFaces
import Mathlib.Data.Finset.Sort

/-! Identification of the actual realization of every represented simplex
face with its literal coordinate face, including the ambient inclusion. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
universe u
namespace Sharpness.RealizationBoundary
open CategoryTheory Simplicial Opposite

def finiteCoordinateFace {n : ℕ} (S : Finset (Fin (n + 1))) :
    Set (SimplexCategory.toTop.{u}.obj ⦋n⦌) :=
  {t | ∀ j, j ∉ S → (t.down : Simplex n).val j = 0}

def faceVertexMap {n k : ℕ} (S : Finset (Fin (n + 1)))
    (e : Fin (k + 1) ≃o S) : Fin (k + 1) → Fin (n + 1) := fun i => (e i).val

theorem faceVertexMap_injective {n k : ℕ} (S : Finset (Fin (n + 1)))
    (e : Fin (k + 1) ≃o S) : Function.Injective (faceVertexMap S e) :=
  Subtype.val_injective.comp e.injective

theorem range_faceVertexMap {n k : ℕ} (S : Finset (Fin (n + 1)))
    (e : Fin (k + 1) ≃o S) : Set.range (faceVertexMap S e) = S := by
  ext j
  constructor
  · rintro ⟨i, rfl⟩
    exact (e i).property
  · intro hj
    exact ⟨e.symm ⟨j, hj⟩, congrArg Subtype.val (e.apply_symm_apply _)⟩

def faceVertexHom {n k : ℕ} (S : Finset (Fin (n + 1)))
    (e : Fin (k + 1) ≃o S) : ⦋k⦌ ⟶ ⦋n⦌ :=
  SimplexCategory.Hom.mk ((OrderHom.Subtype.val _).comp e.toOrderEmbedding.toOrderHom)

def faceRepresentableIso {n k : ℕ} (S : Finset (Fin (n + 1)))
    (e : Fin (k + 1) ≃o S) : (Δ[k] : SSet.{u}) ≅ (SSet.stdSimplex.face S).toSSet :=
  SSet.stdSimplex.isoOfRepresentableBy (SSet.stdSimplex.faceRepresentableBy S k e)

theorem faceRepresentableIso_inclusion {n k : ℕ} (S : Finset (Fin (n + 1)))
    (e : Fin (k + 1) ≃o S) :
    (faceRepresentableIso.{u} S e).hom ≫ (SSet.stdSimplex.face S).ι =
      SSet.stdSimplex.map (faceVertexHom S e) := by
  ext m x
  rfl

def coordinateFaceLiftHomeo {n k : ℕ} (S : Finset (Fin (n + 1)))
    (e : Fin (k + 1) ≃o S) : coordinateFace (faceVertexMap S e) ≃ₜ finiteCoordinateFace.{u} S :=
  (Homeomorph.ulift.subtype (p := fun t : SimplexCategory.toTop.{u}.obj ⦋n⦌ =>
      t.down ∈ coordinateFace (faceVertexMap S e)) (q := coordinateFace (faceVertexMap S e))
      (fun _ => Iff.rfl)).symm.trans
    (Homeomorph.setCongr (by
      ext t
      simp only [finiteCoordinateFace, Set.mem_setOf_eq, coordinateFace, range_faceVertexMap,
        Finset.mem_coe]
      rfl))

def representedFaceHomeo {n k : ℕ} (S : Finset (Fin (n + 1)))
    (e : Fin (k + 1) ≃o S) :
    |(SSet.stdSimplex.face.{u} S).toSSet| ≃ₜ finiteCoordinateFace.{u} S :=
  (TopCat.homeoOfIso (SSet.toTop.mapIso (faceRepresentableIso.{u} S e))).symm.trans
    ((SimplexCategory.toTopHomeo ⦋k⦌).trans
      ((coordinateFaceHomeo (faceVertexMap S e) (faceVertexMap_injective S e)).trans
        (coordinateFaceLiftHomeo S e)))

/-- The face homeomorphism carries the actual realized inclusion to the
literal coordinate inclusion in the native topological simplex. -/
theorem representedFaceHomeo_inclusion {n k : ℕ} (S : Finset (Fin (n + 1)))
    (e : Fin (k + 1) ≃o S) (x : |(SSet.stdSimplex.face.{u} S).toSSet|) :
    (representedFaceHomeo S e x).val =
      (SSet.toTopSimplex.app ⦋n⦌).hom (SSet.toTop.map (SSet.stdSimplex.face S).ι x) := by
  let a := faceRepresentableIso.{u} S e
  let z := SSet.toTop.map a.inv x
  have hx : SSet.toTop.map a.hom z = x := by
    change ((SSet.toTop.mapIso a).inv ≫ (SSet.toTop.mapIso a).hom) x = x
    rw [Iso.inv_hom_id]
    rfl
  have hmap : SSet.toTop.map (SSet.stdSimplex.face S).ι x =
      SSet.toTop.map (SSet.stdSimplex.map (faceVertexHom S e)) z := by
    calc
      _ = SSet.toTop.map (SSet.stdSimplex.face S).ι (SSet.toTop.map a.hom z) :=
        congrArg (SSet.toTop.map (SSet.stdSimplex.face S).ι) hx.symm
      _ = SSet.toTop.map (a.hom ≫ (SSet.stdSimplex.face S).ι) z :=
        (ConcreteCategory.congr_hom (SSet.toTop.map_comp a.hom (SSet.stdSimplex.face S).ι) z).symm
      _ = _ := congrArg (fun f => SSet.toTop.map f z) (faceRepresentableIso_inclusion S e)
  apply ULift.ext
  change _root_.stdSimplex.map (faceVertexMap S e) (SimplexCategory.toTopHomeo ⦋k⦌ z) =
    SimplexCategory.toTopHomeo ⦋n⦌ (SSet.toTop.map (SSet.stdSimplex.face S).ι x)
  rw [hmap]
  exact (SimplexCategory.toTopHomeo_naturality_apply (faceVertexHom S e) z).symm

end Sharpness.RealizationBoundary
