import Sharpness.TotalSummandProjectionAt
import Sharpness.ZeroColumnTotalProjection

/-! Native total-summand projections are natural for actual bicomplex
maps. Every total summand is checked, including those off the selected
column. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory CategoryTheory.Limits
variable {R : Type u} [CommRing R]
    (K L : HomologicalComplex₂ (ModuleCat.{u} R) (ComplexShape.up ℕ) (ComplexShape.up ℕ)) (φ : K ⟶ L)

set_option backward.isDefEq.respectTransparency false in
theorem totalMap_projection (p q n : ℕ) (h : p+q=n) :
    (HomologicalComplex₂.total.map φ (ComplexShape.up ℕ)).f n ≫ totalSummandProjectionAt L p q n h =
      totalSummandProjectionAt K p q n h ≫ (φ.f p).f q := by
  apply HomologicalComplex₂.total.hom_ext
  intro i j hij
  change i+j=n at hij
  have hm := HomologicalComplex₂.ιTotal_map K L φ (ComplexShape.up ℕ) i j n hij
  by_cases hi : i=p
  · subst i
    have hj : j=q := by omega
    subst j
    calc
      _ = (φ.f p).f q ≫ (L.ιTotal (ComplexShape.up ℕ) p q n h ≫ totalSummandProjectionAt L p q n h) :=
        (Category.assoc _ _ _).symm.trans
          ((congrArg (fun a => a ≫ totalSummandProjectionAt L p q n h) hm).trans (Category.assoc _ _ _))
      _ = (φ.f p).f q := (congrArg (fun a => (φ.f p).f q ≫ a)
        (totalSummandProjectionAt_inclusion L p q n h)).trans (Category.comp_id _)
      _ = (K.ιTotal (ComplexShape.up ℕ) p q n h ≫ totalSummandProjectionAt K p q n h) ≫ (φ.f p).f q :=
        ((congrArg (fun a => a ≫ (φ.f p).f q) (totalSummandProjectionAt_inclusion K p q n h)).trans
          (Category.id_comp _)).symm
      _ = _ := Category.assoc _ _ _
  · calc
      _ = (φ.f i).f j ≫ (L.ιTotal (ComplexShape.up ℕ) i j n hij ≫ totalSummandProjectionAt L p q n h) :=
        (Category.assoc _ _ _).symm.trans
          ((congrArg (fun a => a ≫ totalSummandProjectionAt L p q n h) hm).trans (Category.assoc _ _ _))
      _ = 0 := (congrArg (fun a => (φ.f i).f j ≫ a)
        (totalSummandProjectionAt_other L p q n i j h hij hi)).trans comp_zero
      _ = (K.ιTotal (ComplexShape.up ℕ) i j n hij ≫ totalSummandProjectionAt K p q n h) ≫ (φ.f p).f q :=
        ((congrArg (fun a => a ≫ (φ.f p).f q)
          (totalSummandProjectionAt_other K p q n i j h hij hi)).trans zero_comp).symm
      _ = _ := Category.assoc _ _ _

end Sharpness
