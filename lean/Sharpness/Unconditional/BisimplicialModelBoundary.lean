import Sharpness.Unconditional.BisimplicialModelAugmentation

/-! The concrete degree-one lifting condition for the Alexander–Whitney inverse. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
universe u
namespace Sharpness
open CategoryTheory CategoryTheory.Limits

instance bisimplicialAlexanderWhitney_zero_isIso
    (X : CategoryTheory.SimplicialObject SSet.{u}) (R : Type u) [CommRing R] :
    IsIso ((bisimplicialAlexanderWhitney X R).f 0) :=
  (bisimplicialAlexanderWhitneyZeroIso X R).isIso_hom

@[reassoc]
theorem bisimplicialRepresentable_zeroInv_augmentation
    (R : Type u) [CommRing R] (p q : ℕ) :
    (bisimplicialAlexanderWhitneyZeroIso (bisimplicialRepresentable p q) R).inv ≫
      (bisimplicialRepresentableDiagonalHomotopyEquiv R p q).hom.f 0 =
      (bisimplicialRepresentableTotalHomotopyEquiv R p q).hom.f 0 := by
  rw [← bisimplicialRepresentable_AW_augmentation_zero R p q, ← Category.assoc]
  have hi := (bisimplicialAlexanderWhitneyZeroIso (bisimplicialRepresentable p q) R).inv_hom_id
  change _ ≫ (bisimplicialAlexanderWhitney (bisimplicialRepresentable p q) R).f 0 = 𝟙 _ at hi
  rw [hi, Category.id_comp]

/-- Every total degree-one boundary lifts, under the actual degree-zero
inverse, to a diagonal degree-one boundary on each actual representable model. -/
theorem bisimplicialRepresentable_boundary_of_total_boundary
    (R : Type u) [CommRing R] (p q : ℕ)
    (x : (bisimplicialTotalChains (bisimplicialRepresentable p q) R).X 1) :
    ∃ y : (bisimplicialDiagonalChains (bisimplicialRepresentable p q) R).X 1,
      (bisimplicialDiagonalChains (bisimplicialRepresentable p q) R).d 1 0 y =
        (bisimplicialAlexanderWhitneyZeroIso (bisimplicialRepresentable p q) R).inv
          ((bisimplicialTotalChains (bisimplicialRepresentable p q) R).d 1 0 x) := by
  apply chain_boundary_of_homotopyEquiv_single₀
    (bisimplicialRepresentableDiagonalHomotopyEquiv R p q)
  have hc : (bisimplicialTotalChains (bisimplicialRepresentable p q) R).d 1 0 ≫
      (bisimplicialRepresentableTotalHomotopyEquiv R p q).hom.f 0 = 0 := by
    rw [← (bisimplicialRepresentableTotalHomotopyEquiv R p q).hom.comm 1 0,
      HomologicalComplex.single_obj_d, comp_zero]
  have ha := congrArg (fun a => a.hom
      ((bisimplicialTotalChains (bisimplicialRepresentable p q) R).d 1 0 x))
    (bisimplicialRepresentable_zeroInv_augmentation R p q)
  exact ha.trans (congrArg (fun a => a.hom x) hc)

end Sharpness
