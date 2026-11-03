import Sharpness.Unconditional.BisimplicialModelExactness
import Sharpness.Unconditional.BisimplicialAlexanderWhitneyNaturality

/-! Degree-zero compatibility of the actual Alexander–Whitney map and the
constructed model contractions. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
universe u
namespace Sharpness
open CategoryTheory CategoryTheory.Limits Simplicial Opposite

@[simp]
theorem alexanderWhitneySimplex_zero_zero (X : SimplicialObject SSet.{u})
    (x : (bisimplicialDiagonal X).obj (op ⦋0⦌)) :
    alexanderWhitneySimplex X 0 0 0 rfl x = x := by
  rw [alexanderWhitneySimplex_zero]
  have h : SimplexCategory.const ⦋0⦌ ⦋0⦌ 0 = 𝟙 _ := Subsingleton.elim _ _
  rw [h, op_id, X.map_id]
  rfl

theorem bisimplicialAlexanderWhitney_zero_eq_inclusion
    (X : SimplicialObject SSet.{u}) (R : Type u) [CommRing R] :
    (bisimplicialAlexanderWhitney X R).f 0 =
      (bisimplicialChainBicomplex X R).ιTotal (ComplexShape.down ℕ) 0 0 0 rfl := by
  apply chainTotal_projection_hom_ext
  intro p q hpq
  obtain rfl : p=0 := by omega
  obtain rfl : q=0 := by omega
  apply SSet.chainComplex_hom_ext
  intro x
  rw [bisimplicialAlexanderWhitney_component, chainTotalProjection_inclusion]
  change (X.obj (op ⦋0⦌)).ιChainComplex (R := ModuleCat.of R R)
    (alexanderWhitneySimplex X 0 0 0 rfl x) =
    (X.obj (op ⦋0⦌)).ιChainComplex x ≫ 𝟙 _
  rw [Category.comp_id, alexanderWhitneySimplex_zero_zero]

def bisimplicialAlexanderWhitneyZeroIso (X : SimplicialObject SSet.{u})
    (R : Type u) [CommRing R] :
    (bisimplicialDiagonalChains X R).X 0 ≅ (bisimplicialTotalChains X R).X 0 where
  hom := (bisimplicialAlexanderWhitney X R).f 0
  inv := chainTotalProjection (bisimplicialChainBicomplex X R) 0 0 0 rfl
  hom_inv_id := by
    rw [bisimplicialAlexanderWhitney_zero_eq_inclusion, chainTotalProjection_inclusion]
    rfl
  inv_hom_id := by
    rw [bisimplicialAlexanderWhitney_zero_eq_inclusion]
    apply HomologicalComplex₂.total.hom_ext
    intro p q hpq
    change p+q=0 at hpq
    obtain rfl : p=0 := by omega
    obtain rfl : q=0 := by omega
    rw [← Category.assoc, chainTotalProjection_inclusion, Category.id_comp]
    exact (Category.comp_id _).symm


theorem bisimplicialExternalProduct_AW_augmentation_zero
    (R : Type u) [CommRing R] (P Q : SSet.Augmented.{u})
    (eP : SimplicialObject.Augmented.ExtraDegeneracy P)
    (eQ : SimplicialObject.Augmented.ExtraDegeneracy Q) :
    (bisimplicialAlexanderWhitney (bisimplicialExternalProduct P.left Q.left) R).f 0 ≫
      (bisimplicialExternalProductTotalHomotopyEquiv R P Q eP eQ).hom.f 0 =
    ((augmentedSSetProductExtraDegeneracy P Q eP eQ).map
      (sigmaConst.obj (ModuleCat.of R R))).homotopyEquiv.hom.f 0 := by
  let H := ((bisimplicialHorizontalExtraDegeneracy P Q eP).map
    (simplicialChainsFunctor R)).homotopyEquiv
  let V := ((augmentedSSetProductExtraDegeneracy
    (SimplicialObject.Augmented.const.obj P.right) Q
    (SimplicialObject.Augmented.ExtraDegeneracy.const P.right) eQ).map
    (sigmaConst.obj (ModuleCat.of R R))).homotopyEquiv
  let B := chainOuterSingle ((simplicialChainsFunctor R).obj
    (bisimplicialHorizontalAugmented P Q).right)
  change (bisimplicialAlexanderWhitney (bisimplicialExternalProduct P.left Q.left) R).f 0 ≫
    ((HomologicalComplex₂.total.map H.hom (ComplexShape.down ℕ)).f 0 ≫
      (chainTotalProjection B 0 0 0 rfl ≫ V.hom.f 0)) = _
  rw [bisimplicialAlexanderWhitney_zero_eq_inclusion, ← Category.assoc,
    HomologicalComplex₂.ιTotal_map, Category.assoc]
  change (H.hom.f 0).f 0 ≫ (B.ιTotal (ComplexShape.down ℕ) 0 0 0 rfl ≫
    chainTotalProjection B 0 0 0 rfl ≫ V.hom.f 0) = _
  rw [← Category.assoc (B.ιTotal (ComplexShape.down ℕ) 0 0 0 rfl)
    (chainTotalProjection B 0 0 0 rfl) (V.hom.f 0), chainTotalProjection_inclusion,
    Category.id_comp]
  simp only [H, V, SimplicialObject.Augmented.ExtraDegeneracy.homotopyEquiv,
    AlgebraicTopology.AlternatingFaceMapComplex.ε_app_f_zero]
  change (sigmaConst.obj (ModuleCat.of R R)).map
      (((bisimplicialHorizontalAugmented P Q).hom.app (op ⦋0⦌)).app (op ⦋0⦌)) ≫
    (sigmaConst.obj (ModuleCat.of R R)).map
      ((augmentedSSetProduct (SimplicialObject.Augmented.const.obj P.right) Q).hom.app (op ⦋0⦌)) =
    (sigmaConst.obj (ModuleCat.of R R)).map ((augmentedSSetProduct P Q).hom.app (op ⦋0⦌))
  rw [← Functor.map_comp]
  rfl

theorem bisimplicialRepresentable_AW_augmentation_zero
    (R : Type u) [CommRing R] (p q : ℕ) :
    (bisimplicialAlexanderWhitney (bisimplicialRepresentable p q) R).f 0 ≫
      (bisimplicialRepresentableTotalHomotopyEquiv R p q).hom.f 0 =
      (bisimplicialRepresentableDiagonalHomotopyEquiv R p q).hom.f 0 :=
  bisimplicialExternalProduct_AW_augmentation_zero R _ _
    (SSet.Augmented.StandardSimplex.extraDegeneracy ⦋p⦌)
    (SSet.Augmented.StandardSimplex.extraDegeneracy ⦋q⦌)

end Sharpness
