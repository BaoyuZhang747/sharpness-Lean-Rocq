import Sharpness.Unconditional.CostructuredHorizontalRowsContraction
import Sharpness.Unconditional.BisimplicialAlexanderWhitneyNaturality

/-! Actual diagonal comparison maps for the flipped comma replacement.
The final theorem is an explicit intermediate implication from native
Alexander-Whitney and total-map quasi-isomorphisms, not a Thomason input. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness
open CategoryTheory Simplicial Opposite

/-- Flipping the two directions preserves the actual diagonal simplicial set. -/
def bisimplicialDiagonalFlipIso (X : SimplicialObject SSet.{u}) :
    bisimplicialDiagonal X.flip ≅ bisimplicialDiagonal X :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro p r f
    change ((X.obj p).map f ≫ (X.map f).app r) ≫ 𝟙 _ =
      𝟙 _ ≫ ((X.map f).app p ≫ (X.obj r).map f)
    rw [Category.comp_id, Category.id_comp]
    exact (X.map f).naturality f)

theorem bisimplicialDiagonalFlipIso_naturality {X Y : SimplicialObject SSet.{u}}
    (f : X ⟶ Y) :
    bisimplicialDiagonalMap ((flipFunctor _ _ _).map f) ≫ (bisimplicialDiagonalFlipIso Y).hom =
      (bisimplicialDiagonalFlipIso X).hom ≫ bisimplicialDiagonalMap f := by
  apply NatTrans.ext
  funext p
  apply ConcreteCategory.ext_apply
  intro x
  rfl

def bisimplicialConstantDiagonalIso (X : SSet.{u}) :
    bisimplicialDiagonal ((CategoryTheory.Functor.const SimplexCategoryᵒᵖ).obj X) ≅ X :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro p r f
    change (𝟙 _ ≫ X.map f) ≫ 𝟙 _ = 𝟙 _ ≫ X.map f
    simp only [Category.id_comp, Category.comp_id])

variable {X Y : SimplicialObject SSet.{u}} (f : X ⟶ Y) (R : Type u) [CommRing R]

/-- Two-out-of-three applied to the already proved strict naturality square. -/
theorem bisimplicialDiagonalChainsMap_quasiIso_of_AW_total
    (hX : QuasiIso (bisimplicialAlexanderWhitney X R))
    (hY : QuasiIso (bisimplicialAlexanderWhitney Y R))
    (hTotal : QuasiIso (bisimplicialTotalChainsMap f R)) :
    QuasiIso (bisimplicialDiagonalChainsMap f R) := by
  letI := hX
  letI := hY
  letI := hTotal
  haveI : QuasiIso (bisimplicialDiagonalChainsMap f R ≫ bisimplicialAlexanderWhitney Y R) := by
    rw [bisimplicialAlexanderWhitney_naturality]
    infer_instance
  exact _root_.quasiIso_of_comp_right (bisimplicialDiagonalChainsMap f R)
    (bisimplicialAlexanderWhitney Y R)

variable {C D : Type u} [Category.{u} C] [Category.{u} D] (T : C ⥤ D)

def costructuredFlippedDiagonalSourceIso :
    bisimplicialDiagonal (simplicialSetReplacement (costructuredNerveDiagram T)).flip ≅
      simplicialReplacementDiagonal (costructuredNerveDiagram T) :=
  bisimplicialDiagonalFlipIso _

def costructuredFlippedDiagonalTargetIso :
    bisimplicialDiagonal
      ((CategoryTheory.Functor.const SimplexCategoryᵒᵖ).obj (CategoryTheory.nerve C)).flip ≅
      CategoryTheory.nerve C :=
  (bisimplicialDiagonalFlipIso _).trans (bisimplicialConstantDiagonalIso _)

/-- The diagonal of the actual flipped augmentation is the actual cocone
augmentation, under the explicit diagonal identifications. -/
theorem costructuredFlippedDiagonalAugmentation_square :
    bisimplicialDiagonalMap (costructuredFlippedAugmentation T) ≫
        (costructuredFlippedDiagonalTargetIso (C := C)).hom =
      (costructuredFlippedDiagonalSourceIso T).hom ≫
        simplicialReplacementDiagonalAugmentation (costructuredNerveDiagram T)
          (costructuredNerveCocone T) := by
  apply NatTrans.ext
  funext p
  apply ConcreteCategory.ext_apply
  rintro ⟨s, x⟩
  rfl

/-- A native quasi-isomorphism for the flipped diagonal gives one for the
literal cocone augmentation, without any supplied comparison isomorphism. -/
theorem costructuredDiagonalAugmentation_quasiIso_of_flipped
    (h : QuasiIso (bisimplicialDiagonalChainsMap (costructuredFlippedAugmentation T) R)) :
    QuasiIso (SSet.chainComplexMap
      (simplicialReplacementDiagonalAugmentation (costructuredNerveDiagram T)
        (costructuredNerveCocone T)) (ModuleCat.of R R)) := by
  let J := (SSet.chainComplexFunctor (ModuleCat.{u} R)).obj (ModuleCat.of R R)
  haveI : QuasiIso (J.map (bisimplicialDiagonalMap (costructuredFlippedAugmentation T))) := h
  have hs := congrArg J.map (costructuredFlippedDiagonalAugmentation_square T)
  rw [J.map_comp, J.map_comp] at hs
  haveI : QuasiIso (J.map (costructuredFlippedDiagonalSourceIso T).hom ≫
      J.map (simplicialReplacementDiagonalAugmentation (costructuredNerveDiagram T)
        (costructuredNerveCocone T))) := by
    rw [← hs]
    infer_instance
  exact _root_.quasiIso_of_comp_left
    (J.map (costructuredFlippedDiagonalSourceIso T).hom)
    (J.map (simplicialReplacementDiagonalAugmentation (costructuredNerveDiagram T)
      (costructuredNerveCocone T)))

/-- Explicit remaining algebraic premises: only the constructed AW maps
and the constructed total map must be shown to be quasi-isomorphisms. -/
theorem costructuredDiagonalAugmentation_quasiIso_of_AW_total
    (hSource : QuasiIso (bisimplicialAlexanderWhitney
      (simplicialSetReplacement (costructuredNerveDiagram T)).flip R))
    (hTarget : QuasiIso (bisimplicialAlexanderWhitney
      ((CategoryTheory.Functor.const SimplexCategoryᵒᵖ).obj (CategoryTheory.nerve C)).flip R))
    (hTotal : QuasiIso (bisimplicialTotalChainsMap (costructuredFlippedAugmentation T) R)) :
    QuasiIso (SSet.chainComplexMap
      (simplicialReplacementDiagonalAugmentation (costructuredNerveDiagram T)
        (costructuredNerveCocone T)) (ModuleCat.of R R)) :=
  costructuredDiagonalAugmentation_quasiIso_of_flipped R T
    (bisimplicialDiagonalChainsMap_quasiIso_of_AW_total
      (costructuredFlippedAugmentation T) R hSource hTarget hTotal)

end Sharpness
