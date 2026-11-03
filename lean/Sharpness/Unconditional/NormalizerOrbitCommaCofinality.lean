import Sharpness.Unconditional.NormalizerOrbitPointedFirstCoreflection
import Sharpness.Unconditional.NormalizerOrbitPointedSubgroupsContraction
import Sharpness.Unconditional.QuillenAChains

/-! The actual undercategories of the pair-to-centric-orbit functor are
homologically contractible. All image, prefix and adjunction constructions
are proved; the homological comma criterion is the native chain theorem. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
noncomputable section
universe u v w

namespace Sharpness
open CategoryTheory CategoryTheory.Limits

private theorem nerveStar_quasiIso_of_map
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    {A : Type v} [Category.{w} A] [Preadditive A]
    [HasCoproducts.{u} A] [CategoryWithHomology A]
    (T : C ⥤ D) (R : A)
    [QuasiIso (SSet.chainComplexMap (nerveMap T) R)]
    [QuasiIso (SSet.chainComplexMap (nerveMap (Functor.star.{u} D)) R)] :
    QuasiIso (SSet.chainComplexMap (nerveMap (Functor.star.{u} C)) R) := by
  have he : T ⋙ Functor.star.{u} D = Functor.star.{u} C := Functor.punit_ext' _ _
  have hc : SSet.chainComplexMap (nerveMap (Functor.star.{u} C)) R =
      SSet.chainComplexMap (nerveMap T) R ≫
        SSet.chainComplexMap (nerveMap (Functor.star.{u} D)) R := by
    rw [← he]
    exact ((SSet.chainComplexFunctor A).obj R).map_comp
      (nerveMap T) (nerveMap (Functor.star.{u} D))
  rw [hc]
  infer_instance

namespace FusionSystem
variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)
  (p : ℕ) [Fact p.Prime] (hS : IsPGroup p S) (sat : F.Saturated p)
  (P : F.CentricOrbit)

include hS sat

theorem normalizerPointedFirstUnderProjection_quasiIso
    (B : F.NormalizerPointedSubgroup P)
    {A : Type v} [Category.{w} A] [Preadditive A]
    [HasCoproducts.{u} A] [CategoryWithHomology A] (R : A) :
    QuasiIso (SSet.chainComplexMap
      (nerveMap (Functor.star.{u} (F.NormalizerPointedFirstUnder P B))) R) := by
  haveI := nerveAdjunction_right_quasiIso
    (F.normalizerPointedFirstCoreflectionAdjunction p hS sat P B) R
  haveI := nerveAdjunction_left_quasiIso (F.normalizerPointedFirstPointAdjunction P B) R
  exact nerveStar_quasiIso_of_map (F.normalizerPointedFirstCoreflection p hS sat P B) R

theorem normalizerOrbitPointedFirst_quasiIso (R : Type u) [CommRing R] :
    QuasiIso (SSet.chainComplexMap
      (nerveMap (F.normalizerOrbitPointedFirst P)) (ModuleCat.of R R)) :=
  nerveMap_quasiIso_of_structured_fibres (F.normalizerOrbitPointedFirst P) R
    (fun B => F.normalizerPointedFirstUnderProjection_quasiIso p hS sat P B (ModuleCat.of R R))

theorem normalizerOrbitPointedProjection_quasiIso (R : Type u) [CommRing R] :
    QuasiIso (SSet.chainComplexMap
      (nerveMap (Functor.star.{u} (F.NormalizerOrbitPointed P))) (ModuleCat.of R R)) := by
  haveI := F.normalizerOrbitPointedFirst_quasiIso p hS sat P R
  haveI := F.normalizerPointedSubgroupProjection_quasiIso P (ModuleCat.of R R)
  exact nerveStar_quasiIso_of_map (F.normalizerOrbitPointedFirst P) (ModuleCat.of R R)

/-- The literal comma-augmentation map for the actual forgetful functor.
This is the input to all-coefficient homological cofinality. -/
theorem normalizerOrbitUnderProjection_quasiIso (R : Type u) [CommRing R] :
    QuasiIso (SSet.chainComplexMap
      (nerveMap (Functor.star.{u} (StructuredArrow P F.normalizerOrbitPairForget)))
      (ModuleCat.of R R)) := by
  haveI := nerveAdjunction_right_quasiIso (F.normalizerOrbitImageCoreflectionAdjunction P)
    (ModuleCat.of R R)
  haveI := F.normalizerOrbitPointedProjection_quasiIso p hS sat P R
  exact nerveStar_quasiIso_of_map (F.normalizerOrbitImageCoreflection P) (ModuleCat.of R R)

end FusionSystem
end Sharpness
