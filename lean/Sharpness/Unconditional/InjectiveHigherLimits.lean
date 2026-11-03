import Sharpness.Unconditional.InjectiveExtLinear
import Sharpness.Unconditional.ProjectiveExtLinear
import Sharpness.Unconditional.LimitHom
import Sharpness.Unconditional.InjectiveCoefficients
import Sharpness.Unconditional.ProjectiveCoefficients
import Sharpness.ExtZeroTarget

/-! Actual higher limits are computed by applying the ordinary limit functor
to any injective resolution. The comparison is an isomorphism of modules
in every degree, including zero; it is not only an equivalence of vanishing. -/
set_option autoImplicit false
noncomputable section
universe u v
namespace Sharpness
open CategoryTheory CategoryTheory.Limits Opposite

variable (R : Type u) [CommRing R]
    {C : Type v} [Category.{u} C] [Abelian C] [Linear R C]
    [EnoughProjectives C] [EnoughInjectives C]

def extInjectiveHomologyIso (X Y : C) (I : InjectiveResolution Y) (n : ℕ) :
    ((Ext R C n).obj (op X)).obj Y ≅
      (injectiveHomComplex R X Y I).homology n := by
  letI : HasExt.{u} C := hasExt_of_enoughProjectives.{u, u, v} C
  cases n with
  | zero =>
    let H := (linearCoyoneda R C).obj (op X)
    letI : PreservesFiniteLimits (H ⋙ forget (ModuleCat R)) :=
      inferInstanceAs (PreservesFiniteLimits (coyoneda.obj (op X)))
    letI : PreservesFiniteLimits H :=
      preservesFiniteLimits_of_reflects_of_preserves H (forget (ModuleCat R))
    exact extZeroHomIso R X Y ≪≫ (H.rightDerivedZeroIsoSelf.app Y).symm ≪≫
      I.isoRightDerivedObj H 0
  | succ n =>
    exact nativeExtIsoDerivedExt R X Y n ≪≫
      (injectiveHomologyIsoDerivedExt R I X n).symm

variable {J : Type u} [Category.{u} J]

def covariantHigherLimitInjectiveResolutionIso
    (D : J ⥤ ModuleCat.{u} R) (I : InjectiveResolution D) (n : ℕ) :
    covariantHigherLimit R D n ≅
      (((lim : (J ⥤ ModuleCat.{u} R) ⥤ ModuleCat.{u} R).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj I.cocomplex).homology n :=
  extInjectiveHomologyIso R ((Functor.const J).obj (ModuleCat.of R R)) D I n ≪≫
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℕ) n).mapIso
      ((NatIso.mapHomologicalComplex (constantHomLimitIso R J)
        (ComplexShape.up ℕ)).app I.cocomplex)

def higherLimitInjectiveResolutionIso
    (D : CoefficientCategory R J) (I : InjectiveResolution D) (n : ℕ) :
    higherLimit D n ≅
      (((lim : (CoefficientCategory R J) ⥤ ModuleCat.{u} R).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj I.cocomplex).homology n :=
  covariantHigherLimitInjectiveResolutionIso R D I n

end Sharpness
