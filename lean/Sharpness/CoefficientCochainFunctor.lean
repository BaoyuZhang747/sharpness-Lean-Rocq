import Sharpness.CoefficientReplacement
import Sharpness.HigherLimitFunctor

/-! The actual category coefficient cochains form a linear functor of
the coefficient diagram, with coordinatewise action on cochains. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory Simplicial Opposite
variable {R C : Type u} [CommRing R] [Category.{u} C]
    {M N : CoefficientCategory R C}

def coefficientReplacementNatTrans (a : M ⟶ N) : coefficientReplacement M ⟶ coefficientReplacement N where
  app i := ModuleCat.ofHom (LinearMap.pi (fun s =>
    (a.app (op (chainHead s))).hom.comp (LinearMap.proj s)))
  naturality {i j} f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext s
    exact congrArg (fun t => t (x (restrictCategoryChain f s)))
      (a.naturality (categoryChainHeadArrow f s).op)

def coefficientReplacementFunctor : CoefficientCategory R C ⥤ CosimplicialObject (ModuleCat.{u} R) where
  obj := coefficientReplacement
  map := coefficientReplacementNatTrans
  map_id M := by
    apply NatTrans.ext
    funext i
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl
  map_comp a b := by
    apply NatTrans.ext
    funext i
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl

def coefficientCochainFunctor : CoefficientCategory R C ⥤ CochainComplex (ModuleCat.{u} R) ℕ :=
  coefficientReplacementFunctor ⋙ AlgebraicTopology.alternatingCofaceMapComplex (ModuleCat.{u} R)

instance coefficientCochainFunctor_additive : (coefficientCochainFunctor (R := R) (C := C)).Additive where
  map_add := by
    intros
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl

instance coefficientCochainFunctor_linear : (coefficientCochainFunctor (R := R) (C := C)).Linear R where
  map_smul := by
    intros
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl

def coefficientCohomologyFunctor (n : ℕ) : CoefficientCategory R C ⥤ ModuleCat.{u} R :=
  coefficientCochainFunctor ⋙ HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℕ) n

end Sharpness
