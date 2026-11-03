import Sharpness.Unconditional.LinearAdjunction
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.CategoryTheory.Linear.FunctorCategory

/-! The module of maps from the constant rank-one diagram is naturally the
ordinary inverse limit. This comparison is linear and natural in coefficients. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness
open CategoryTheory CategoryTheory.Limits Opposite

variable (R : Type u) [CommRing R] (J : Type u) [Category.{u} J]

instance constantModuleFunctor_additive :
    (Functor.const J : ModuleCat.{u} R ⥤ J ⥤ ModuleCat.{u} R).Additive where
  map_add := by intros; rfl

instance constantModuleFunctor_linear :
    (Functor.const J : ModuleCat.{u} R ⥤ J ⥤ ModuleCat.{u} R).Linear R where
  map_smul := by intros; rfl

instance limitModuleFunctor_linear :
    (lim : (J ⥤ ModuleCat.{u} R) ⥤ ModuleCat.{u} R).Linear R :=
  rightAdjointLinear R constLimAdj

/-- Linear evaluation at one after the constant/limit adjunction. -/
def constantHomLimitEquiv (D : J ⥤ ModuleCat.{u} R) :
    ((Functor.const J).obj (ModuleCat.of R R) ⟶ D) ≃ₗ[R] ↥(limit D : ModuleCat.{u} R) :=
  (adjunctionHomLinearEquiv R constLimAdj (ModuleCat.of R R) D).trans
    (ModuleCat.homLinearEquiv.trans
      (LinearMap.ringLmapEquivSelf R R ↥(limit D : ModuleCat.{u} R)))

/-- Linear Hom from the constant rank-one diagram is naturally the limit functor. -/
def constantHomLimitIso :
    (linearCoyoneda R (J ⥤ ModuleCat.{u} R)).obj
      (op ((Functor.const J).obj (ModuleCat.of R R))) ≅
        (lim : (J ⥤ ModuleCat.{u} R) ⥤ ModuleCat.{u} R) :=
  NatIso.ofComponents (fun D => (constantHomLimitEquiv R J D).toModuleIso) (by
    intro D E α
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    change (constLimAdj.homEquiv (ModuleCat.of R R) E (f ≫ α)) (1 : R) =
      (lim.map α) ((constLimAdj.homEquiv (ModuleCat.of R R) D f) (1 : R))
    rw [Adjunction.homEquiv_naturality_right]
    rfl)

end Sharpness
