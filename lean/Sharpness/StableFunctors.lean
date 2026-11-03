import Sharpness.MackeyLinearCategory
import Sharpness.MackeyCoefficientFunctors
import Sharpness.ReferenceInputs

/-! The actual compatible-family and stable-element functors on full
Mackey coefficients, over any commutative ring. The epsilon/eta
identification is natural in Mackey morphisms, not merely objectwise. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem
open CategoryTheory
variable {S R : Type u} [Group S] [Finite S] [CommRing R] (F : FusionSystem S)

abbrev compatibleElements (M : MackeyModule.{u,u,u} R F.Orbit F.mackeyShape) :=
  ((F.coefficientData M).onFull F.centricProperty).limit

abbrev stableElements (M : MackeyModule.{u,u,u} R F.Orbit F.mackeyShape) :=
  (F.coefficientData M).arrowStable F.topOrbit F.toTop

def compatibleElementsMap
    {M N : MackeyModule.{u,u,u} R F.Orbit F.mackeyShape} (f : M ⟶ N) :
    F.compatibleElements M →ₗ[R] F.compatibleElements N where
  toFun x := ⟨fun P => f.app P.obj (x.val P), by
    intro P Q a
    change N.pull a.hom (f.app Q.obj (x.val Q)) = f.app P.obj (x.val P)
    have hx : M.pull a.hom (x.val Q) = x.val P := x.property a
    exact (f.pull_comm a.hom (x.val Q)).symm.trans (congrArg (f.app P.obj) hx)⟩
  map_add' x y := by apply Subtype.ext; funext P; exact (f.app P.obj).map_add _ _
  map_smul' r x := by apply Subtype.ext; funext P; exact (f.app P.obj).map_smul _ _

def stableElementsMap
    {M N : MackeyModule.{u,u,u} R F.Orbit F.mackeyShape} (f : M ⟶ N) :
    F.stableElements M →ₗ[R] F.stableElements N where
  toFun x := ⟨f.app F.topOrbit x.val, by
    intro P Q a
    change N.pull a (N.pull (F.toTop Q) (f.app F.topOrbit x.val)) =
      N.pull (F.toTop P) (f.app F.topOrbit x.val)
    rw [← f.pull_comm (F.toTop Q), ← f.pull_comm a]
    have hx : M.pull a (M.pull (F.toTop Q) x.val) = M.pull (F.toTop P) x.val := x.property a
    exact (congrArg (f.app P) hx).trans (f.pull_comm (F.toTop P) x.val)⟩
  map_add' x y := Subtype.ext ((f.app F.topOrbit).map_add _ _)
  map_smul' r x := Subtype.ext ((f.app F.topOrbit).map_smul _ _)

def compatibleElementsFunctor :
    MackeyModule.{u,u,u} R F.Orbit F.mackeyShape ⥤ ModuleCat.{u} R where
  obj M := ModuleCat.of R (F.compatibleElements M)
  map f := ModuleCat.ofHom (F.compatibleElementsMap f)
  map_id M := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl

def stableElementsFunctor :
    MackeyModule.{u,u,u} R F.Orbit F.mackeyShape ⥤ ModuleCat.{u} R where
  obj M := ModuleCat.of R (F.stableElements M)
  map f := ModuleCat.ofHom (F.stableElementsMap f)
  map_id M := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl

instance compatibleElementsFunctor_additive : (F.compatibleElementsFunctor (R := R)).Additive where
  map_add := by
    intros
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl

instance stableElementsFunctor_additive : (F.stableElementsFunctor (R := R)).Additive where
  map_add := by
    intros
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl

instance compatibleElementsFunctor_linear : (F.compatibleElementsFunctor (R := R)).Linear R where
  map_smul := by
    intros
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl

instance stableElementsFunctor_linear : (F.stableElementsFunctor (R := R)).Linear R where
  map_smul := by
    intros
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl

def compatibleStableLinearEquiv (BLO : F.AlperinInput)
    (M : MackeyModule.{u,u,u} R F.Orbit F.mackeyShape) :
    F.compatibleElements M ≃ₗ[R] F.stableElements M :=
  (F.coefficientData M).limitCentricEquivStable F.centricProperty F.topOrbit F.toTop
    F.top_centric F.toTop_top BLO.theorem_A_10

def compatibleStableNatIso (BLO : F.AlperinInput) :
    F.compatibleElementsFunctor (R := R) ≅ F.stableElementsFunctor (R := R) :=
  NatIso.ofComponents (fun M => (F.compatibleStableLinearEquiv BLO M).toModuleIso) (by
    intro M N f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl)

end Sharpness.FusionSystem
