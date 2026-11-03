import Sharpness.ReferenceInputs

/-! Degree-zero higher limits are compatible families. This constructs the
previously supplied `DegreeZeroInput` from mathlib's derived-functor comparison
and evaluation of a linear natural transformation at the scalar `1`. -/

set_option autoImplicit false
noncomputable section
universe u v

namespace Sharpness
open CategoryTheory CategoryTheory.Limits Opposite

variable (R : Type u) [CommRing R]
    {A : Type v} [Category.{u} A] [Abelian A] [Linear R A] [EnoughProjectives A]

/-- The project's module-valued Ext in degree zero is the actual hom module. -/
def extZeroHomIso (X Y : A) :
    ((Ext R A 0).obj (op X)).obj Y ≅ ModuleCat.of R (X ⟶ Y) := by
  let F := (linearYoneda R A).obj Y
  letI : PreservesFiniteLimits (F ⋙ forget (ModuleCat R)) :=
    inferInstanceAs (PreservesFiniteLimits (yoneda.obj Y))
  letI : PreservesFiniteLimits F :=
    preservesFiniteLimits_of_reflects_of_preserves F (forget (ModuleCat R))
  letI : PreservesFiniteColimits F.rightOp := preservesFiniteColimits_rightOp F
  exact (F.rightOp.leftDerivedZeroIsoSelf.app X).unop.symm

namespace Coefficient
variable {R} {C : Type u} [Category.{u} C] (D : Coefficient.{u,u,u} R C)

/-- The module-valued functor associated to concrete coefficient data. -/
def asFunctor : CoefficientCategory R C where
  obj P := ModuleCat.of R (D.Value P.unop)
  map f := ModuleCat.ofHom (D.pull f.unop)
  map_id P := ModuleCat.hom_ext (D.pull_id P.unop)
  map_comp f g := ModuleCat.hom_ext (D.pull_comp g.unop f.unop)

/-- A map out of the constant free rank-one diagram is a compatible family. -/
def homConstantEquivLimit :
    (constantCoefficient R C ⟶ D.asFunctor) ≃ₗ[R] D.limit where
  toFun a := ⟨fun P => a.app (op P) (1 : R), by
    intro P Q f
    have h := congrArg (fun t => t (1 : R)) (a.naturality f.op)
    exact h.symm⟩
  invFun x :=
    { app := fun P => ModuleCat.ofHom
        { toFun := fun r => r • x.val P.unop
          map_add' := fun r s => add_smul r s _
          map_smul' := fun r s => (smul_smul r s _).symm }
      naturality := by
        intro P Q f
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro r
        change r • x.val Q.unop = D.pull f.unop (r • x.val P.unop)
        rw [map_smul, x.property f.unop] }
  left_inv a := by
    apply NatTrans.ext
    funext P
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    change R at r
    change r • (a.app P).hom (1 : R) = (a.app P).hom r
    have h := (a.app P).hom.map_smul r (1 : R)
    change (a.app P).hom (r * (1 : R)) = r • (a.app P).hom (1 : R) at h
    simpa only [mul_one] using h.symm
  right_inv x := by
    apply Subtype.ext
    funext P
    exact one_smul R (x.val P)
  map_add' a b := rfl
  map_smul' r a := rfl

/-- The actual Ext-valued zeroth higher limit agrees with compatible families. -/
def higherLimitZeroIso [EnoughProjectives (CoefficientCategory R C)] :
    higherLimit D.asFunctor 0 ≅ ModuleCat.of R D.limit :=
  extZeroHomIso R _ _ ≪≫ D.homConstantEquivLimit.toModuleIso

end Coefficient

namespace FusionSystem
variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)
    {k : Type u} [Field k] [EnoughProjectives (CoefficientCategory k F.CentricOrbit)]

/-- Degree-zero identification is proved, rather than supplied as a reference. -/
def provedDegreeZeroInput : F.DegreeZeroInput (k := k) where
  AKO_III_5_3 M := ((F.coefficientData M).onFull F.centricProperty).higherLimitZeroIso

end FusionSystem
end Sharpness
