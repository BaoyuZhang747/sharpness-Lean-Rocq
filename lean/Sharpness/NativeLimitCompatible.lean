import Sharpness.Unconditional.DegreeZero
import Mathlib.Algebra.Category.ModuleCat.Limits

/-! The native inverse limit of an actual module-valued coefficient
functor is its explicit module of compatible families. All components
are the native limit projections. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness.Coefficient
open CategoryTheory CategoryTheory.Limits Opposite
variable {R C : Type u} [CommRing R] [Category.{u} C]
    (D : Coefficient.{u,u,u} R C)

def nativeLimitToCompatible : CategoryTheory.Limits.limit D.asFunctor ⟶ ModuleCat.of R D.limit :=
  ModuleCat.ofHom
    { toFun x := ⟨fun P => limit.π D.asFunctor (op P) x, by
        intro P Q f
        exact congrArg (fun h => h x) (limit.w D.asFunctor f.op)⟩
      map_add' x y := by apply Subtype.ext; funext P; exact (limit.π D.asFunctor (op P)).hom.map_add x y
      map_smul' r x := by apply Subtype.ext; funext P; exact (limit.π D.asFunctor (op P)).hom.map_smul r x }

def compatibleEvaluation (P : C) : ModuleCat.of R D.limit ⟶ ModuleCat.of R (D.Value P) :=
  ModuleCat.ofHom
    { toFun x := x.val P
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }

def compatibleCone : Cone D.asFunctor where
  pt := ModuleCat.of R D.limit
  π :=
    { app P := D.compatibleEvaluation P.unop
      naturality {P Q} f := by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        exact (x.property f.unop).symm }

def compatibleToNativeLimit : ModuleCat.of R D.limit ⟶ CategoryTheory.Limits.limit D.asFunctor :=
  limit.lift _ D.compatibleCone

@[reassoc]
theorem compatibleToNativeLimit_projection (P : C) :
    D.compatibleToNativeLimit ≫ limit.π D.asFunctor (op P) = D.compatibleEvaluation P :=
  limit.lift_π _ _

@[reassoc]
theorem nativeLimitToCompatible_evaluation (P : C) :
    D.nativeLimitToCompatible ≫ D.compatibleEvaluation P = limit.π D.asFunctor (op P) := rfl

def nativeLimitCompatibleIso : CategoryTheory.Limits.limit D.asFunctor ≅ ModuleCat.of R D.limit where
  hom := D.nativeLimitToCompatible
  inv := D.compatibleToNativeLimit
  hom_inv_id := by
    apply limit.hom_ext
    intro P
    change (D.nativeLimitToCompatible ≫ D.compatibleToNativeLimit) ≫
      limit.π D.asFunctor (op P.unop) = (𝟙 _) ≫ limit.π D.asFunctor (op P.unop)
    simp only [Category.assoc, compatibleToNativeLimit_projection,
      nativeLimitToCompatible_evaluation, Category.id_comp]
  inv_hom_id := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    funext P
    exact congrArg (fun h => h x) (D.compatibleToNativeLimit_projection P)

end Sharpness.Coefficient
