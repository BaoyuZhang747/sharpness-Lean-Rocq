import Mathlib.CategoryTheory.FiberedCategory.Fiber
import Mathlib.CategoryTheory.FiberedCategory.Fibered
import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Limits.Final

/-! The inclusion of a fiber into the comma category computing a right Kan
extension has a right adjoint. Its value is the chosen cartesian pullback.
Thus this inclusion is initial, and limits of the comma diagram are limits
over the actual fiber. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
universe u v

namespace Sharpness
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open CategoryTheory.Functor.IsPreFibered

variable {A : Type u} {B : Type v} [Category A] [Category B]
    (p : A ⥤ B) (b : B)

/-- The canonical inclusion of a strict fiber into the right-Kan comma category. -/
def fiberToComma : Fiber p b ⥤ StructuredArrow b p where
  obj X := StructuredArrow.mk (eqToHom X.property.symm)
  map {X Y} f := StructuredArrow.homMk f.val (by
    haveI := f.property
    rw [IsHomLift.fac' p (𝟙 b) f.val]
    simp)
  map_id _ := StructuredArrow.hom_ext _ _ rfl
  map_comp _ _ := StructuredArrow.hom_ext _ _ rfl

variable [p.IsPreFibered]

/-- The cartesian pullback of an object of the comma category lies in the fiber. -/
def commaPullbackObj (Y : StructuredArrow b p) : Fiber p b :=
  ⟨pullbackObj rfl Y.hom, pullbackObj_proj rfl Y.hom⟩

instance comma_hom_isHomLift (X : Fiber p b) (Y : StructuredArrow b p)
    (f : (fiberToComma p b).obj X ⟶ Y) : p.IsHomLift Y.hom f.right := by
  apply IsHomLift.of_fac p _ _ X.property rfl
  have h := (StructuredArrow.w f).symm
  change Y.hom = eqToHom X.property.symm ≫ p.map f.right at h
  simpa only [eqToHom_refl, Category.comp_id] using h

/-- Cartesian factorization gives the adjunction's hom equivalence. -/
def fiberCommaHomEquiv (X : Fiber p b) (Y : StructuredArrow b p) :
    ((fiberToComma p b).obj X ⟶ Y) ≃ (X ⟶ commaPullbackObj p b Y) where
  toFun f := ⟨IsCartesian.map p Y.hom (pullbackMap rfl Y.hom) f.right, inferInstance⟩
  invFun f := StructuredArrow.homMk (f.val ≫ pullbackMap rfl Y.hom) (by
    haveI := f.property
    haveI : p.IsHomLift Y.hom (f.val ≫ pullbackMap rfl Y.hom) := inferInstance
    rw [IsHomLift.fac' p Y.hom (f.val ≫ pullbackMap rfl Y.hom)]
    simp [fiberToComma])
  left_inv f := StructuredArrow.hom_ext _ _
    (IsCartesian.fac p Y.hom (pullbackMap rfl Y.hom) f.right)
  right_inv f := by
    apply Subtype.ext
    haveI := f.property
    exact (IsCartesian.map_uniq p Y.hom (pullbackMap rfl Y.hom)
      (f.val ≫ pullbackMap rfl Y.hom) f.val rfl).symm

theorem fiberCommaHomEquiv_natural (X' X : Fiber p b) (Y : StructuredArrow b p)
    (f : X' ⟶ X) (g : (fiberToComma p b).obj X ⟶ Y) :
    fiberCommaHomEquiv p b X' Y ((fiberToComma p b).map f ≫ g) =
      f ≫ fiberCommaHomEquiv p b X Y g := by
  apply Subtype.ext
  haveI := f.property
  change IsCartesian.map p Y.hom (pullbackMap rfl Y.hom) (f.val ≫ g.right) =
    f.val ≫ IsCartesian.map p Y.hom (pullbackMap rfl Y.hom) g.right
  apply (IsCartesian.map_uniq p Y.hom (pullbackMap rfl Y.hom)
    (f.val ≫ g.right) _ ?_).symm
  simp only [Category.assoc, IsCartesian.fac]

/-- The pullback right adjoint of the fiber inclusion into the comma category. -/
def commaPullback : StructuredArrow b p ⥤ Fiber p b :=
  Adjunction.rightAdjointOfEquiv (fiberCommaHomEquiv p b)
    (fiberCommaHomEquiv_natural p b)

def fiberCommaAdjunction : fiberToComma p b ⊣ commaPullback p b :=
  Adjunction.adjunctionOfEquivRight (fiberCommaHomEquiv p b)
    (fiberCommaHomEquiv_natural p b)

instance fiberToComma_initial : (fiberToComma p b).Initial :=
  Functor.initial_of_adjunction (fiberCommaAdjunction p b)

/-- Computing the right-Kan comma limit using the actual fiber. -/
instance fiberHasLimit {H : Type*} [Category H] (D : A ⥤ H)
    [HasLimit (StructuredArrow.proj b p ⋙ D)] :
    HasLimit (Fiber.fiberInclusion (p := p) (S := b) ⋙ D) := by
  change HasLimit (fiberToComma p b ⋙ (StructuredArrow.proj b p ⋙ D))
  infer_instance

/-- Computing the right-Kan comma limit using the actual fiber. -/
def fiberCommaLimitIso {H : Type*} [Category H] (D : A ⥤ H)
    [HasLimit (StructuredArrow.proj b p ⋙ D)] :
    limit (Fiber.fiberInclusion (p := p) (S := b) ⋙ D) ≅
      limit (StructuredArrow.proj b p ⋙ D) :=
  Functor.Initial.limitIso (fiberToComma p b) (StructuredArrow.proj b p ⋙ D)

end Sharpness
