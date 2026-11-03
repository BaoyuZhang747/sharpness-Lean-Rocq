import Sharpness.Unconditional.FiberComma
import Mathlib.CategoryTheory.Discrete.Basic

/-! The comma category computing left Kan extension from a fiber has one
terminal object for every arrow in the base. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
universe u v

namespace Sharpness
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open CategoryTheory.Functor.IsPreFibered

variable {A : Type u} {B : Type v} [Category A] [Category B]
    (p : A ⥤ B) (b : B) (a : A)

abbrev FiberLanComma := CostructuredArrow (Fiber.fiberInclusion (p := p) (S := b)) a

def fiberLanBaseArrow (X : FiberLanComma p b a) : b ⟶ p.obj a :=
  eqToHom X.left.property.symm ≫ p.map X.hom

instance fiberLanComma_isHomLift (X : FiberLanComma p b a) :
    p.IsHomLift (fiberLanBaseArrow p b a X) X.hom := by
  apply IsHomLift.of_fac p _ _ X.left.property rfl
  simp [fiberLanBaseArrow]

theorem fiberLanBaseArrow_eq {X Y : FiberLanComma p b a} (f : X ⟶ Y) :
    fiberLanBaseArrow p b a X = fiberLanBaseArrow p b a Y := by
  haveI := f.left.property
  have h := CostructuredArrow.w f
  change f.left.val ≫ Y.hom = X.hom at h
  rw [fiberLanBaseArrow, fiberLanBaseArrow, ← h, p.map_comp,
    IsHomLift.fac' p (𝟙 b) f.left.val]
  simp

def fiberLanBase : FiberLanComma p b a ⥤ Discrete (b ⟶ p.obj a) where
  obj X := ⟨fiberLanBaseArrow p b a X⟩
  map f := Discrete.eqToHom (fiberLanBaseArrow_eq p b a f)

variable [p.IsPreFibered]

def fiberLanTerminalObj (f : Discrete (b ⟶ p.obj a)) : FiberLanComma p b a :=
  ⟨⟨pullbackObj rfl f.as, pullbackObj_proj rfl f.as⟩, ⟨⟨⟩⟩,
    pullbackMap rfl f.as⟩

@[simp] theorem fiberLanTerminalObj_base (f : Discrete (b ⟶ p.obj a)) :
    fiberLanBaseArrow p b a (fiberLanTerminalObj p b a f) = f.as := by
  dsimp [fiberLanBaseArrow, fiberLanTerminalObj]
  rw [IsHomLift.fac' p f.as (pullbackMap rfl f.as)]
  simp

def fiberLanHomEquiv (X : FiberLanComma p b a) (f : Discrete (b ⟶ p.obj a)) :
    ((fiberLanBase p b a).obj X ⟶ f) ≃ (X ⟶ fiberLanTerminalObj p b a f) where
  toFun h := by
    have he := Discrete.eq_of_hom h
    change fiberLanBaseArrow p b a X = f.as at he
    haveI : p.IsHomLift f.as X.hom := he ▸ inferInstance
    exact CostructuredArrow.homMk
      ⟨IsCartesian.map p f.as (pullbackMap rfl f.as) X.hom, inferInstance⟩
      (IsCartesian.fac p f.as (pullbackMap rfl f.as) X.hom)
  invFun h := Discrete.eqToHom
    ((fiberLanBaseArrow_eq p b a h).trans (fiberLanTerminalObj_base p b a f))
  left_inv _ := Subsingleton.elim _ _
  right_inv h := by
    apply CostructuredArrow.hom_ext
    apply Subtype.ext
    haveI := h.left.property
    have he := (fiberLanBaseArrow_eq p b a h).trans (fiberLanTerminalObj_base p b a f)
    haveI : p.IsHomLift f.as X.hom := he ▸ inferInstance
    exact (IsCartesian.map_uniq p f.as (pullbackMap rfl f.as) X.hom h.left.val
      (CostructuredArrow.w h)).symm

theorem fiberLanHomEquiv_natural (X' X : FiberLanComma p b a)
    (f : Discrete (b ⟶ p.obj a)) (h : X' ⟶ X)
    (g : (fiberLanBase p b a).obj X ⟶ f) :
    fiberLanHomEquiv p b a X' f ((fiberLanBase p b a).map h ≫ g) =
      h ≫ fiberLanHomEquiv p b a X f g := by
  apply CostructuredArrow.hom_ext
  apply Subtype.ext
  haveI := h.left.property
  have he := Discrete.eq_of_hom g
  change fiberLanBaseArrow p b a X = f.as at he
  haveI : p.IsHomLift f.as X.hom := he ▸ inferInstance
  have he' := (fiberLanBaseArrow_eq p b a h).trans he
  haveI : p.IsHomLift f.as X'.hom := he' ▸ inferInstance
  change IsCartesian.map p f.as (pullbackMap rfl f.as) X'.hom =
    h.left.val ≫ IsCartesian.map p f.as (pullbackMap rfl f.as) X.hom
  apply (IsCartesian.map_uniq p f.as (pullbackMap rfl f.as) X'.hom _ ?_).symm
  rw [Category.assoc, IsCartesian.fac]
  exact CostructuredArrow.w h

/-- Choosing the cartesian lifts is a right adjoint, hence a final functor. -/
def fiberLanTerminals : Discrete (b ⟶ p.obj a) ⥤ FiberLanComma p b a :=
  Adjunction.rightAdjointOfEquiv (fiberLanHomEquiv p b a)
    (fiberLanHomEquiv_natural p b a)

def fiberLanBaseAdjunction : fiberLanBase p b a ⊣ fiberLanTerminals p b a :=
  Adjunction.adjunctionOfEquivRight (fiberLanHomEquiv p b a)
    (fiberLanHomEquiv_natural p b a)

instance fiberLanTerminals_final : (fiberLanTerminals p b a).Final :=
  Functor.final_of_adjunction (fiberLanBaseAdjunction p b a)

end Sharpness
