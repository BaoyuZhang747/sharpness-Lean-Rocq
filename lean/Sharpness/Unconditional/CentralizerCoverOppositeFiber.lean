import Sharpness.Unconditional.CentralizerCoverFibration
import Mathlib.CategoryTheory.FiberedCategory.Fiber

/-! Opposite fibers and inclusion compatibility, for the actual fibration
used in the centralizer argument. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

universe u₁ u₂ v₁ v₂
namespace Sharpness
open CategoryTheory Opposite

variable {X : Type u₁} {Y : Type u₂} [Category.{v₁} X] [Category.{v₂} Y]
    (q : X ⥤ Yᵒᵖ) (E : Y)

def oppositeFiberToLeftOpFiber : (q.Fiber (op E))ᵒᵖ ⥤ q.leftOp.Fiber E where
  obj A := ⟨op A.unop.val, congrArg Opposite.unop A.unop.property⟩
  map f := ⟨f.unop.val.op, homLift_leftOp_of_homLift q f.unop.property⟩
  map_id _ := Subtype.ext rfl
  map_comp _ _ := Subtype.ext rfl

def leftOpFiberObject (A : q.leftOp.Fiber E) : q.Fiber (op E) :=
  ⟨A.val.unop, congrArg Opposite.op A.property⟩

def leftOpFiberToOppositeFiber : q.leftOp.Fiber E ⥤ (q.Fiber (op E))ᵒᵖ where
  obj A := op (leftOpFiberObject q E A)
  map {A B} f := (show leftOpFiberObject q E B ⟶ leftOpFiberObject q E A from
    ⟨f.val.unop, homLift_of_leftOp q f.property⟩).op
  map_id _ := Quiver.Hom.unop_inj (Subtype.ext rfl)
  map_comp _ _ := Quiver.Hom.unop_inj (Subtype.ext rfl)

/-- Opposing the fiber of `q` agrees with taking the fiber of `q.leftOp`. -/
def oppositeFiberEquivalence : (q.Fiber (op E))ᵒᵖ ≌ q.leftOp.Fiber E where
  functor := oppositeFiberToLeftOpFiber q E
  inverse := leftOpFiberToOppositeFiber q E
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by intros; simp; rfl)
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by intros; simp; rfl)

/-- The equivalence respects the actual inclusions into the total categories. -/
def oppositeFiberEquivalenceInclusionIso :
    (oppositeFiberEquivalence q E).functor ⋙
        (Functor.Fiber.fiberInclusion : q.leftOp.Fiber E ⥤ Xᵒᵖ) ≅
      (Functor.Fiber.fiberInclusion : q.Fiber (op E) ⥤ X).op := Iso.refl _

end Sharpness
