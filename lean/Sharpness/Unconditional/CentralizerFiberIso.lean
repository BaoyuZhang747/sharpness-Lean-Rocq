import Sharpness.Unconditional.CentralizerCoverGeometry
import Sharpness.Unconditional.CentralizerSaturation
import Mathlib.CategoryTheory.IsoCat

/-! Strict category isomorphisms for the centralizer-cover fibers.
The existing concrete functors are bijective on objects, not merely
essentially surjective, and retain their literal ambient compatibility. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

universe u u₁ u₂ v₁ v₂ w
namespace Sharpness
open CategoryTheory Opposite

variable {X : Type u₁} {Y : Type u₂} [Category.{v₁} X] [Category.{v₂} Y]
    (q : X ⥤ Yᵒᵖ) (E : Y)

instance oppositeFiberToLeftOpFiber_isIso :
    (oppositeFiberToLeftOpFiber q E).IsIso where
  faithful := (oppositeFiberEquivalence q E).faithful_functor
  full := (oppositeFiberEquivalence q E).full_functor
  bijective_obj := by
    constructor
    · intro A B h
      apply Opposite.unop_injective
      apply Subtype.ext
      exact congrArg (fun A : q.leftOp.Fiber E => A.val.unop) h
    · intro A
      exact ⟨(leftOpFiberToOppositeFiber q E).obj A, rfl⟩

/-- The opposite of the strict fiber is strictly isomorphic to the opposite
functor's fiber. Its forward functor is the original concrete one. -/
def oppositeFiberIsoCat : IsoCat (q.Fiber (op E))ᵒᵖ (q.leftOp.Fiber E) :=
  (oppositeFiberToLeftOpFiber q E).asIsomorphism

theorem oppositeFiberIsoCat_inclusion :
    (oppositeFiberIsoCat q E).functor ⋙
        (Functor.Fiber.fiberInclusion : q.leftOp.Fiber E ⥤ Xᵒᵖ) =
      (Functor.Fiber.fiberInclusion : q.Fiber (op E) ⥤ X).op := rfl

namespace FusionSystem
variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)
    (p : ℕ) [Fact p.Prime] (hS : IsPGroup p S) (sat : F.Saturated p)
    (E : F.ElementaryCategory p) (C : F.AKOCentralizerInput p hS sat E)

theorem localCentricToCoverFiber_obj_injective :
    Function.Injective (F.localCentricToCoverFiber p hS sat E C).obj := by
  rintro ⟨⟨⟨P⟩⟩, hP⟩ ⟨⟨⟨Q⟩⟩, hQ⟩ h
  have ha : ambientSubgroup (F.centralizerGroup p E) P =
      ambientSubgroup (F.centralizerGroup p E) Q :=
    congrArg (fun A : Functor.Fiber (F.centralizerCoverProjection p) (op E) =>
      A.val.obj.centric.obj.as.subgroup) h
  have hPQ : P = Q := Subgroup.map_injective
    (F.centralizerGroup p E).subtype_injective ha
  cases hPQ
  rfl

instance localCentricToCoverFiber_isIso :
    (F.localCentricToCoverFiber p hS sat E C).IsIso where
  bijective_obj := ⟨F.localCentricToCoverFiber_obj_injective p hS sat E C,
    F.localCentricToCoverFiber_obj_surjective p hS sat E C⟩

/-- The actual centralizer centric orbit category and the actual strict
cover fiber are isomorphic categories. -/
def centralizerCoverFiberIsoCat : IsoCat C.system.CentricOrbit
    (Functor.Fiber (F.centralizerCoverProjection p) (op E)) :=
  (F.localCentricToCoverFiber p hS sat E C).asIsomorphism

theorem centralizerCoverFiberIsoCat_forget :
    (F.centralizerCoverFiberIsoCat p hS sat E C).functor ⋙
        Functor.Fiber.fiberInclusion ⋙ F.centralizedCoverToCentric p =
      F.subsystemCentricFunctor (F.centralizerGroup p E) C.system C.embedding
        (F.yalcinCentralizerCentricInput p hS sat E C).centric := rfl

instance centralizerCoverFibrationFiberFunctor_isIso :
    (F.centralizerCoverFibrationFiberEquivalence p hS sat E C).functor.IsIso where
  faithful := (F.centralizerCoverFibrationFiberEquivalence p hS sat E C).faithful_functor
  full := (F.centralizerCoverFibrationFiberEquivalence p hS sat E C).full_functor
  bijective_obj := by
    change Function.Bijective
      ((oppositeFiberToLeftOpFiber (F.centralizerCoverProjection p) E).obj ∘
        (F.localCentricToCoverFiber p hS sat E C).op.obj)
    apply Function.Bijective.comp (Functor.bijective_obj _)
    constructor
    · intro P Q h
      apply Opposite.unop_injective
      exact F.localCentricToCoverFiber_obj_injective p hS sat E C
        (congrArg Opposite.unop h)
    · intro A
      obtain ⟨P, hP⟩ := F.localCentricToCoverFiber_obj_surjective p hS sat E C A.unop
      exact ⟨op P, congrArg Opposite.op hP⟩

/-- Strict identification of the fiber of the fibration used in detection. -/
def centralizerCoverFibrationFiberIsoCat : IsoCat C.system.CentricOrbitᵒᵖ
    (Functor.Fiber (F.centralizerCoverFibration p) E) :=
  (F.centralizerCoverFibrationFiberEquivalence p hS sat E C).functor.asIsomorphism

theorem centralizerCoverFibrationFiberIsoCat_inclusion :
    (F.centralizerCoverFibrationFiberIsoCat p hS sat E C).functor ⋙
        Functor.Fiber.fiberInclusion ⋙ (F.centralizedCoverToCentric p).op =
      (F.subsystemCentricFunctor (F.centralizerGroup p E) C.system C.embedding
        (F.yalcinCentralizerCentricInput p hS sat E C).centric).op := rfl

theorem centralizerCoverFibrationFiberIsoCat_coefficient
    {V : Type w} [Category V] (D : F.CentricOrbitᵒᵖ ⥤ V) :
    (F.centralizerCoverFibrationFiberIsoCat p hS sat E C).functor ⋙
        Functor.Fiber.fiberInclusion ⋙ ((F.centralizedCoverToCentric p).op ⋙ D) =
      (F.subsystemCentricFunctor (F.centralizerGroup p E) C.system C.embedding
        (F.yalcinCentralizerCentricInput p hS sat E C).centric).op ⋙ D := rfl

/-- Ordinary-hypothesis version, using the constructed centralizer system. -/
def centralizerSystemCoverFiberIsoCat : IsoCat (F.centralizerSystem p E).CentricOrbit
    (Functor.Fiber (F.centralizerCoverProjection p) (op E)) :=
  F.centralizerCoverFiberIsoCat p hS sat E (F.akoCentralizerInput p hS sat E)

/-- Ordinary-hypothesis strict opposite-fiber identification. -/
def centralizerSystemFibrationFiberIsoCat :
    IsoCat (F.centralizerSystem p E).CentricOrbitᵒᵖ
      (Functor.Fiber (F.centralizerCoverFibration p) E) :=
  F.centralizerCoverFibrationFiberIsoCat p hS sat E (F.akoCentralizerInput p hS sat E)

end FusionSystem
end Sharpness
