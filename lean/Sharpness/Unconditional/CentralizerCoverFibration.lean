import Sharpness.Unconditional.CentralizerCoverCocartesian
import Mathlib.CategoryTheory.FiberedCategory.Fibered

/-! The opposite of the centralizer projection is a genuine fibered category.
The opposite-category transport below records the actual universal properties. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

universe u₁ u₂ v₁ v₂ u
namespace Sharpness
open CategoryTheory Opposite

section OppositeTransport
variable {X : Type u₁} {Y : Type u₂} [Category.{v₁} X] [Category.{v₂} Y]
    (q : X ⥤ Yᵒᵖ)

theorem homLift_leftOp_of_homLift {R S : Yᵒᵖ} {a b : X}
    {f : R ⟶ S} {φ : a ⟶ b} (h : q.IsHomLift f φ) :
    q.leftOp.IsHomLift f.unop φ.op := by
  cases h
  exact IsHomLift.map _ _

theorem homLift_of_leftOp {R S : Y} {a b : Xᵒᵖ}
    {f : R ⟶ S} {φ : a ⟶ b} (h : q.leftOp.IsHomLift f φ) :
    q.IsHomLift f.op φ.unop := by
  cases h
  exact IsHomLift.map _ _

theorem stronglyCartesian_leftOp_of_stronglyCocartesian
    {R S : Yᵒᵖ} {a b : X} (f : R ⟶ S) (φ : a ⟶ b)
    [q.IsStronglyCocartesian f φ] : q.leftOp.IsStronglyCartesian f.unop φ.op := by
  letI : q.leftOp.IsHomLift f.unop φ.op :=
    homLift_leftOp_of_homLift q (inferInstance : q.IsHomLift f φ)
  refine ⟨?_⟩
  intro a' g ψ hψ
  have hψ' : q.IsHomLift (f ≫ g.op) ψ.unop := homLift_of_leftOp q hψ
  letI := hψ'
  obtain ⟨χ, ⟨hχ, hfac⟩, huniq⟩ :=
    Functor.IsStronglyCocartesian.universal_property' (p := q) (f := f) (φ := φ)
      g.op ψ.unop
  refine ⟨χ.op, ⟨homLift_leftOp_of_homLift q hχ, ?_⟩, ?_⟩
  · exact congrArg Quiver.Hom.op hfac
  · intro χ' hχ'
    apply Quiver.Hom.unop_inj
    apply huniq
    exact ⟨homLift_of_leftOp q hχ'.1, congrArg Quiver.Hom.unop hχ'.2⟩

end OppositeTransport

namespace FusionSystem
variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S) (p : ℕ)

theorem centralizerCover_stronglyCocartesian_over
    {R T : (F.ElementaryCategory p)ᵒᵖ} (f : R ⟶ T)
    {A B : F.CentralizedCentralizerCover p} (φ : A ⟶ B)
    [(F.centralizerCoverProjection p).IsHomLift f φ] [IsIso φ.hom.val] :
    (F.centralizerCoverProjection p).IsStronglyCocartesian f φ := by
  subst_hom_lift (F.centralizerCoverProjection p) f φ
  exact F.centralizerCover_stronglyCocartesian p φ

/-- The projection used for contravariant coefficients, with base `F^e`. -/
def centralizerCoverFibration : (F.CentralizedCentralizerCover p)ᵒᵖ ⥤ F.ElementaryCategory p :=
  (F.centralizerCoverProjection p).leftOp

/-- Ambient saturation provides the strongly Cartesian lifts needed for the
ordinary mathlib definition of a fibered category. -/
theorem centralizerCoverFibration_isFibered (sat : F.Saturated p) :
    (F.centralizerCoverFibration p).IsFibered := by
  apply Functor.IsFibered.of_exists_isStronglyCartesian
  intro A E θ
  obtain ⟨B, φ, hφ, hi⟩ := F.centralizerCover_exists_lift p sat A.unop E θ
  letI : IsIso φ.hom.val := hi
  letI : (F.centralizerCoverProjection p).IsHomLift θ.op φ := hφ
  letI : (F.centralizerCoverProjection p).IsStronglyCocartesian θ.op φ :=
    F.centralizerCover_stronglyCocartesian_over p θ.op φ
  exact ⟨op B, φ.op,
    stronglyCartesian_leftOp_of_stronglyCocartesian (F.centralizerCoverProjection p) θ.op φ⟩

end FusionSystem
end Sharpness
