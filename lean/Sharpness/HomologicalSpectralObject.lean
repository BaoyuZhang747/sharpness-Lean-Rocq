import Mathlib.CategoryTheory.Triangulated.SpectralObject
import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor
import Mathlib.Algebra.Homology.SpectralObject.Basic

/-! Applying a native homological functor to a triangulated spectral
object gives an actual abelian spectral object. All three exactness
conditions follow from distinguished triangles; they are not inputs.
This bridges the actual mapping-cone construction to native spectral
sequences for the filtered cochain complexes used in Corollary 4.1. -/
set_option autoImplicit false
noncomputable section
universe v u v' u' w t
namespace Sharpness
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
    [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    {A : Type u'} [Category.{v'} A] [Abelian A]
    {ι : Type t} [Category.{w} ι]
    (X : Triangulated.SpectralObject C ι) (F : C ⥤ A)
    [F.IsHomological] [F.ShiftSequence ℤ]

def homologicalSpectralObject : Abelian.SpectralObject A ι where
  H n := X.ω₁ ⋙ F.shift n
  δ' n₀ n₁ h :=
    { app D := F.homologySequenceδ (X.ω₂.obj D) n₀ n₁ h
      naturality {D E} f :=
        F.homologySequenceδ_naturality (X.ω₂.obj D) (X.ω₂.obj E) (X.ω₂.map f) n₀ n₁ h }
  exact₁' n₀ n₁ h D :=
    (F.homologySequence_exact₁ (X.ω₂.obj D) (X.ω₂_obj_distinguished D) n₀ n₁ h).exact_toComposableArrows
  exact₂' n D :=
    (F.homologySequence_exact₂ (X.ω₂.obj D) (X.ω₂_obj_distinguished D) n).exact_toComposableArrows
  exact₃' n₀ n₁ h D :=
    (F.homologySequence_exact₃ (X.ω₂.obj D) (X.ω₂_obj_distinguished D) n₀ n₁ h).exact_toComposableArrows

theorem homologicalSpectralObject_H (n : ℤ) :
    (homologicalSpectralObject X F).H n = X.ω₁ ⋙ F.shift n := rfl

theorem homologicalSpectralObject_delta {i j k : ι} (f : i ⟶ j) (g : j ⟶ k)
    (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    (homologicalSpectralObject X F).δ f g n₀ n₁ h =
      F.homologySequenceδ (X.triangle f g) n₀ n₁ h := rfl

end Sharpness
