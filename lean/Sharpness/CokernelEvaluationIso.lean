import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-! Native cokernels of complexes commute with evaluation, including
the formula for the actual projection in each degree. -/
set_option autoImplicit false
noncomputable section
universe u v t
namespace Sharpness
open CategoryTheory CategoryTheory.Limits
variable {C : Type u} [Category.{v} C] [Abelian C]
    {ι : Type t} {c : ComplexShape ι} {K L : HomologicalComplex C c}
    (f : K ⟶ L) (n : ι)

def cokernelEvaluationIso : (cokernel f).X n ≅ cokernel (f.f n) :=
  PreservesCokernel.iso (HomologicalComplex.eval C c n) f

theorem cokernelEvaluationIso_projection :
    (cokernel.π f).f n ≫ (cokernelEvaluationIso f n).hom = cokernel.π (f.f n) :=
  PreservesCokernel.π_iso_hom (HomologicalComplex.eval C c n) f

theorem cokernel_term_zero (h : IsZero (L.X n)) : IsZero ((cokernel f).X n) :=
  IsZero.of_epi ((cokernel.π f).f n) h

end Sharpness
