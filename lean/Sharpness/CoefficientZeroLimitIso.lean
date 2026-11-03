import Sharpness.CoefficientZeroLimitMaps

/-! The actual zeroth coefficient cohomology is canonically the native
inverse limit. The isomorphism is fixed by its value at every object,
independently of any bar-comparison reference input. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory CategoryTheory.Limits Opposite
variable {R C : Type u} [CommRing R] [Category.{u} C]
    (M : Cᵒᵖ ⥤ ModuleCat.{u} R)

set_option backward.isDefEq.respectTransparency false in
def coefficientZeroCyclesLimitIso : (coefficientCochains M).cycles 0 ≅ limit M where
  hom := coefficientZeroCyclesToLimit M
  inv := coefficientLimitToZeroCycles M
  hom_inv_id := by
    apply (cancel_mono ((coefficientCochains M).iCycles 0)).mp
    apply coefficientZero_hom_ext M
    intro P
    simp only [Category.assoc, coefficientLimitToZeroCycles_inclusion_assoc,
      coefficientLimitZeroCochain_projection, coefficientZeroCyclesToLimit_projection, Category.id_comp]
  inv_hom_id := by
    apply limit.hom_ext
    intro P
    simp only [Category.assoc, coefficientZeroCyclesToLimit_projection M P.unop,
      coefficientLimitToZeroCycles_inclusion_assoc, coefficientLimitZeroCochain_projection, Category.id_comp]

def coefficientZeroCohomologyLimitIso : (coefficientCochains M).homology 0 ≅ limit M :=
  (coefficientCochains M).isoHomologyπ₀.symm ≪≫ coefficientZeroCyclesLimitIso M

set_option backward.isDefEq.respectTransparency false in
theorem coefficientZeroCohomologyLimitIso_projection (P : C) :
    (coefficientCochains M).homologyπ 0 ≫ (coefficientZeroCohomologyLimitIso M).hom ≫ limit.π M (op P) =
      (coefficientCochains M).iCycles 0 ≫ coefficientZeroEvaluation M P := by
  change ((coefficientCochains M).isoHomologyπ₀.hom) ≫
    ((coefficientCochains M).isoHomologyπ₀.inv ≫ coefficientZeroCyclesToLimit M) ≫ limit.π M (op P) = _
  simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  exact coefficientZeroCyclesToLimit_projection M P

end Sharpness
