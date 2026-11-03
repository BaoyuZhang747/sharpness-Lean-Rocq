import Sharpness.ColumnFiltrationFunctor
import Sharpness.CochainSubmoduleHomology
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono

/-! Column filtration maps remain actual monomorphisms after extension
to integer cochain complexes. Both componentwise injectivity and the
zero components outside the natural-number embedding are proved here. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory CategoryTheory.Limits
variable {R : Type u} [CommRing R]
    (K : HomologicalComplex₂ (ModuleCat.{u} R) (ComplexShape.up ℕ) (ComplexShape.up ℕ))

theorem totalColumnFilteredMap_mono {k l : ℕ} (h : k ≤ l) :
    Mono (totalColumnFilteredMap K h) :=
  CochainSubmodules.map_mono _ (fun n => totalColumnFiltration_antitone K n h)

theorem totalColumnFilteredExtendedMap_mono {k l : ℕ} (h : k ≤ l) :
    Mono (HomologicalComplex.extendMap (totalColumnFilteredMap K h) ComplexShape.embeddingUpNat) := by
  letI := totalColumnFilteredMap_mono K h
  apply HomologicalComplex.mono_of_mono_f
  intro n
  by_cases hn : 0 ≤ n
  · obtain ⟨i, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    rw [HomologicalComplex.extendMap_f _ _ (show ComplexShape.embeddingUpNat.f i = (i : ℤ) from rfl)]
    infer_instance
  · have hz := HomologicalComplex.isZero_extend_X (totalColumnFilteredComplex K l)
      ComplexShape.embeddingUpNat n (by
        intro i hi
        change (i : ℤ) = n at hi
        omega)
    exact mono_of_source_iso_zero _ hz.isoZero

end Sharpness
