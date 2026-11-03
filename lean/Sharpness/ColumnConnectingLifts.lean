import Sharpness.ColumnCycleLifts
import Sharpness.ColumnFilteredMonomorphisms

/-! The two actual lifts used to compute the filtered connecting map:
a vertical cycle in F^p and its horizontal differential in F^(p+1).
Their defining differential equality holds in the filtered complex. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory CategoryTheory.Limits
variable {R : Type u} [CommRing R]
    (K : HomologicalComplex₂ (ModuleCat.{u} R) (ComplexShape.up ℕ) (ComplexShape.up ℕ))

def totalColumnSummandLiftAt (p q n : ℕ) (h : p+q=n) :
    (K.X p).X q ⟶ (totalColumnFilteredComplex K p).X n :=
  (totalColumnSubmodules K p).degreeLift n
    (K.ιTotal (ComplexShape.up ℕ) p q n h)
    (totalColumnFiltration_summand_mem K p p q n h (le_refl p))

theorem totalColumnSummandLiftAt_inclusion (p q n : ℕ) (h : p+q=n) :
    totalColumnSummandLiftAt K p q n h ≫ (totalColumnFilteredInclusion K p).f n =
      K.ιTotal (ComplexShape.up ℕ) p q n h :=
  CochainSubmodules.degreeLift_inclusion _ _ _ _

theorem totalColumnFilteredMap_inclusion_component {k l : ℕ} (h : k ≤ l) (n : ℕ) :
    (totalColumnFilteredMap K h).f n ≫ (totalColumnFilteredInclusion K k).f n =
      (totalColumnFilteredInclusion K l).f n :=
  HomologicalComplex.congr_hom (CochainSubmodules.map_inclusion
    (V := totalColumnSubmodules K l) (W := totalColumnSubmodules K k)
      (fun n => totalColumnFiltration_antitone K n h)) n

set_option backward.isDefEq.respectTransparency false in
theorem totalColumnCycle_filtered_d (p q : ℕ) :
    ((K.X p).iCycles q ≫ (K.d p (p+1)).f q ≫
        totalColumnSummandLiftAt K (p+1) q (p+q+1) (by omega)) ≫
      (totalColumnFilteredMap K (Nat.le_succ p)).f (p+q+1) =
    ((K.X p).iCycles q ≫ totalColumnSummandLift K p q) ≫
      (totalColumnFilteredComplex K p).d (p+q) (p+q+1) := by
  letI : Mono ((totalColumnFilteredInclusion K p).f (p+q+1)) :=
    (totalColumnSubmodules K p).inclusion_component_mono (p+q+1)
  apply (cancel_mono ((totalColumnFilteredInclusion K p).f (p+q+1))).mp
  calc
    _ = (K.X p).iCycles q ≫ (K.d p (p+1)).f q ≫
        K.ιTotal (ComplexShape.up ℕ) (p+1) q (p+q+1)
          (by change p+1+q=p+q+1; omega) := by
      simp only [Category.assoc, totalColumnFilteredMap_inclusion_component,
        totalColumnSummandLiftAt_inclusion]
    _ = (K.X p).iCycles q ≫ K.ιTotal (ComplexShape.up ℕ) p q (p+q) rfl ≫
        (K.total (ComplexShape.up ℕ)).d (p+q) (p+q+1) := (totalColumnCycle_d K p q).symm
    _ = _ := by
      simp only [Category.assoc]
      rw [← (totalColumnFilteredInclusion K p).comm]
      simp only [totalColumnSummandLift_inclusion_assoc]

end Sharpness
