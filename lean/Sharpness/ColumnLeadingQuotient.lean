import Sharpness.TotalSummandProjection
import Sharpness.KernelQuotientIso

/-! In total degree p+q, the actual quotient of column filtration p
by column filtration p+1 is the actual (p,q) module. The map is the
literal total-summand projection, with its kernel and surjectivity
proved from the generating summands of the filtration. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory CategoryTheory.Limits
variable {R : Type u} [CommRing R]
    (K : HomologicalComplex₂ (ModuleCat.{u} R) (ComplexShape.up ℕ) (ComplexShape.up ℕ))

def totalColumnLeadingMap (p q : ℕ) : totalColumnFiltration K p (p+q) →ₗ[R] (K.X p).X q :=
  (totalSummandProjection K p q).hom.comp (totalColumnFiltration K p (p+q)).subtype

theorem totalColumnLeadingMap_surjective (p q : ℕ) :
    Function.Surjective (totalColumnLeadingMap K p q) := by
  intro x
  refine ⟨⟨K.ιTotal (ComplexShape.up ℕ) p q (p+q) rfl x,
    totalColumnFiltration_summand_mem K p p q (p+q) rfl le_rfl x⟩, ?_⟩
  exact totalSummandProjection_apply_inclusion K p q x

theorem totalSummandProjection_kills_next (p q : ℕ) :
    totalColumnFiltration K (p+1) (p+q) ≤ (totalSummandProjection K p q).hom.ker := by
  refine iSup_le fun i => iSup_le fun j => iSup_le fun h => iSup_le fun hi => ?_
  rintro y ⟨x, rfl⟩
  exact totalSummandProjection_apply_other K p q i j h (by omega) x

theorem totalColumn_remove_leading (p q : ℕ) :
    totalColumnFiltration K p (p+q) ≤
      (totalColumnFiltration K (p+1) (p+q)).comap
        (LinearMap.id - (K.ιTotal (ComplexShape.up ℕ) p q (p+q) rfl).hom.comp
          (totalSummandProjection K p q).hom) := by
  refine iSup_le fun i => iSup_le fun j => iSup_le fun h => iSup_le fun hi => ?_
  rintro y ⟨x, rfl⟩
  change K.ιTotal (ComplexShape.up ℕ) i j (p+q) h x -
    K.ιTotal (ComplexShape.up ℕ) p q (p+q) rfl
      (totalSummandProjection K p q (K.ιTotal (ComplexShape.up ℕ) i j (p+q) h x)) ∈
        totalColumnFiltration K (p+1) (p+q)
  by_cases hip : i = p
  · subst i
    have hj : j = q := by omega
    subst j
    rw [totalSummandProjection_apply_inclusion, sub_self]
    exact Submodule.zero_mem _
  · rw [totalSummandProjection_apply_other K p q i j h hip x, map_zero, sub_zero]
    exact totalColumnFiltration_summand_mem K (p+1) i j (p+q) h (by omega) x

theorem totalColumnLeadingMap_ker (p q : ℕ) :
    (totalColumnLeadingMap K p q).ker =
      (totalColumnFiltration K (p+1) (p+q)).comap
        (totalColumnFiltration K p (p+q)).subtype := by
  ext x
  constructor
  · intro hx
    have ht := totalColumn_remove_leading K p q x.property
    change totalSummandProjection K p q x.val = 0 at hx
    change x.val ∈ totalColumnFiltration K (p+1) (p+q)
    change x.val - K.ιTotal (ComplexShape.up ℕ) p q (p+q) rfl
      (totalSummandProjection K p q x.val) ∈ totalColumnFiltration K (p+1) (p+q) at ht
    simpa only [hx, map_zero, sub_zero] using ht
  · intro hx
    exact totalSummandProjection_kills_next K p q hx

def totalColumnLeadingQuotientIso (p q : ℕ) :
    ModuleCat.of R (totalColumnFiltration K p (p+q) ⧸
      (totalColumnFiltration K (p+1) (p+q)).comap
        (totalColumnFiltration K p (p+q)).subtype) ≅ (K.X p).X q :=
  quotientIsoOfKer (totalColumnLeadingMap K p q) _ (totalColumnLeadingMap_ker K p q)
    (totalColumnLeadingMap_surjective K p q)

theorem totalColumnLeadingQuotientIso_mk (p q : ℕ)
    (x : totalColumnFiltration K p (p+q)) :
    (totalColumnLeadingQuotientIso K p q).hom (Submodule.Quotient.mk x) =
      totalColumnLeadingMap K p q x := by
  exact quotientIsoOfKer_mk _ _ _ _ x

end Sharpness
