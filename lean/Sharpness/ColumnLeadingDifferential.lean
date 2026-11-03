import Sharpness.ColumnLeadingQuotient
import Sharpness.FirstQuadrantFilteredCochains

/-! On the leading column quotient the total differential is exactly
(-1)^p times the actual vertical differential. The proof removes the
leading summand and uses preservation of the next filtration term. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory CategoryTheory.Limits
variable {R : Type u} [CommRing R]
    (K : HomologicalComplex₂ (ModuleCat.{u} R) (ComplexShape.up ℕ) (ComplexShape.up ℕ))

set_option backward.isDefEq.respectTransparency false in
theorem totalSummandProjection_d_inclusion (p q : ℕ) (x : (K.X p).X q) :
    totalSummandProjection K p (q+1)
      ((K.total (ComplexShape.up ℕ)).d (p+q) (p+(q+1))
        (K.ιTotal (ComplexShape.up ℕ) p q (p+q) rfl x)) =
      (((-1 : ℤˣ)^p : ℤ) • (K.X p).d q (q+1) x) := by
  have hd := congrArg (fun f => f x) (cochainNatBicomplexTotal_d K p q)
  change (K.total (ComplexShape.up ℕ)).d (p+q) (p+q+1)
      (K.ιTotal (ComplexShape.up ℕ) p q (p+q) rfl x) =
    K.ιTotal (ComplexShape.up ℕ) (p+1) q (p+q+1) (by change p+1+q=p+q+1; omega)
        ((K.d p (p+1)).f q x) +
      (((-1 : ℤˣ)^p : ℤ) •
        K.ιTotal (ComplexShape.up ℕ) p (q+1) (p+q+1) (by change p+(q+1)=p+q+1; omega)
          ((K.X p).d q (q+1) x)) at hd
  have hh := congrArg (fun z : (K.total (ComplexShape.up ℕ)).X (p+(q+1)) =>
    totalSummandProjection K p (q+1) z) hd
  have ha : totalSummandProjection K p (q+1)
      (K.ιTotal (ComplexShape.up ℕ) (p+1) q (p+q+1)
        (by change p+1+q=p+q+1; omega) ((K.d p (p+1)).f q x)) = 0 :=
    totalSummandProjection_apply_other K p (q+1) (p+1) q (by omega) (by omega) _
  have hb : totalSummandProjection K p (q+1)
      (K.ιTotal (ComplexShape.up ℕ) p (q+1) (p+q+1)
        (by change p+(q+1)=p+q+1; omega) ((K.X p).d q (q+1) x)) =
      (K.X p).d q (q+1) x := totalSummandProjection_apply_inclusion K p (q+1) _
  have hs := congrArg₂ (fun a b => a + (((-1 : ℤˣ)^p : ℤ) • b)) ha hb
  apply hh.trans
  simp only [map_add, map_zsmul]
  exact hs.trans (zero_add _)

theorem totalColumnLeadingMap_d (p q : ℕ) (x : totalColumnFiltration K p (p+q)) :
    totalSummandProjection K p (q+1)
      ((K.total (ComplexShape.up ℕ)).d (p+q) (p+(q+1)) x.val) =
      (((-1 : ℤˣ)^p : ℤ) • (K.X p).d q (q+1) (totalColumnLeadingMap K p q x)) := by
  let z := x.val - K.ιTotal (ComplexShape.up ℕ) p q (p+q) rfl
    (totalSummandProjection K p q x.val)
  have hz : z ∈ totalColumnFiltration K (p+1) (p+q) :=
    totalColumn_remove_leading K p q x.property
  have hdz : (K.total (ComplexShape.up ℕ)).d (p+q) (p+(q+1)) z ∈
      totalColumnFiltration K (p+1) (p+(q+1)) :=
    totalColumnFiltration_d K (p+1) (p+q) hz
  have hk := totalSummandProjection_kills_next K p (q+1) hdz
  change totalSummandProjection K p (q+1)
    ((K.total (ComplexShape.up ℕ)).d (p+q) (p+(q+1)) z) = 0 at hk
  dsimp only [z] at hk
  rw [map_sub, map_sub] at hk
  exact (sub_eq_zero.mp hk).trans
    (totalSummandProjection_d_inclusion K p q (totalSummandProjection K p q x.val))

end Sharpness
