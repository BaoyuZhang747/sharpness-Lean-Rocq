import Sharpness.TotalDualDegreeIso
import Sharpness.NativeCoproductPiComponents
import Sharpness.TotalSummandProjectionAt
import Sharpness.ZeroColumnTotalProjection

/-! The finite coproduct dual evaluation is exactly the already used
native total-summand projection. Thus the degreewise dual comparison
is fixed on every actual chain-total inclusion. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory
variable {R : Type u} [CommRing R]
    (K : HomologicalComplex₂ (ModuleCat.{u} R) (ComplexShape.down ℕ) (ComplexShape.down ℕ))
    (A : ModuleCat.{u} R)

set_option backward.isDefEq.respectTransparency false in
theorem dualTotalDegreeProjection_eq (n : ℕ) (z : NatTotalIndex n) :
    dualTotalDegreeProjection K A n z =
      totalSummandProjectionAt (dualNatBicomplex K A) z.val.1 z.val.2 n z.property := by
  apply HomologicalComplex₂.total.hom_ext
  intro i j h
  change i+j=n at h
  let M : NatTotalIndex n → ModuleCat.{u} R :=
    fun w => ModuleCat.of R ((K.X w.val.1).X w.val.2 ⟶ A)
  by_cases hi : i=z.val.1
  · subst i
    have hj : j=z.val.2 := by have := z.property; omega
    subst j
    exact (nativeCoproductPiIso_inclusion_self M z).trans
      (totalSummandProjectionAt_inclusion (dualNatBicomplex K A) z.val.1 z.val.2 n z.property).symm
  · have hz : (⟨(i,j),h⟩ : NatTotalIndex n) ≠ z := by
      intro he
      exact hi (congrArg (fun w : NatTotalIndex n => w.val.1) he)
    exact (nativeCoproductPiIso_inclusion_other M ⟨(i,j),h⟩ z hz).trans
      (totalSummandProjectionAt_other (dualNatBicomplex K A) z.val.1 z.val.2 n i j z.property h hi).symm

set_option backward.isDefEq.respectTransparency false in
theorem totalDualDegreeIso_inv_totalProjection (n : ℕ) (z : NatTotalIndex n)
    (f : (K.total (ComplexShape.down ℕ)).X n ⟶ A) :
    totalSummandProjectionAt (dualNatBicomplex K A) z.val.1 z.val.2 n z.property
        ((totalDualDegreeIso K A n).inv f) =
      K.ιTotal (ComplexShape.down ℕ) z.val.1 z.val.2 n z.property ≫ f :=
  (congrArg (fun a => a ((totalDualDegreeIso K A n).inv f)) (dualTotalDegreeProjection_eq K A n z)).symm.trans
    (totalDualDegreeIso_inv_projection K A n z f)

end Sharpness
