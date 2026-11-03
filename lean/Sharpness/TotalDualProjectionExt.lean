import Sharpness.TotalDualProjection

/-! The actual total-summand projections jointly detect morphisms
into the dual total module. This follows from the proved finite
coproduct-to-product isomorphism, not a joint-monicity assumption. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory
variable {R : Type u} [CommRing R]
    (K : HomologicalComplex₂ (ModuleCat.{u} R) (ComplexShape.down ℕ) (ComplexShape.down ℕ))
    (A : ModuleCat.{u} R)

set_option backward.isDefEq.respectTransparency false in
theorem dualTotalProjection_hom_ext (n : ℕ) {B : ModuleCat.{u} R}
    {f g : B ⟶ ((dualNatBicomplex K A).total (ComplexShape.up ℕ)).X n}
    (h : ∀ z : NatTotalIndex n,
      f ≫ totalSummandProjectionAt (dualNatBicomplex K A) z.val.1 z.val.2 n z.property =
        g ≫ totalSummandProjectionAt (dualNatBicomplex K A) z.val.1 z.val.2 n z.property) : f=g := by
  let M : NatTotalIndex n → ModuleCat.{u} R := fun z => ModuleCat.of R ((K.X z.val.1).X z.val.2 ⟶ A)
  apply (cancel_mono (nativeCoproductPiIso M).hom).mp
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  funext z
  have hz := dualTotalDegreeProjection_eq K A n z
  have hp := (congrArg (fun b => f ≫ b) hz).trans
    ((h z).trans (congrArg (fun b => g ≫ b) hz).symm)
  exact congrArg (fun b => b x) hp

end Sharpness
