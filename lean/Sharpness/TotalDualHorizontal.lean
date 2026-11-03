import Sharpness.TotalDualDirectionalMaps
import Sharpness.DualNatBicomplexComponents
import Sharpness.TotalIncomingHorizontal

/-! The degreewise inverse dual comparison commutes with the actual
horizontal total differential, including column zero. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory CategoryTheory.Limits
variable {R : Type u} [CommRing R]
    (K : HomologicalComplex₂ (ModuleCat.{u} R) (ComplexShape.down ℕ) (ComplexShape.down ℕ))
    (A : ModuleCat.{u} R)

set_option backward.isDefEq.respectTransparency false in
theorem totalDualDegreeIso_inv_horizontal (n : ℕ) :
    (totalDualDegreeIso K A n).inv ≫ (dualNatBicomplex K A).D₁ (ComplexShape.up ℕ) n (n+1) =
      totalDualHorizontalMap K A n ≫ (totalDualDegreeIso K A (n+1)).inv := by
  apply dualTotalProjection_hom_ext K A (n+1)
  rintro ⟨⟨p,q⟩,hz⟩
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  cases p with
  | zero =>
    have hd := cochainTotal_horizontal_zero_incoming (dualNatBicomplex K A) q n hz
    calc
      _ = 0 := congrArg (fun a => a ((totalDualDegreeIso K A n).inv f)) hd
      _ = K.ιTotal (ComplexShape.down ℕ) 0 q (n+1) hz ≫
          (K.D₁ (ComplexShape.down ℕ) (n+1) n ≫ f) :=
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun a => a ≫ f) (chainTotal_horizontal_zero_outgoing K q n hz)).trans zero_comp)).symm
      _ = _ := (totalDualDegreeIso_inv_totalProjection K A (n+1) ⟨(0,q),hz⟩
        (K.D₁ (ComplexShape.down ℕ) (n+1) n ≫ f)).symm
  | succ p =>
    have h : p+q=n := by omega
    have hd := cochainTotal_horizontal_incoming (dualNatBicomplex K A) p q n h
    have hp := totalDualDegreeIso_inv_totalProjection K A n ⟨(p,q),h⟩ f
    calc
      _ = ((dualNatBicomplex K A).d p (p+1)).f q
          (totalSummandProjectionAt (dualNatBicomplex K A) p q n h ((totalDualDegreeIso K A n).inv f)) :=
        congrArg (fun a => a ((totalDualDegreeIso K A n).inv f)) hd
      _ = (K.d (p+1) p).f q ≫
          totalSummandProjectionAt (dualNatBicomplex K A) p q n h ((totalDualDegreeIso K A n).inv f) :=
        dualNatBicomplex_horizontal_apply K A p q _
      _ = (K.d (p+1) p).f q ≫ (K.ιTotal (ComplexShape.down ℕ) p q n h ≫ f) :=
        congrArg (fun a => (K.d (p+1) p).f q ≫ a) hp
      _ = ((K.d (p+1) p).f q ≫ K.ιTotal (ComplexShape.down ℕ) p q n h) ≫ f :=
        (Category.assoc _ _ _).symm
      _ = (K.ιTotal (ComplexShape.down ℕ) (p+1) q (n+1) hz ≫
          K.D₁ (ComplexShape.down ℕ) (n+1) n) ≫ f :=
        congrArg (fun a => a ≫ f) (chainTotal_horizontal_outgoing K p q n h).symm
      _ = K.ιTotal (ComplexShape.down ℕ) (p+1) q (n+1) hz ≫
          (K.D₁ (ComplexShape.down ℕ) (n+1) n ≫ f) := Category.assoc _ _ _
      _ = _ := (totalDualDegreeIso_inv_totalProjection K A (n+1) ⟨(p+1,q),hz⟩
        (K.D₁ (ComplexShape.down ℕ) (n+1) n ≫ f)).symm

end Sharpness
