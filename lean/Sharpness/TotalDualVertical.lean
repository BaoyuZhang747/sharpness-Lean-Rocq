import Sharpness.TotalDualDirectionalMaps
import Sharpness.DualNatBicomplexComponents
import Sharpness.TotalIncomingVertical

/-! The degreewise inverse dual comparison commutes with the actual
vertical total differential, including row zero and its (-1)^p sign. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory CategoryTheory.Limits
variable {R : Type u} [CommRing R]
    (K : HomologicalComplex₂ (ModuleCat.{u} R) (ComplexShape.down ℕ) (ComplexShape.down ℕ))
    (A : ModuleCat.{u} R)

set_option backward.isDefEq.respectTransparency false in
theorem totalDualDegreeIso_inv_vertical (n : ℕ) :
    (totalDualDegreeIso K A n).inv ≫ (dualNatBicomplex K A).D₂ (ComplexShape.up ℕ) n (n+1) =
      totalDualVerticalMap K A n ≫ (totalDualDegreeIso K A (n+1)).inv := by
  apply dualTotalProjection_hom_ext K A (n+1)
  rintro ⟨⟨p,q⟩,hz⟩
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  cases q with
  | zero =>
    have hd := cochainTotal_vertical_zero_incoming (dualNatBicomplex K A) p n hz
    calc
      _ = 0 := congrArg (fun a => a ((totalDualDegreeIso K A n).inv f)) hd
      _ = K.ιTotal (ComplexShape.down ℕ) p 0 (n+1) hz ≫
          (K.D₂ (ComplexShape.down ℕ) (n+1) n ≫ f) :=
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun a => a ≫ f) (chainTotal_vertical_zero_outgoing K p n hz)).trans zero_comp)).symm
      _ = _ := (totalDualDegreeIso_inv_totalProjection K A (n+1) ⟨(p,0),hz⟩
        (K.D₂ (ComplexShape.down ℕ) (n+1) n ≫ f)).symm
  | succ q =>
    have h : p+q=n := by omega
    have hd := cochainTotal_vertical_incoming (dualNatBicomplex K A) p q n h
    have hp := totalDualDegreeIso_inv_totalProjection K A n ⟨(p,q),h⟩ f
    calc
      _ = (-1 : ℤˣ)^p • (((dualNatBicomplex K A).X p).d q (q+1)
          (totalSummandProjectionAt (dualNatBicomplex K A) p q n h ((totalDualDegreeIso K A n).inv f))) :=
        congrArg (fun a => a ((totalDualDegreeIso K A n).inv f)) hd
      _ = (-1 : ℤˣ)^p • ((K.X p).d (q+1) q ≫
          (K.ιTotal (ComplexShape.down ℕ) p q n h ≫ f)) :=
        congrArg (fun a => (-1 : ℤˣ)^p • ((K.X p).d (q+1) q ≫ a)) hp
      _ = (-1 : ℤˣ)^p • (((K.X p).d (q+1) q ≫ K.ιTotal (ComplexShape.down ℕ) p q n h) ≫ f) :=
        congrArg (fun a => (-1 : ℤˣ)^p • a) (Category.assoc _ _ _).symm
      _ = ((-1 : ℤˣ)^p • ((K.X p).d (q+1) q ≫ K.ιTotal (ComplexShape.down ℕ) p q n h)) ≫ f := by
        rw [Linear.units_smul_comp]
      _ = (K.ιTotal (ComplexShape.down ℕ) p (q+1) (n+1) hz ≫
          K.D₂ (ComplexShape.down ℕ) (n+1) n) ≫ f :=
        congrArg (fun a => a ≫ f) (chainTotal_vertical_outgoing K p q n h).symm
      _ = K.ιTotal (ComplexShape.down ℕ) p (q+1) (n+1) hz ≫
          (K.D₂ (ComplexShape.down ℕ) (n+1) n ≫ f) := Category.assoc _ _ _
      _ = _ := (totalDualDegreeIso_inv_totalProjection K A (n+1) ⟨(p,q+1),hz⟩
        (K.D₂ (ComplexShape.down ℕ) (n+1) n ≫ f)).symm

end Sharpness
