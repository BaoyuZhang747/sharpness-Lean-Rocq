import Sharpness.CochainUnitTwistCycles

/-! The middle-identity unit-twist comparison preserves every actual
cycle representative, including degree zero. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory CategoryTheory.Limits
variable {R : Type u} [CommRing R] (V : CochainComplex (ModuleCat.{u} R) ℕ) (a : ℤˣ)

set_option backward.isDefEq.respectTransparency false in
theorem cochainUnitTwistCycleClass {M : ModuleCat.{u} R} (q : ℕ) (x : M ⟶ V.X q)
    (hx : x ≫ V.d q (q+1) = 0)
    (ha : x ≫ (cochainUnitTwist V a).d q (q+1) = 0) :
    ((cochainUnitTwist V a).liftCycles x (q+1) ((ComplexShape.up ℕ).next_eq' rfl) ha ≫
        (cochainUnitTwist V a).homologyπ q) ≫ (cochainUnitTwistCycleCohomologyIso V a q).hom =
      V.liftCycles x (q+1) ((ComplexShape.up ℕ).next_eq' rfl) hx ≫ V.homologyπ q := by
  let s := (cochainUnitTwistShortComplexIso V a q).hom
  have hs : ShortComplex.cyclesMap s ≫ V.iCycles q = (cochainUnitTwist V a).iCycles q := by
    have h : ShortComplex.cyclesMap s ≫ V.iCycles q =
        (cochainUnitTwist V a).iCycles q ≫ 𝟙 _ := ShortComplex.cyclesMap_i s
    exact h.trans (Category.comp_id _)
  have hc : (cochainUnitTwist V a).liftCycles x (q+1) ((ComplexShape.up ℕ).next_eq' rfl) ha ≫
      ShortComplex.cyclesMap s = V.liftCycles x (q+1) ((ComplexShape.up ℕ).next_eq' rfl) hx := by
    apply (cancel_mono (V.iCycles q)).mp
    simp only [Category.assoc, hs, HomologicalComplex.liftCycles_i]
  change (_ ≫ ((cochainUnitTwist V a).sc q).homologyπ) ≫ ShortComplex.homologyMap s = _
  rw [Category.assoc, ShortComplex.homologyπ_naturality]
  exact (Category.assoc _ _ _).symm.trans (congrArg (fun t => t ≫ V.homologyπ q) hc)

end Sharpness
