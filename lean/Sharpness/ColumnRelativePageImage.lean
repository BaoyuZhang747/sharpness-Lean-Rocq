import Sharpness.ColumnAbsoluteRelative
import Sharpness.SpectralObjectImageQuotient
import Sharpness.ImageQuotientCongr

/-! The actual page object, with a sufficiently high left cutoff,
is the quotient of images of actual absolute filtered cohomology maps.
This applies the generic spectral-object calculation to the constructed
column model, eliminating all relative-cohomology comparison parameters. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
variable {R : Type u} [CommRing R]
    (K : HomologicalComplex₂ (ModuleCat.{u} R) (ComplexShape.up ℕ) (ComplexShape.up ℕ))

set_option backward.isDefEq.respectTransparency false in
def columnRelativePageImageIso (a b c d : ℕ) (hb : b ≤ a) (hc : c ≤ b) (hd : d ≤ c)
    (n : ℤ) (hn : n+1 < a) :
    (columnMappingConeSpectralObject K).E
      (homOfLE (show OrderDual.toDual a ≤ OrderDual.toDual b from hb))
      (homOfLE (show OrderDual.toDual b ≤ OrderDual.toDual c from hc))
      (homOfLE (show OrderDual.toDual c ≤ OrderDual.toDual d from hd)) (n-1) n (n+1) ≅
    ModuleCat.of R (ImageQuotient
      (HomologicalComplex.homologyMap ((totalColumnFiltrationIntFunctor K).map
        (homOfLE (show OrderDual.toDual b ≤ OrderDual.toDual c from hc))) n).hom
      (HomologicalComplex.homologyMap ((totalColumnFiltrationIntFunctor K).map
        (homOfLE (show OrderDual.toDual c ≤ OrderDual.toDual d from hd))) n).hom) := by
  let I := totalColumnFiltrationIntFunctor K
  let X := columnMappingConeSpectralObject K
  let f₁ := homOfLE (show OrderDual.toDual a ≤ OrderDual.toDual b from hb)
  let f₂ := homOfLE (show OrderDual.toDual b ≤ OrderDual.toDual c from hc)
  let f₃ := homOfLE (show OrderDual.toDual c ≤ OrderDual.toDual d from hd)
  let u := HomologicalComplex.homologyMap (I.map f₂) n
  let v := HomologicalComplex.homologyMap (I.map f₃) n
  let u' := spectralImageLeft X f₁ f₂ n
  let v' := spectralImageRight X f₁ f₂ f₃ n
  let eB := (columnAbsoluteRelativeIso K a b hb n hn).toLinearEquiv
  let eA := (columnAbsoluteRelativeIso K a c (hc.trans hb) n hn).toLinearEquiv
  let eH := (columnAbsoluteRelativeIso K a d (hd.trans (hc.trans hb)) n hn).toLinearEquiv
  have hu : ∀ x, u'.hom (eB x) = eA (u.hom x) := by
    intro x
    exact (congrArg (fun t => t x) (columnAbsoluteRelativeIso_naturality K a b c hb hc n hn)).symm
  have hv : ∀ x, v'.hom (eA x) = eH (v.hom x) := by
    intro x
    exact (congrArg (fun t => t x)
      (columnAbsoluteRelativeIso_naturality K a c d (hc.trans hb) hd n hn)).symm
  exact spectralObjectImageQuotientIso X f₁ f₂ f₃ n ≪≫
    (imageQuotientCongr v.hom v'.hom eA eH hv u.hom u'.hom eB hu).toModuleIso.symm

end Sharpness
