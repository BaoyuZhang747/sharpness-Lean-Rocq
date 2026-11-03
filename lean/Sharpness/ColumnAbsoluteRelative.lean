import Sharpness.ColumnFilteredSpectralObject
import Sharpness.MappingConeCohomology

/-! In low total degrees a high column cutoff has zero cohomology.
Consequently, absolute cohomology of each filtered complex is naturally
isomorphic to the actual relative mapping-cone cohomology. This is the
comparison used to turn the stable page into the abutment filtration. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
variable {R : Type u} [CommRing R]
    (K : HomologicalComplex₂ (ModuleCat.{u} R) (ComplexShape.up ℕ) (ComplexShape.up ℕ))

def columnAbsoluteRelativeIso (a p : ℕ) (hp : p ≤ a) (n : ℤ) (hn : n+1 < a) :
    ((totalColumnFiltrationIntFunctor K).obj (OrderDual.toDual p)).homology n ≅
      columnRelative (columnMappingConeSpectralObject K) n a p hp := by
  let f := (totalColumnFiltrationIntFunctor K).map
    (homOfLE (show OrderDual.toDual a ≤ OrderDual.toDual p from hp))
  letI : ((totalColumnFiltrationIntFunctor K).obj (OrderDual.toDual a)).IsStrictlyGE (a : ℤ) :=
    totalColumnFilteredExtended_isStrictlyGE K a
  exact mappingConeInrCohomologyIso f n
      (((totalColumnFiltrationIntFunctor K).obj (OrderDual.toDual a)).isZero_of_isGE a n (by omega))
      (((totalColumnFiltrationIntFunctor K).obj (OrderDual.toDual a)).isZero_of_isGE a (n+1) hn) ≪≫
    (columnMappingConeRelativeIso K n a p hp).symm

theorem columnAbsoluteRelativeIso_hom (a p : ℕ) (hp : p ≤ a) (n : ℤ) (hn : n+1 < a) :
    (columnAbsoluteRelativeIso K a p hp n hn).hom =
      mappingConeAbsoluteMap ((totalColumnFiltrationIntFunctor K).map
        (homOfLE (show OrderDual.toDual a ≤ OrderDual.toDual p from hp))) n := rfl

set_option backward.isDefEq.respectTransparency false in
theorem columnAbsoluteRelativeIso_naturality (a p q : ℕ) (hp : p ≤ a) (hq : q ≤ p)
    (n : ℤ) (hn : n+1 < a) :
    HomologicalComplex.homologyMap ((totalColumnFiltrationIntFunctor K).map
        (homOfLE (show OrderDual.toDual p ≤ OrderDual.toDual q from hq))) n ≫
      (columnAbsoluteRelativeIso K a q (hq.trans hp) n hn).hom =
    (columnAbsoluteRelativeIso K a p hp n hn).hom ≫
      ((columnMappingConeSpectralObject K).H n).map
        (twoδ₂Toδ₁ (homOfLE (show OrderDual.toDual a ≤ OrderDual.toDual p from hp))
          (homOfLE (show OrderDual.toDual p ≤ OrderDual.toDual q from hq))
          (homOfLE (show OrderDual.toDual a ≤ OrderDual.toDual q from hq.trans hp)) rfl) := by
  let I := totalColumnFiltrationIntFunctor K
  let f := homOfLE (show OrderDual.toDual a ≤ OrderDual.toDual p from hp)
  let g := homOfLE (show OrderDual.toDual p ≤ OrderDual.toDual q from hq)
  exact mappingConeAbsoluteMap_naturality (I.map f) n (I.map (f ≫ g))
    (I.map (𝟙 (OrderDual.toDual a))) (I.map g) (by rw [← I.map_comp, ← I.map_comp]; rfl)

end Sharpness
