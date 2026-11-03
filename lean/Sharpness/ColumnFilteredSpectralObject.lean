import Sharpness.HomologicalSpectralObject
import Sharpness.ColumnFiltrationFunctor
import Sharpness.ColumnFiltrationSupport
import Mathlib.Algebra.Homology.HomotopyCategory.SpectralObject
import Mathlib.Algebra.Homology.HomotopyCategory.HomologicalFunctor
import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence
import Mathlib.Algebra.Homology.HomotopyCategory.Plus
import Sharpness.ColumnSpectralSequence

/-! The actual filtered total complex determines a native spectral object
and a first-quadrant spectral sequence. Its support is proved from the
actual filtration terms. No pages, differentials, cohomological support,
or spectral-sequence existence are accepted as reference inputs. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
variable {R : Type u} [CommRing R]
    (K : HomologicalComplex₂ (ModuleCat.{u} R) (ComplexShape.up ℕ) (ComplexShape.up ℕ))

def columnMappingConeTriangulatedSpectralObject :
    Triangulated.SpectralObject (HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ)) ℕᵒᵈ :=
  (HomotopyCategory.spectralObjectMappingCone (ModuleCat.{u} R)).precomp
    (totalColumnFiltrationIntFunctor K)

def columnMappingConeSpectralObject : Abelian.SpectralObject (ModuleCat.{u} R) ℕᵒᵈ :=
  homologicalSpectralObject (columnMappingConeTriangulatedSpectralObject K)
    (HomotopyCategory.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) 0)

def columnMappingConeRelativeIso (n : ℤ) (a b : ℕ) (h : b ≤ a) :
    columnRelative (columnMappingConeSpectralObject K) n a b h ≅
      (CochainComplex.mappingCone ((totalColumnFiltrationIntFunctor K).map
        (homOfLE (show OrderDual.toDual a ≤ OrderDual.toDual b from h)))).homology n :=
  (HomotopyCategory.homologyFunctorFactors (ModuleCat.{u} R) (ComplexShape.up ℤ) n).app _

instance columnMappingConeSpectralObject_support :
    ColumnSpectralSupport (columnMappingConeSpectralObject K) where
  zero_below a b h n hab hn := by
    let f := (totalColumnFiltrationIntFunctor K).map
      (homOfLE (show OrderDual.toDual a ≤ OrderDual.toDual b from h))
    letI : ((totalColumnFiltrationIntFunctor K).obj (OrderDual.toDual a)).IsStrictlyGE (a : ℤ) :=
      totalColumnFilteredExtended_isStrictlyGE K a
    letI : ((totalColumnFiltrationIntFunctor K).obj (OrderDual.toDual b)).IsStrictlyGE (b : ℤ) :=
      totalColumnFilteredExtended_isStrictlyGE K b
    letI : (CochainComplex.mappingCone f).IsStrictlyGE (b : ℤ) :=
      CochainComplex.isStrictlyGE_mappingCone f a b b (by omega) le_rfl
    exact IsZero.of_iso ((CochainComplex.mappingCone f).isZero_of_isGE b n hn)
      (columnMappingConeRelativeIso K n a b h)

def totalColumnSpectralSequence : CohomologicalSpectralSequenceNat (ModuleCat.{u} R) 1 :=
  columnSpectralSequence (columnMappingConeSpectralObject K)

def totalColumnE₂SpectralSequence : E₂CohomologicalSpectralSequenceNat (ModuleCat.{u} R) :=
  columnE₂SpectralSequence (columnMappingConeSpectralObject K)

def totalColumnFirstPageIso (p q : ℕ) :
    ((totalColumnSpectralSequence K).page 1).X (p,q) ≅
      (CochainComplex.mappingCone ((totalColumnFiltrationIntFunctor K).map
        (homOfLE (show OrderDual.toDual (p+1) ≤ OrderDual.toDual p from Nat.le_succ p)))).homology
          (p+q) :=
  columnSpectralSequenceFirstPageIso (columnMappingConeSpectralObject K) p q ≪≫
    columnMappingConeRelativeIso K (p+q) (p+1) p (Nat.le_succ p)

def totalColumnSecondPageIso (p q : ℕ) :
    ((totalColumnSpectralSequence K).page 1).homology (p,q) ≅
      ((totalColumnE₂SpectralSequence K).page 2).X (p,q) :=
  (totalColumnSpectralSequence K).iso 1 2 (p,q)

end Sharpness
