import Sharpness.ColumnRelativePageImage
import Sharpness.FilteredCohomologyImages
import Sharpness.SpectralSequenceVanishing

/-! Full finite convergence for the constructed column spectral sequence,
with abutment the native cohomology of the integer-extended zeroth
filtered complex. The graded isomorphisms are proved from the actual
spectral-object image quotient and absolute/relative comparison. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory CategoryTheory.Limits
variable {R : Type u} [CommRing R]
    (K : HomologicalComplex₂ (ModuleCat.{u} R) (ComplexShape.up ℕ) (ComplexShape.up ℕ))

set_option backward.isDefEq.respectTransparency false in
def totalColumnStablePageImageIso (n p : ℕ) (hp : p ≤ n) :
    ((totalColumnE₂SpectralSequence K).page (n+2) (by omega)).X (p,n-p) ≅
      ModuleCat.of R (filteredCohomologyImage (totalColumnFiltrationIntFunctor K) n p ⧸
        (filteredCohomologyImage (totalColumnFiltrationIntFunctor K) n (p+1)).comap
          (filteredCohomologyImage (totalColumnFiltrationIntFunctor K) n p).subtype) := by
  let X := columnMappingConeSpectralObject K
  have ep : ((totalColumnE₂SpectralSequence K).page (n+2) (by omega)).X (p,n-p) ≅
      X.E (homOfLE (show OrderDual.toDual (n+p+2) ≤ OrderDual.toDual (p+1) from
          (show p+1 ≤ n+p+2 from by omega)))
        (homOfLE (show OrderDual.toDual (p+1) ≤ OrderDual.toDual p from Nat.le_succ p))
        (homOfLE (show OrderDual.toDual p ≤ OrderDual.toDual 0 from Nat.zero_le p))
        ((n : ℤ)-1) n ((n : ℤ)+1) :=
    X.spectralSequencePageXIso columnSpectralCore (n+2) (by omega) (p,n-p)
      (OrderDual.toDual (n+p+2)) (OrderDual.toDual (p+1))
      (OrderDual.toDual p) (OrderDual.toDual 0)
      (by change n+p+2 = ((p : ℤ)+(n+2 : ℕ)).toNat; omega) rfl rfl
      (by change 0 = ((p : ℤ)+1-(n+2 : ℕ)).toNat; omega)
      ((n : ℤ)-1) n ((n : ℤ)+1)
      (by change (n : ℤ) = (p : ℤ)+(n-p : ℕ); omega)
  exact ep ≪≫ columnRelativePageImageIso K (n+p+2) (p+1) p 0 (by omega)
      (Nat.le_succ p) (Nat.zero_le p) n (by omega) ≪≫
    filteredCohomologyImageQuotientIso (totalColumnFiltrationIntFunctor K) n p

def totalColumnIntegerConvergence : FiniteSpectralConvergence (totalColumnE₂SpectralSequence K)
    (fun n => ((totalColumnFiltrationIntFunctor K).obj (OrderDual.toDual 0)).homology (n : ℤ)) where
  filtration n k := filteredCohomologyImage (totalColumnFiltrationIntFunctor K) n k
  antitone n := filteredCohomologyImage_antitone _ n
  start n := filteredCohomologyImage_start _ n
  stop n := by
    letI : ((totalColumnFiltrationIntFunctor K).obj (OrderDual.toDual (n+1))).IsStrictlyGE
        ((n+1 : ℕ) : ℤ) := totalColumnFilteredExtended_isStrictlyGE K (n+1)
    exact filteredCohomologyImage_zero _ n (n+1)
      (((totalColumnFiltrationIntFunctor K).obj (OrderDual.toDual (n+1))).isZero_of_isGE
        ((n+1 : ℕ) : ℤ) n (by omega))
  graded n p hp := (totalColumnStablePageImageIso K n p hp).symm

end Sharpness
