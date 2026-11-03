import Sharpness.Unconditional.ElementaryCochainEdgeSurjective

/-! Elementary first-quadrant cochain edge comparison. The proof uses only
finite diagonal correction, and the isomorphism's component is the actual
zero-column total projection. No spectral-sequence construction is used. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
universe u
namespace Sharpness.ElementaryCochainEdge
open CategoryTheory CategoryTheory.Limits HomologicalComplex
variable {R : Type u} [CommRing R]
    (K : HomologicalComplex₂ (ModuleCat.{u} R) (ComplexShape.up ℕ) (ComplexShape.up ℕ))

theorem edgeMap_bijective (hK : PositiveHorizontalExact K) (n : ℕ) :
    Function.Bijective (edgeMap K n) :=
  ⟨edgeMap_injective K hK n, edgeMap_surjective K hK n⟩

theorem edgeMap_isIso (hK : PositiveHorizontalExact K) (n : ℕ) : IsIso (edgeMap K n) :=
  edgeMap_isIso_of_bijective K n (edgeMap_bijective K hK n)

def edgeIso (hK : PositiveHorizontalExact K) (n : ℕ) :
    (K.total (ComplexShape.up ℕ)).homology n ≅ ModuleCat.of R (edgeKernel K n) :=
  edgeIsoOfBijective K n (edgeMap_bijective K hK n)

@[simp] theorem edgeIso_hom (hK : PositiveHorizontalExact K) (n : ℕ) :
    (edgeIso K hK n).hom = edgeMap K n := rfl

@[reassoc] theorem edgeIso_kernelSubtype (hK : PositiveHorizontalExact K) (n : ℕ) :
    (edgeIso K hK n).hom ≫ edgeKernelSubtype K n =
      homologyMap (zeroColumnTotalProjection K) n := rfl

def edgeKernelCyclesIso (n : ℕ) :
    ModuleCat.of R (edgeKernel K n) ≅ (verticalHomology K n).cycles 0 :=
  ((verticalHomology K n).sc' 0 0 1).moduleCatCyclesIso.symm ≪≫
    ((verticalHomology K n).cyclesIsoSc' 0 0 1 (by simp) (by simp)).symm

@[reassoc] theorem edgeKernelCyclesIso_iCycles (n : ℕ) :
    (edgeKernelCyclesIso K n).hom ≫ (verticalHomology K n).iCycles 0 =
      edgeKernelSubtype K n := by
  simp only [edgeKernelCyclesIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    cyclesIsoSc'_inv_iCycles, ShortComplex.moduleCatCyclesIso_inv_iCycles]
  rfl

def edgeHomologyZeroIso (hK : PositiveHorizontalExact K) (n : ℕ) :
    (K.total (ComplexShape.up ℕ)).homology n ≅ (verticalHomology K n).homology 0 :=
  edgeIso K hK n ≪≫ edgeKernelCyclesIso K n ≪≫ (verticalHomology K n).isoHomologyπ₀

/-- The all-degree comparison retains the actual map into zero-column
vertical cohomology, including n=0. -/
@[reassoc] theorem edgeHomologyZeroIso_component (hK : PositiveHorizontalExact K) (n : ℕ) :
    (edgeHomologyZeroIso K hK n).hom ≫ (verticalHomology K n).isoHomologyπ₀.inv ≫
      (verticalHomology K n).iCycles 0 =
      homologyMap (zeroColumnTotalProjection K) n := by
  simp only [edgeHomologyZeroIso, Iso.trans_hom, Category.assoc,
    Iso.hom_inv_id_assoc, edgeKernelCyclesIso_iCycles, edgeIso_kernelSubtype]

end Sharpness.ElementaryCochainEdge
