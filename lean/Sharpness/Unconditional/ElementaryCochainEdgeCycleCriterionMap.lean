import Sharpness.Unconditional.ElementaryCochainEdgeLeading

/-! The actual cohomological edge map into the kernel of the horizontal
differential. This constructs the map; bijectivity is a separate theorem. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
universe u
namespace Sharpness.ElementaryCochainEdge
open CategoryTheory CategoryTheory.Limits HomologicalComplex

variable {R : Type u} [CommRing R]
    (K : HomologicalComplex₂ (ModuleCat.{u} R) (ComplexShape.up ℕ) (ComplexShape.up ℕ))

def edgeKernel (n : ℕ) : Submodule R ((K.X 0).homology n) :=
  LinearMap.ker (homologyMap (K.d 0 1) n).hom

theorem zeroColumnHomologyMap_mem_edgeKernel (n : ℕ)
    (z : (K.total (ComplexShape.up ℕ)).homology n) :
    homologyMap (zeroColumnTotalProjection K) n z ∈ edgeKernel K n := by
  obtain ⟨x, hx, rfl⟩ := cycleClass_surjective (K.total (ComplexShape.up ℕ)) n z
  change homologyMap (K.d 0 1) n
    (homologyMap (zeroColumnTotalProjection K) n
      (cycleClass (K.total (ComplexShape.up ℕ)) n x hx)) = 0
  rw [cycleClass_map]
  exact leading_horizontal_cycle K 0 n n (by omega) x hx (by
    intro p q hpq hp
    omega)

def edgeMap (n : ℕ) : (K.total (ComplexShape.up ℕ)).homology n ⟶
    ModuleCat.of R (edgeKernel K n) :=
  ModuleCat.ofHom ((homologyMap (zeroColumnTotalProjection K) n).hom.codRestrict
    (edgeKernel K n) (zeroColumnHomologyMap_mem_edgeKernel K n))

def edgeKernelSubtype (n : ℕ) : ModuleCat.of R (edgeKernel K n) ⟶ (K.X 0).homology n :=
  ModuleCat.ofHom (edgeKernel K n).subtype

@[reassoc] theorem edgeMap_kernelSubtype (n : ℕ) :
    edgeMap K n ≫ edgeKernelSubtype K n = homologyMap (zeroColumnTotalProjection K) n := rfl

@[simp] theorem edgeMap_apply_val (n : ℕ)
    (z : (K.total (ComplexShape.up ℕ)).homology n) :
    (edgeMap K n z).val = homologyMap (zeroColumnTotalProjection K) n z := rfl

theorem edgeMap_cycleClass_val (n : ℕ)
    (x : (K.total (ComplexShape.up ℕ)).X n)
    (hx : Cycle (K.total (ComplexShape.up ℕ)) n x) :
    (edgeMap K n (cycleClass (K.total (ComplexShape.up ℕ)) n x hx)).val =
      cycleClass (K.X 0) n (totalSummandProjectionAt K 0 n n (by omega) x)
        (leading_cycle K 0 n n (by omega) x hx (by intro p q hpq hp; omega)) :=
  cycleClass_map (zeroColumnTotalProjection K) n x hx

theorem edgeMap_cycleClass (n : ℕ)
    (x : (K.total (ComplexShape.up ℕ)).X n)
    (hx : Cycle (K.total (ComplexShape.up ℕ)) n x) :
    edgeMap K n (cycleClass (K.total (ComplexShape.up ℕ)) n x hx) =
      ⟨cycleClass (K.X 0) n (totalSummandProjectionAt K 0 n n (by omega) x)
        (leading_cycle K 0 n n (by omega) x hx (by intro p q hpq hp; omega)),
        leading_horizontal_cycle K 0 n n (by omega) x hx (by intro p q hpq hp; omega)⟩ :=
  Subtype.ext (edgeMap_cycleClass_val K n x hx)

theorem edgeMap_isIso_of_bijective (n : ℕ) (h : Function.Bijective (edgeMap K n)) :
    IsIso (edgeMap K n) := (ConcreteCategory.isIso_iff_bijective _).mpr h

def edgeIsoOfBijective (n : ℕ) (h : Function.Bijective (edgeMap K n)) :
    (K.total (ComplexShape.up ℕ)).homology n ≅ ModuleCat.of R (edgeKernel K n) := by
  letI := edgeMap_isIso_of_bijective K n h
  exact asIso (edgeMap K n)

@[simp] theorem edgeIsoOfBijective_hom (n : ℕ) (h : Function.Bijective (edgeMap K n)) :
    (edgeIsoOfBijective K n h).hom = edgeMap K n := rfl

end Sharpness.ElementaryCochainEdge
