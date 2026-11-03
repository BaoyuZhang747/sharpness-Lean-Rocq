import Sharpness.FirstQuadrantFilteredCochains
import Mathlib.Algebra.Homology.Embedding.Extend
import Mathlib.Algebra.Homology.Embedding.ExtendHomology

/-! The actual column filtration is a functor on the reverse ordered
natural numbers. Its morphisms are literal subtype inclusions. Extension
by zero supplies integer-indexed cochain complexes, for native mapping
cones and their spectral objects. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
universe u
namespace Sharpness
open CategoryTheory Opposite
variable {R : Type u} [CommRing R]
    (K : HomologicalComplex₂ (ModuleCat.{u} R) (ComplexShape.up ℕ) (ComplexShape.up ℕ))

theorem totalColumnFilteredComplex_d (k n : ℕ) :
    (totalColumnFilteredComplex K k).d n (n+1) =
      ModuleCat.ofHom (totalColumnFilteredDifferential K k n) :=
  (totalColumnSubmodules K k).complex_d n

def totalColumnFilteredMap {k l : ℕ} (h : k ≤ l) :
    totalColumnFilteredComplex K l ⟶ totalColumnFilteredComplex K k :=
  CochainSubmodules.map (V := totalColumnSubmodules K l) (W := totalColumnSubmodules K k)
    (fun n => totalColumnFiltration_antitone K n h)

theorem totalColumnFilteredMap_id (k : ℕ) : totalColumnFilteredMap K (le_refl k) = 𝟙 _ :=
  CochainSubmodules.map_id

theorem totalColumnFilteredMap_comp {k l m : ℕ} (h : k ≤ l) (g : l ≤ m) :
    totalColumnFilteredMap K (h.trans g) = totalColumnFilteredMap K g ≫ totalColumnFilteredMap K h :=
  CochainSubmodules.map_comp (fun n => totalColumnFiltration_antitone K n g)
    (fun n => totalColumnFiltration_antitone K n h)

def totalColumnFiltrationFunctor : ℕᵒᵈ ⥤ CochainComplex (ModuleCat.{u} R) ℕ where
  obj k := totalColumnFilteredComplex K (OrderDual.ofDual k)
  map f := totalColumnFilteredMap K (leOfHom f)
  map_id k := totalColumnFilteredMap_id K (OrderDual.ofDual k)
  map_comp f g := totalColumnFilteredMap_comp K (leOfHom g) (leOfHom f)

def totalColumnFiltrationIntFunctor : ℕᵒᵈ ⥤ CochainComplex (ModuleCat.{u} R) ℤ :=
  totalColumnFiltrationFunctor K ⋙
    ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{u} R)

end Sharpness
