import Sharpness.ColumnSpectralConvergence
import Sharpness.ColumnHomologyFiltration

/-! The filtration in the constructed convergence data is exactly the
image filtration of the original total complex, rather than merely an
unrelated finite filtration on an isomorphic module. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory

theorem range_map_of_commuting_equiv
    {R A B A' B' : Type u} [CommRing R]
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup A'] [Module R A'] [AddCommGroup B'] [Module R B']
    (f : A →ₗ[R] B) (g : A' →ₗ[R] B') (eA : A ≃ₗ[R] A') (eB : B ≃ₗ[R] B')
    (h : ∀ a, g (eA a) = eB (f a)) :
    f.range.map eB.toLinearMap = g.range := by
  ext y
  constructor
  · rintro ⟨x, ⟨a, ha⟩, he⟩
    exact ⟨eA a, (h a).trans ((congrArg eB ha).trans he)⟩
  · rintro ⟨a, rfl⟩
    refine ⟨f (eA.symm a), ⟨eA.symm a, rfl⟩, ?_⟩
    exact (h (eA.symm a)).symm.trans (congrArg g (eA.apply_symm_apply a))

variable {R : Type u} [CommRing R]
    (K : HomologicalComplex₂ (ModuleCat.{u} R) (ComplexShape.up ℕ) (ComplexShape.up ℕ))

def totalColumnExtendedHomologyIso (k n : ℕ) :
    ((totalColumnFiltrationIntFunctor K).obj (OrderDual.toDual k)).homology (n : ℤ) ≅
      (totalColumnFilteredComplex K k).homology n :=
  (totalColumnFilteredComplex K k).extendHomologyIso ComplexShape.embeddingUpNat
    (show ComplexShape.embeddingUpNat.f n = (n : ℤ) from rfl)

set_option backward.isDefEq.respectTransparency false in
theorem totalColumnAbutmentIso_filteredMap (k n : ℕ) :
    filteredCohomologyMap (totalColumnFiltrationIntFunctor K) n k 0 (Nat.zero_le k) ≫
      (totalColumnAbutmentIso K n).hom =
    (totalColumnExtendedHomologyIso K k n).hom ≫
      HomologicalComplex.homologyMap (totalColumnFilteredInclusion K k) n := by
  have hn := HomologicalComplex.extendHomologyIso_hom_naturality
    (totalColumnFilteredMap K (Nat.zero_le k)) ComplexShape.embeddingUpNat
      (show ComplexShape.embeddingUpNat.f n = (n : ℤ) from rfl)
  have hc := CochainSubmodules.map_inclusion
    (V := totalColumnSubmodules K k) (W := totalColumnSubmodules K 0)
      (fun i => totalColumnFiltration_antitone K i (Nat.zero_le k))
  have hn' : filteredCohomologyMap (totalColumnFiltrationIntFunctor K) n k 0
        (Nat.zero_le k) ≫ (totalColumnExtendedHomologyIso K 0 n).hom =
      (totalColumnExtendedHomologyIso K k n).hom ≫
        HomologicalComplex.homologyMap (totalColumnFilteredMap K (Nat.zero_le k)) n := hn
  have hc' : HomologicalComplex.homologyMap (totalColumnFilteredMap K (Nat.zero_le k)) n ≫
      HomologicalComplex.homologyMap (totalColumnFilteredInclusion K 0) n =
        HomologicalComplex.homologyMap (totalColumnFilteredInclusion K k) n :=
    (HomologicalComplex.homologyMap_comp _ _ n).symm.trans
      (congrArg (fun f => HomologicalComplex.homologyMap f n) hc)
  calc
    _ = (filteredCohomologyMap (totalColumnFiltrationIntFunctor K) n k 0 (Nat.zero_le k) ≫
        (totalColumnExtendedHomologyIso K 0 n).hom) ≫
          HomologicalComplex.homologyMap (totalColumnFilteredInclusion K 0) n :=
      (Category.assoc _ _ _).symm
    _ = ((totalColumnExtendedHomologyIso K k n).hom ≫
        HomologicalComplex.homologyMap (totalColumnFilteredMap K (Nat.zero_le k)) n) ≫
          HomologicalComplex.homologyMap (totalColumnFilteredInclusion K 0) n :=
      congrArg (fun f => f ≫ HomologicalComplex.homologyMap (totalColumnFilteredInclusion K 0) n) hn'
    _ = _ := (Category.assoc _ _ _).trans
      (congrArg (fun f => (totalColumnExtendedHomologyIso K k n).hom ≫ f) hc')

theorem totalColumnConvergence_filtration (n k : ℕ) :
    (totalColumnConvergence K).filtration n k = totalColumnHomologyFiltration K n k := by
  exact range_map_of_commuting_equiv
    (filteredCohomologyMap (totalColumnFiltrationIntFunctor K) n k 0 (Nat.zero_le k)).hom
    (HomologicalComplex.homologyMap (totalColumnFilteredInclusion K k) n).hom
    (totalColumnExtendedHomologyIso K k n).toLinearEquiv
    (totalColumnAbutmentIso K n).toLinearEquiv
    (fun a => (congrArg (fun f => f a) (totalColumnAbutmentIso_filteredMap K k n)).symm)

end Sharpness
