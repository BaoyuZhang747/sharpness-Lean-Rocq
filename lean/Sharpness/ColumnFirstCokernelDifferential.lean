import Sharpness.ColumnFirstDifferential
import Sharpness.ColumnAssociatedGraded
import Sharpness.FilteredConeSpectralDelta

/-! The actual native first differential, under the actual adjacent
quotient comparisons, is the actual filtered short-exact-sequence
connecting map followed by the next quotient projection. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
universe u v
namespace Sharpness
open CategoryTheory CategoryTheory.Limits
attribute [-simp] Fin.reduceFinMk

theorem isoDifferential_desc {C : Type u} [Category.{v} C]
    {U V A B A' B' : C} (d : U ⟶ V) (a : U ≅ A) (b : V ≅ B)
    (c : A ⟶ B) (e : A ⟶ A') (f : B ⟶ B') (d' : A' ⟶ B')
    (hd : d = a.hom ≫ c ≫ b.inv) (hc : c ≫ f = e ≫ d') :
    d ≫ (b.hom ≫ f) = (a.hom ≫ e) ≫ d' := by
  calc
    _ = (a.hom ≫ c ≫ b.inv) ≫ (b.hom ≫ f) := congrArg (fun t => t ≫ (b.hom ≫ f)) hd
    _ = a.hom ≫ (c ≫ f) := by simp only [Category.assoc, Iso.inv_hom_id_assoc]
    _ = a.hom ≫ (e ≫ d') := congrArg (fun t => a.hom ≫ t) hc
    _ = _ := (Category.assoc _ _ _).symm

variable {R : Type u} [CommRing R]
    (K : HomologicalComplex₂ (ModuleCat.{u} R) (ComplexShape.up ℕ) (ComplexShape.up ℕ))

def totalColumnAdjacentIntMap (p : ℕ) :
    (totalColumnFiltrationIntFunctor K).obj (OrderDual.toDual (p+1)) ⟶
      (totalColumnFiltrationIntFunctor K).obj (OrderDual.toDual p) :=
  (totalColumnFiltrationIntFunctor K).map
    (homOfLE (show OrderDual.toDual (p+1) ≤ OrderDual.toDual p from Nat.le_succ p))

theorem totalColumnAdjacentIntMap_mono (p : ℕ) : Mono (totalColumnAdjacentIntMap K p) :=
  totalColumnFilteredExtendedMap_mono K (Nat.le_succ p)

set_option backward.isDefEq.respectTransparency false in
def totalColumnCokernelDifferential (p q : ℕ) :
    (totalColumnAssociatedGraded K p).homology ((p : ℤ)+q) ⟶
      (totalColumnAssociatedGraded K (p+1)).homology (((p+1 : ℕ) : ℤ)+q) := by
  letI := totalColumnAdjacentIntMap_mono K p
  exact (monoCokernelShortComplex_shortExact (totalColumnAdjacentIntMap K p)).δ
      ((p : ℤ)+q) (((p+1 : ℕ) : ℤ)+q) (by change (p : ℤ)+q+1 = ((p+1 : ℕ) : ℤ)+q; omega) ≫
    HomologicalComplex.homologyMap (cokernel.π (totalColumnAdjacentIntMap K (p+1)))
      (((p+1 : ℕ) : ℤ)+q)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
theorem totalColumnFirstPageAssociatedGradedIso_d (p q : ℕ) :
    ((totalColumnSpectralSequence K).page 1).d (p,q) (p+1,q) ≫
        (totalColumnFirstPageAssociatedGradedIso K (p+1) q).hom =
      (totalColumnFirstPageAssociatedGradedIso K p q).hom ≫ totalColumnCokernelDifferential K p q := by
  letI := totalColumnAdjacentIntMap_mono K p
  letI := totalColumnAdjacentIntMap_mono K (p+1)
  let f := homOfLE (show OrderDual.toDual (p+2) ≤ OrderDual.toDual (p+1) from Nat.le_succ (p+1))
  let g := homOfLE (show OrderDual.toDual (p+1) ≤ OrderDual.toDual p from Nat.le_succ p)
  letI : Mono ((totalColumnFiltrationIntFunctor K).map f) := totalColumnAdjacentIntMap_mono K (p+1)
  letI : Mono ((totalColumnFiltrationIntFunctor K).map g) := totalColumnAdjacentIntMap_mono K p
  have h := isoDifferential_desc
    (((totalColumnSpectralSequence K).page 1).d (p,q) (p+1,q))
    (columnSpectralSequenceFirstPageIso (columnMappingConeSpectralObject K) p q)
    (columnSpectralSequenceFirstPageIso (columnMappingConeSpectralObject K) (p+1) q)
    ((columnMappingConeSpectralObject K).δ f g ((p : ℤ)+q) (((p+1 : ℕ) : ℤ)+q)
      (by change (p : ℤ)+q+1 = ((p+1 : ℕ) : ℤ)+q; omega))
    (homotopyConeCokernelIso (totalColumnAdjacentIntMap K p) ((p : ℤ)+q)).hom
    (homotopyConeCokernelIso (totalColumnAdjacentIntMap K (p+1)) (((p+1 : ℕ) : ℤ)+q)).hom
    (totalColumnCokernelDifferential K p q)
    (columnSpectralSequence_first_d_eq (columnMappingConeSpectralObject K) p q)
    (filteredConeSpectralObject_delta_cokernel (totalColumnFiltrationIntFunctor K) f g
      ((p : ℤ)+q) (((p+1 : ℕ) : ℤ)+q)
      (by change (p : ℤ)+q+1 = ((p+1 : ℕ) : ℤ)+q; omega))
  simpa only [totalColumnFirstPageAssociatedGradedIso, totalColumnFirstPageIso,
    columnMappingConeRelativeIso, homotopyConeCokernelIso, totalColumnAdjacentIntMap,
    HomotopyCategory.composableArrowsFunctor, Functor.mapComposableArrows,
    Functor.comp_map,
    Functor.whiskeringRight, ComposableArrows.map', ComposableArrows.Mk₁.map,
    ComposableArrows.Mk₁.obj, ComposableArrows.mk₁,
    Iso.trans_hom, Category.assoc] using h

attribute [simp] Fin.reduceFinMk
end Sharpness
