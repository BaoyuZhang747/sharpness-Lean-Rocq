import Sharpness.FirstQuadrantTotalFiltration
import Sharpness.SubmoduleCochainComplex

/-! The column filtration is preserved by the actual total differential.
Each filtration term is therefore an actual cochain complex, with its
actual inclusion into the total complex. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory
variable {R : Type u} [CommRing R]
    (K : HomologicalComplex₂ (ModuleCat.{u} R) (ComplexShape.up ℕ) (ComplexShape.up ℕ))

set_option backward.isDefEq.respectTransparency false in
theorem cochainNatBicomplexTotal_d (i n : ℕ) :
    K.ιTotal (ComplexShape.up ℕ) i n (i+n) rfl ≫
        (K.total (ComplexShape.up ℕ)).d (i+n) (i+n+1) =
      (K.d i (i+1)).f n ≫ K.ιTotal (ComplexShape.up ℕ)
            (i+1) n (i+n+1) (by change i+1+n=i+n+1; omega) +
        (-1 : ℤˣ)^i •
          ((K.X i).d n (n+1) ≫ K.ιTotal (ComplexShape.up ℕ)
              i (n+1) (i+n+1) (by change i+(n+1)=i+n+1; omega)) := by
  rw [HomologicalComplex₂.total_d, Preadditive.comp_add,
    HomologicalComplex₂.ι_D₁, HomologicalComplex₂.ι_D₂,
    HomologicalComplex₂.d₁_eq _ _ (show (ComplexShape.up ℕ).Rel i (i+1) from rfl) n
      (i+n+1) (by change i+1+n=i+n+1; omega),
    HomologicalComplex₂.d₂_eq _ _ i (show (ComplexShape.up ℕ).Rel n (n+1) from rfl)
      (i+n+1) (by change i+(n+1)=i+n+1; omega)]
  simp only [cochainNatTotalHorizontalSign, cochainNatTotalVerticalSign, one_smul]

set_option backward.isDefEq.respectTransparency false in
theorem totalColumnFiltration_d (k n : ℕ) :
    totalColumnFiltration K k n ≤
      (totalColumnFiltration K k (n+1)).comap
        ((K.total (ComplexShape.up ℕ)).d n (n+1)).hom := by
  refine iSup_le fun i => iSup_le fun j => iSup_le fun h => iSup_le fun hk => ?_
  rintro y ⟨x, rfl⟩
  subst n
  have hd := congrArg (fun f => f x) (cochainNatBicomplexTotal_d K i j)
  change (K.total (ComplexShape.up ℕ)).d (i+j) (i+j+1)
      (K.ιTotal (ComplexShape.up ℕ) i j (i+j) rfl x) =
    K.ιTotal (ComplexShape.up ℕ) (i+1) j (i+j+1) (by change i+1+j=i+j+1; omega)
        ((K.d i (i+1)).f j x) +
      (((-1 : ℤˣ)^i : ℤ) •
        K.ιTotal (ComplexShape.up ℕ) i (j+1) (i+j+1) (by change i+(j+1)=i+j+1; omega)
          ((K.X i).d j (j+1) x)) at hd
  change (K.total (ComplexShape.up ℕ)).d (i+j) (i+j+1)
      (K.ιTotal (ComplexShape.up ℕ) i j (i+j) rfl x) ∈
        totalColumnFiltration K k (i+j+1)
  rw [hd]
  exact (totalColumnFiltration K k (i+j+1)).add_mem
    (totalColumnFiltration_summand_mem K k (i+1) j (i+j+1) (by omega) (by omega) _)
    ((totalColumnFiltration K k (i+j+1)).toAddSubgroup.zsmul_mem
      (totalColumnFiltration_summand_mem K k i (j+1) (i+j+1) (by omega) hk _) _)

def totalColumnSubmodules (k : ℕ) : CochainSubmodules (K.total (ComplexShape.up ℕ)) where
  term n := totalColumnFiltration K k n
  d_mem := totalColumnFiltration_d K k

def totalColumnFilteredDifferential (k n : ℕ) :
    totalColumnFiltration K k n →ₗ[R] totalColumnFiltration K k (n+1) :=
  (totalColumnSubmodules K k).differential n

def totalColumnFilteredComplex (k : ℕ) : CochainComplex (ModuleCat.{u} R) ℕ :=
  (totalColumnSubmodules K k).complex

def totalColumnFilteredInclusion (k : ℕ) :
    totalColumnFilteredComplex K k ⟶ K.total (ComplexShape.up ℕ) :=
  (totalColumnSubmodules K k).inclusion

end Sharpness
