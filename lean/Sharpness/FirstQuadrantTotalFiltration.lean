import Sharpness.CochainNatTotalSigns
import Mathlib.Algebra.Homology.TotalComplex
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.LinearAlgebra.Quotient.Basic

/-! The descending column filtration on an actual first-quadrant cochain
totalization. Its terms are spans of the actual total summands with
horizontal degree at least k. It starts at the whole module and stops
after total degree n; these are proved, not supplied convergence fields. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory CategoryTheory.Limits
variable {R : Type u} [CommRing R]
    (K : HomologicalComplex₂ (ModuleCat.{u} R) (ComplexShape.up ℕ) (ComplexShape.up ℕ))

def totalColumnFiltration (k n : ℕ) : Submodule R ((K.total (ComplexShape.up ℕ)).X n) :=
  ⨆ (i : ℕ) (j : ℕ) (h : i+j=n) (_hk : k ≤ i),
    LinearMap.range (K.ιTotal (ComplexShape.up ℕ) i j n h).hom

theorem totalColumnFiltration_summand_mem (k i j n : ℕ) (h : i+j=n) (hk : k ≤ i)
    (x : (K.X i).X j) :
    K.ιTotal (ComplexShape.up ℕ) i j n h x ∈ totalColumnFiltration K k n := by
  have hrange : LinearMap.range (K.ιTotal (ComplexShape.up ℕ) i j n h).hom ≤
      totalColumnFiltration K k n :=
    le_iSup_of_le i (le_iSup_of_le j (le_iSup_of_le h
      (le_iSup_of_le hk le_rfl)))
  exact hrange ⟨x, rfl⟩

theorem totalColumnFiltration_antitone (n : ℕ) : Antitone (fun k => totalColumnFiltration K k n) := by
  intro k l hkl
  refine iSup_le fun i => iSup_le fun j => iSup_le fun h => iSup_le fun hli => ?_
  exact le_iSup_of_le i (le_iSup_of_le j (le_iSup_of_le h
    (le_iSup_of_le (hkl.trans hli) le_rfl)))

theorem totalColumnFiltration_stop (n : ℕ) : totalColumnFiltration K (n+1) n = ⊥ := by
  apply le_bot_iff.mp
  refine iSup_le fun i => iSup_le fun j => iSup_le fun h => iSup_le fun hk => ?_
  omega

set_option backward.isDefEq.respectTransparency false in
theorem totalColumnFiltration_start (n : ℕ) : totalColumnFiltration K 0 n = ⊤ := by
  let W := totalColumnFiltration K 0 n
  have hzero : (ModuleCat.ofHom W.mkQ :
      (K.total (ComplexShape.up ℕ)).X n ⟶
        ModuleCat.of R ((K.total (ComplexShape.up ℕ)).X n ⧸ W)) = 0 := by
    apply HomologicalComplex₂.total.hom_ext
    intro i j h
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change W.mkQ (K.ιTotal (ComplexShape.up ℕ) i j n h x) = 0
    exact (Submodule.Quotient.mk_eq_zero W).mpr
      (totalColumnFiltration_summand_mem K 0 i j n h (Nat.zero_le _) x)
  apply top_unique
  intro x _
  exact (Submodule.Quotient.mk_eq_zero W).mp
    (congrArg (fun f : (K.total (ComplexShape.up ℕ)).X n ⟶
      ModuleCat.of R ((K.total (ComplexShape.up ℕ)).X n ⧸ W) => f x) hzero)

end Sharpness
