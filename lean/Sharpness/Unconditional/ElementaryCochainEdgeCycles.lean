import Mathlib.Algebra.Homology.ConcreteCategory
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.QuasiIso

/-! Native cycle representatives and boundary detection for nonnegative
cochain complexes. Degree zero uses the actual zero incoming differential. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
universe u v
namespace Sharpness.ElementaryCochainEdge
open CategoryTheory CategoryTheory.Limits HomologicalComplex

variable {R : Type u} [Ring R]

def Cycle (K : CochainComplex (ModuleCat.{v} R) ℕ) (n : ℕ) (x : K.X n) : Prop :=
  ∀ j, K.d n j x = 0

def cycleClass (K : CochainComplex (ModuleCat.{v} R) ℕ) (n : ℕ)
    (x : K.X n) (hx : Cycle K n x) : K.homology n :=
  K.homologyπ n (K.cyclesMk x _ rfl (hx _))

theorem cycle_iCycles (K : CochainComplex (ModuleCat.{v} R) ℕ) (n : ℕ)
    (z : K.cycles n) : Cycle K n (K.iCycles n z) := by
  intro j
  exact congrArg (fun f => f.hom z) (K.iCycles_d n j)

theorem cycleClass_surjective (K : CochainComplex (ModuleCat.{v} R) ℕ) (n : ℕ)
    (z : K.homology n) : ∃ (x : K.X n) (hx : Cycle K n x), cycleClass K n x hx = z := by
  obtain ⟨y, rfl⟩ := (ModuleCat.epi_iff_surjective (K.homologyπ n)).mp inferInstance z
  refine ⟨K.iCycles n y, cycle_iCycles K n y, ?_⟩
  unfold cycleClass
  congr 1
  apply (ModuleCat.mono_iff_injective (K.iCycles n)).mp inferInstance
  exact K.i_cyclesMk _ _ rfl _

theorem cycleClass_eq_zero_iff (K : CochainComplex (ModuleCat.{v} R) ℕ) (n : ℕ)
    (x : K.X n) (hx : Cycle K n x) :
    cycleClass K n x hx = 0 ↔ ∃ y : K.X (n-1), K.d (n-1) n y = x := by
  have hp : (ComplexShape.up ℕ).prev n = n-1 := by
    cases n <;> simp
  have he : K.homologyι n (cycleClass K n x hx) = K.pOpcycles n x := by
    have h := congrArg (fun f => f.hom (K.cyclesMk x _ rfl (hx _))) (K.homology_π_ι n)
    change K.homologyι n (cycleClass K n x hx) =
      K.pOpcycles n (K.iCycles n (K.cyclesMk x _ rfl (hx _))) at h
    exact h.trans (congrArg (K.pOpcycles n) (K.i_cyclesMk x _ rfl (hx _)))
  have hz : cycleClass K n x hx = 0 ↔ K.pOpcycles n x = 0 := by
    rw [← he]
    exact ⟨fun h => by rw [h, map_zero], fun h =>
      (ModuleCat.mono_iff_injective (K.homologyι n)).mp inferInstance (h.trans (map_zero _).symm)⟩
  rw [hz]
  have h := (K.sc n).moduleCat_pOpcycles_eq_zero_iff x
  change K.pOpcycles n x = 0 ↔ ∃ y : K.X ((ComplexShape.up ℕ).prev n),
    K.d ((ComplexShape.up ℕ).prev n) n y = x at h
  rw [hp] at h
  exact h

theorem cycle_map {K L : CochainComplex (ModuleCat.{v} R) ℕ} (f : K ⟶ L)
    (n : ℕ) (x : K.X n) (hx : Cycle K n x) : Cycle L n (f.f n x) := by
  intro j
  have h := congrArg (fun g => g.hom x) (f.comm n j)
  change L.d n j (f.f n x) = f.f j (K.d n j x) at h
  rw [h, hx j, map_zero]

theorem cycleClass_map {K L : CochainComplex (ModuleCat.{v} R) ℕ} (f : K ⟶ L)
    (n : ℕ) (x : K.X n) (hx : Cycle K n x) :
    homologyMap f n (cycleClass K n x hx) =
      cycleClass L n (f.f n x) (cycle_map f n x hx) := by
  unfold cycleClass
  have h := congrArg (fun g => g.hom (K.cyclesMk x _ rfl (hx _)))
    (homologyπ_naturality f n)
  change homologyMap f n (K.homologyπ n (K.cyclesMk x _ rfl (hx _))) =
    L.homologyπ n (cyclesMap f n (K.cyclesMk x _ rfl (hx _))) at h
  rw [h]
  congr 1
  apply (ModuleCat.mono_iff_injective (L.iCycles n)).mp inferInstance
  have hm := congrArg (fun g => g.hom (K.cyclesMk x _ rfl (hx _))) (cyclesMap_i f n)
  change L.iCycles n (cyclesMap f n (K.cyclesMk x _ rfl (hx _))) =
    f.f n (K.iCycles n (K.cyclesMk x _ rfl (hx _))) at hm
  exact (hm.trans (congrArg (f.f n) (K.i_cyclesMk x _ rfl (hx _)))).trans
    (L.i_cyclesMk _ _ rfl _).symm

theorem cycleClass_eq_iff (K : CochainComplex (ModuleCat.{v} R) ℕ) (n : ℕ)
    (x y : K.X n) (hx : Cycle K n x) (hy : Cycle K n y) :
    cycleClass K n x hx = cycleClass K n y hy ↔
      ∃ z : K.X (n-1), K.d (n-1) n z = x-y := by
  have he (x : K.X n) (hx : Cycle K n x) :
      K.homologyι n (cycleClass K n x hx) = K.pOpcycles n x := by
    have h := congrArg (fun f => f.hom (K.cyclesMk x _ rfl (hx _))) (K.homology_π_ι n)
    change K.homologyι n (cycleClass K n x hx) =
      K.pOpcycles n (K.iCycles n (K.cyclesMk x _ rfl (hx _))) at h
    exact h.trans (congrArg (K.pOpcycles n) (K.i_cyclesMk x _ rfl (hx _)))
  have hi := (ModuleCat.mono_iff_injective (K.homologyι n)).mp inferInstance
  rw [← hi.eq_iff, he x hx, he y hy]
  have hp : (ComplexShape.up ℕ).prev n = n-1 := by
    cases n <;> simp
  have h := (K.sc n).moduleCat_pOpcycles_eq_iff x y
  change K.pOpcycles n x = K.pOpcycles n y ↔
    ∃ z : K.X ((ComplexShape.up ℕ).prev n),
      K.d ((ComplexShape.up ℕ).prev n) n z = x-y at h
  rw [hp] at h
  exact h


theorem cycle_iff (K : CochainComplex (ModuleCat.{v} R) ℕ) (n : ℕ) (x : K.X n) :
    Cycle K n x ↔ K.d n (n+1) x = 0 := by
  refine ⟨fun h => h _, ?_⟩
  intro hx j
  by_cases h : n+1 = j
  · subst j
    exact hx
  · rw [K.shape n j h]
    rfl

theorem cycle_zero (K : CochainComplex (ModuleCat.{v} R) ℕ) (n : ℕ) :
    Cycle K n 0 := fun _ => map_zero _

theorem cycle_add (K : CochainComplex (ModuleCat.{v} R) ℕ) (n : ℕ)
    (x y : K.X n) (hx : Cycle K n x) (hy : Cycle K n y) : Cycle K n (x+y) := by
  intro j
  rw [map_add, hx j, hy j, add_zero]

theorem cycle_sub (K : CochainComplex (ModuleCat.{v} R) ℕ) (n : ℕ)
    (x y : K.X n) (hx : Cycle K n x) (hy : Cycle K n y) : Cycle K n (x-y) := by
  intro j
  rw [map_sub, hx j, hy j, sub_self]

theorem cycleClass_homologyι (K : CochainComplex (ModuleCat.{v} R) ℕ) (n : ℕ)
    (x : K.X n) (hx : Cycle K n x) :
    K.homologyι n (cycleClass K n x hx) = K.pOpcycles n x := by
  have h := congrArg (fun f => f.hom (K.cyclesMk x _ rfl (hx _))) (K.homology_π_ι n)
  change K.homologyι n (cycleClass K n x hx) =
    K.pOpcycles n (K.iCycles n (K.cyclesMk x _ rfl (hx _))) at h
  exact h.trans (congrArg (K.pOpcycles n) (K.i_cyclesMk x _ rfl (hx _)))

@[simp] theorem cycleClass_zero (K : CochainComplex (ModuleCat.{v} R) ℕ) (n : ℕ) :
    cycleClass K n 0 (cycle_zero K n) = 0 := by
  apply (ModuleCat.mono_iff_injective (K.homologyι n)).mp inferInstance
  rw [cycleClass_homologyι, map_zero, map_zero]

theorem cycleClass_add (K : CochainComplex (ModuleCat.{v} R) ℕ) (n : ℕ)
    (x y : K.X n) (hx : Cycle K n x) (hy : Cycle K n y) :
    cycleClass K n (x+y) (cycle_add K n x y hx hy) =
      cycleClass K n x hx + cycleClass K n y hy := by
  apply (ModuleCat.mono_iff_injective (K.homologyι n)).mp inferInstance
  simp only [cycleClass_homologyι, map_add]

theorem cycleClass_sub (K : CochainComplex (ModuleCat.{v} R) ℕ) (n : ℕ)
    (x y : K.X n) (hx : Cycle K n x) (hy : Cycle K n y) :
    cycleClass K n (x-y) (cycle_sub K n x y hx hy) =
      cycleClass K n x hx - cycleClass K n y hy := by
  apply (ModuleCat.mono_iff_injective (K.homologyι n)).mp inferInstance
  simp only [cycleClass_homologyι, map_sub]

@[simp] theorem cycleClass_eq_zero_iff_zero (K : CochainComplex (ModuleCat.{v} R) ℕ)
    (x : K.X 0) (hx : Cycle K 0 x) : cycleClass K 0 x hx = 0 ↔ x = 0 := by
  rw [cycleClass_eq_zero_iff]
  change (∃ y : K.X 0, K.d 0 0 y = x) ↔ x = 0
  rw [K.shape 0 0 (by decide)]
  change (∃ _ : K.X 0, (0 : K.X 0) = x) ↔ x = 0
  constructor
  · rintro ⟨_, h⟩
    exact h.symm
  · intro h
    exact ⟨0, h.symm⟩

theorem exactAt_boundary (K : CochainComplex (ModuleCat.{v} R) ℕ) (n : ℕ)
    (hK : K.ExactAt n) (x : K.X n) (hx : Cycle K n x) :
    ∃ y : K.X (n-1), K.d (n-1) n y = x := by
  apply (cycleClass_eq_zero_iff K n x hx).mp
  letI : Subsingleton (K.homology n) := ModuleCat.isZero_iff_subsingleton.mp hK.isZero_homology
  exact Subsingleton.elim _ _

theorem exactAt_succ_boundary (K : CochainComplex (ModuleCat.{v} R) ℕ) (n : ℕ)
    (hK : K.ExactAt (n+1)) (x : K.X (n+1)) (hx : Cycle K (n+1) x) :
    ∃ y : K.X n, K.d n (n+1) y = x := by
  simpa using exactAt_boundary K (n+1) hK x hx

theorem cycle_smul (K : CochainComplex (ModuleCat.{v} R) ℕ) (n : ℕ)
    (r : R) (x : K.X n) (hx : Cycle K n x) : Cycle K n (r • x) := by
  intro j
  rw [map_smul, hx j, smul_zero]

theorem cycleClass_smul (K : CochainComplex (ModuleCat.{v} R) ℕ) (n : ℕ)
    (r : R) (x : K.X n) (hx : Cycle K n x) :
    cycleClass K n (r • x) (cycle_smul K n r x hx) = r • cycleClass K n x hx := by
  apply (ModuleCat.mono_iff_injective (K.homologyι n)).mp inferInstance
  simp only [cycleClass_homologyι, map_smul]

theorem cycle_boundary (K : CochainComplex (ModuleCat.{v} R) ℕ) (m n : ℕ)
    (y : K.X m) : Cycle K n (K.d m n y) := by
  intro j
  have h := congrArg (fun f => f.hom y) (K.d_comp_d m n j)
  exact h

theorem cycleClass_boundary (K : CochainComplex (ModuleCat.{v} R) ℕ) (n : ℕ)
    (y : K.X (n-1)) :
    cycleClass K n (K.d (n-1) n y) (cycle_boundary K (n-1) n y) = 0 :=
  (cycleClass_eq_zero_iff K n _ _).mpr ⟨y, rfl⟩

end Sharpness.ElementaryCochainEdge
