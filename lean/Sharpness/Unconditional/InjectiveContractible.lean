import Mathlib.CategoryTheory.Abelian.Injective.Resolution

/-! An acyclic nonnegative complex of injectives is contractible. Consequently
every additive functor sends it to an acyclic complex. This is the homological
step in the centralizer detection argument. -/

set_option autoImplicit false
noncomputable section
universe u v w z

namespace Sharpness
open CategoryTheory CategoryTheory.Limits HomologicalComplex ZeroObject

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Regard an acyclic complex of injectives as an injective resolution of zero. -/
def acyclicInjectiveResolution (K : CochainComplex C ℕ)
    [∀ n, Injective (K.X n)] (hK : ∀ n, K.ExactAt n) : InjectiveResolution (0 : C) where
  cocomplex := K
  ι := 0
  quasiIso := by
    rw [quasiIso_iff]
    intro n
    rw [quasiIsoAt_iff_isIso_homologyMap]
    exact ((homologyFunctor C (ComplexShape.up ℕ) n).map_isZero
      ((CochainComplex.single₀ C).map_isZero (isZero_zero C))).isIso
      ((hK n).isZero_homology) _

/-- A contracting homotopy for an acyclic nonnegative complex of injectives. -/
def acyclicInjectiveHomotopy (K : CochainComplex C ℕ)
    [∀ n, Injective (K.X n)] (hK : ∀ n, K.ExactAt n) : Homotopy (𝟙 K) 0 :=
  InjectiveResolution.descHomotopyZero
    (I := acyclicInjectiveResolution K hK) (J := acyclicInjectiveResolution K hK)
    (𝟙 K) (by
      change (0 : (CochainComplex.single₀ C).obj (0 : C) ⟶ K) ≫ 𝟙 K = 0
      exact zero_comp)

/-- An additive functor preserves the acyclicity of a nonnegative acyclic
complex of injectives, without any exactness assumption on the functor. -/
theorem map_acyclic_injective_exactAt
    {D : Type w} [Category.{z} D] [Abelian D]
    (F : C ⥤ D) [F.Additive] (K : CochainComplex C ℕ)
    [∀ n, Injective (K.X n)] (hK : ∀ n, K.ExactAt n) (n : ℕ) :
    ((F.mapHomologicalComplex _).obj K).ExactAt n := by
  rw [exactAt_iff_isZero_homology, IsZero.iff_id_eq_zero]
  have h := (F.mapHomotopy (acyclicInjectiveHomotopy K hK)).homologyMap_eq n
  simpa using h

end Sharpness
