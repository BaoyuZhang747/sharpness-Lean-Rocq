import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-! Actual subcomplexes of module cochains, given by differential-stable
submodules. Inclusion maps and their laws are proved once with an opaque
ambient complex, avoiding repeated reduction of a concrete totalization. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory
variable {R : Type u} [CommRing R] (T : CochainComplex (ModuleCat.{u} R) ℕ)

structure CochainSubmodules where
  term : ∀ n : ℕ, Submodule R (T.X n)
  d_mem : ∀ n, term n ≤ (term (n+1)).comap (T.d n (n+1)).hom

namespace CochainSubmodules
variable {T} (V : CochainSubmodules T)

def differential (n : ℕ) : V.term n →ₗ[R] V.term (n+1) where
  toFun x := ⟨T.d n (n+1) x.val, V.d_mem n x.property⟩
  map_add' x y := Subtype.ext ((T.d n (n+1)).hom.map_add _ _)
  map_smul' r x := Subtype.ext ((T.d n (n+1)).hom.map_smul _ _)

def complex : CochainComplex (ModuleCat.{u} R) ℕ :=
  CochainComplex.of (fun n => ModuleCat.of R (V.term n))
    (fun n => ModuleCat.ofHom (V.differential n)) (by
      intro n
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      exact congrArg (fun f => f x.val) (T.d_comp_d n (n+1) (n+1+1)))

theorem complex_d (n : ℕ) : V.complex.d n (n+1) = ModuleCat.ofHom (V.differential n) := by
  dsimp only [complex]
  exact CochainComplex.of_d _ _ n

def inclusion : V.complex ⟶ T :=
  CochainComplex.ofHom (fun n => ModuleCat.ofHom (V.term n).subtype) (by
    intro n
    rw [V.complex_d]
    rfl)

variable {V} {W U : CochainSubmodules T}

def map (h : ∀ n, V.term n ≤ W.term n) : V.complex ⟶ W.complex :=
  CochainComplex.ofHom (fun n => ModuleCat.ofHom (Submodule.inclusion (h n))) (by
    intro n
    rw [V.complex_d, W.complex_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    rfl)

theorem map_id : map (fun n => le_refl (V.term n)) = 𝟙 V.complex := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

theorem map_comp (h : ∀ n, V.term n ≤ W.term n) (g : ∀ n, W.term n ≤ U.term n) :
    map (fun n => (h n).trans (g n)) = map h ≫ map g := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

theorem map_inclusion (h : ∀ n, V.term n ≤ W.term n) : map h ≫ W.inclusion = V.inclusion := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

end CochainSubmodules
end Sharpness
