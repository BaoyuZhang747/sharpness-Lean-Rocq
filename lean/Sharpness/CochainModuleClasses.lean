import Sharpness.ModuleHomologyClass
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-! Native cohomology as the explicit quotient of closed cochains by
boundaries, with a fixed degree-zero convention. The comparison is
induced by the identity middle map of the actual short complexes. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory
variable {R : Type u} [CommRing R] (K : CochainComplex (ModuleCat.{u} R) ℕ)

theorem cochain_prev_nat (n : ℕ) : (ComplexShape.up ℕ).prev n = n-1 := by
  cases n with
  | zero => exact CochainComplex.prev_nat_zero
  | succ n => exact CochainComplex.prev_nat_succ n

abbrev cochainKernel (n : ℕ) := (K.d n (n+1)).hom.ker
abbrev cochainShort (n : ℕ) := K.sc' (n-1) n (n+1)
abbrev cochainBoundaries (n : ℕ) : Submodule R (cochainKernel K n) :=
  LinearMap.range (cochainShort K n).moduleCatToCycles

def cochainClassIso (n : ℕ) :
    K.homology n ≅ ModuleCat.of R (cochainKernel K n ⧸ cochainBoundaries K n) :=
  ShortComplex.homologyMapIso
      (K.isoSc' (n-1) n (n+1) (cochain_prev_nat n) (CochainComplex.next ℕ n)) ≪≫
    (cochainShort K n).moduleCatHomologyIso

def cochainClass (n : ℕ) : ModuleCat.of R (cochainKernel K n) ⟶ K.homology n :=
  ModuleCat.ofHom (cochainBoundaries K n).mkQ ≫ (cochainClassIso K n).inv

theorem cochainClass_surjective (n : ℕ) : Function.Surjective (cochainClass K n) := by
  intro y
  obtain ⟨x, hx⟩ := (cochainBoundaries K n).mkQ_surjective ((cochainClassIso K n).hom y)
  refine ⟨x, ?_⟩
  change (cochainClassIso K n).inv ((cochainBoundaries K n).mkQ x) = y
  rw [hx]
  exact (cochainClassIso K n).toLinearEquiv.symm_apply_apply y

theorem cochainClass_eq_zero_iff (n : ℕ) (x : cochainKernel K n) :
    cochainClass K n x = 0 ↔ x ∈ cochainBoundaries K n := by
  change (cochainClassIso K n).inv ((cochainBoundaries K n).mkQ x) = 0 ↔ _
  rw [← (cochainClassIso K n).inv.hom.map_zero]
  change (cochainClassIso K n).toLinearEquiv.symm ((cochainBoundaries K n).mkQ x) =
    (cochainClassIso K n).toLinearEquiv.symm 0 ↔ _
  exact (cochainClassIso K n).toLinearEquiv.symm.injective.eq_iff.trans
    (Submodule.Quotient.mk_eq_zero (cochainBoundaries K n))

theorem cochainClass_boundary (n : ℕ) (x : K.X (n-1)) :
    cochainClass K n ((cochainShort K n).moduleCatToCycles x) = 0 := by
  apply (cochainClass_eq_zero_iff K n _).mpr
  exact ⟨x, rfl⟩

end Sharpness
