import Sharpness.Unconditional.AtomicGroupOrbit
import Sharpness.Unconditional.ExtAdjunction
import Sharpness.Unconditional.ProjectiveCoefficients
import Sharpness.HigherLimitFunctor
import Mathlib.CategoryTheory.Adjunction.Opposites
import Mathlib.CategoryTheory.Adjunction.Whiskering
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-!
Derived-limit comparison for a right-adjoint inclusion, and the resulting
normal-p-subgroup vanishing for atomic coefficients on the ordinary group
orbit category. The derived comparison uses projective resolutions of the
constant diagram and the project's actual module-valued Ext.
-/
set_option autoImplicit false
noncomputable section
universe u

namespace Sharpness
open CategoryTheory CategoryTheory.Limits Opposite

variable (R : Type u) [CommRing R]
    {C D : Type u} [Category.{u} C] [Category.{u} D]

/-- Restriction along a right adjoint preserves all higher inverse limits
of contravariant module-valued diagrams. -/
def higherLimitRightAdjointIso (r : C ⥤ D) (i : D ⥤ C) (adj : r ⊣ i)
    (M : CoefficientCategory R C) (n : ℕ) :
    higherLimit M n ≅ higherLimit (i.op ⋙ M) n := by
  let L := restrictionCoefficientFunctor R r
  let G := restrictionCoefficientFunctor R i
  haveI : L.PreservesHomology := by
    dsimp [L, restrictionCoefficientFunctor]
    infer_instance
  haveI : G.PreservesEpimorphisms := by
    dsimp [G, restrictionCoefficientFunctor]
    infer_instance
  exact extAdjunctionIso R (L := L) (G := G)
    (adj.op.whiskerLeft (ModuleCat.{u} R)) (constantCoefficient R D) M n

/-- Every degree of the derived inverse limit of a zero coefficient is zero. -/
theorem higherLimit_isZero_of_isZero (M : CoefficientCategory R C) (hM : IsZero M)
    (n : ℕ) : IsZero (higherLimit M n) := by
  let P := projectiveResolution (constantCoefficient R C)
  apply IsZero.of_iso _ (P.isoExt (R := R) n M)
  apply HomologicalComplex.ExactAt.isZero_homology
  apply HomologicalComplex.ExactAt.of_isZero
  change IsZero (ModuleCat.of R (P.complex.X n ⟶ M))
  letI : Subsingleton (P.complex.X n ⟶ M) := ⟨fun f g => hM.eq_of_tgt f g⟩
  exact ModuleCat.isZero_of_subsingleton _

namespace AtomicGroupOrbit

variable {p : ℕ} {G : Type u} [Group G]
    (N : Subgroup G) [N.Normal] (hN : IsPGroup p N)

include hN

/-- An atomic coefficient supported at the trivial subgroup has zero
higher limits, in every degree, if the group has a nontrivial normal
p-subgroup. The coefficient ring can be any commutative ring. -/
theorem atomic_higherLimits_zero (hne : N ≠ ⊥)
    (M : CoefficientCategory R (Orbit (p := p) (G := G)))
    (supported : ∀ P : Orbit (p := p) (G := G), P.as.subgroup ≠ ⊥ → IsZero (M.obj (op P)))
    (n : ℕ) : IsZero (higherLimit M n) := by
  let i := overgroupInclusion (p := p) N
  have hres : IsZero (i.op ⋙ M) := by
    apply Functor.isZero
    intro P
    exact supported P.unop.obj (fun h => hne (bot_unique (h ▸ P.unop.property)))
  exact IsZero.of_iso (higherLimit_isZero_of_isZero R (i.op ⋙ M) hres n)
    (higherLimitRightAdjointIso R (reflector N hN) i (reflectorAdjunction N hN) M n)

end AtomicGroupOrbit
end Sharpness
