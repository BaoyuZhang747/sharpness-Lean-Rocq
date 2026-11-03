import Sharpness.ExtEquivalence

/-! Actual higher limits are invariant under equivalence of their indexing
categories. The comparison follows from the proved projective-resolution
Ext isomorphism and the linear equivalence of coefficient categories. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory CategoryTheory.Limits
variable (R : Type u) [CommRing R]
    {C D : Type u} [Category.{u} C] [Category.{u} D] (e : C ≌ D)

def coefficientEquivalence : CoefficientCategory R D ≌ CoefficientCategory R C :=
  (Equivalence.congrLeft e.op).symm

instance coefficientEquivalence_additive : (coefficientEquivalence R e).functor.Additive where
  map_add := by
    intro A B f g
    apply NatTrans.ext
    funext X
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl

instance coefficientEquivalence_linear : (coefficientEquivalence R e).functor.Linear R where
  map_smul := by
    intro A B f r
    apply NatTrans.ext
    funext X
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl

variable [EnoughProjectives (CoefficientCategory R C)]
    [EnoughProjectives (CoefficientCategory R D)]

def higherLimitEquivalenceIso (A : CoefficientCategory R D) (i : ℕ) :
    higherLimit A i ≅ higherLimit (e.functor.op ⋙ A) i :=
  extEquivalenceIso R (coefficientEquivalence R e) (constantCoefficient R D) A i

theorem acyclic_of_equivalence_pullback (A : CoefficientCategory R D)
    (h : Acyclic (e.functor.op ⋙ A)) : Acyclic A := by
  intro i hi
  exact IsZero.of_iso (h i hi) (higherLimitEquivalenceIso R e A i)

theorem acyclic_equivalence_pullback_of (A : CoefficientCategory R D)
    (h : Acyclic A) : Acyclic (e.functor.op ⋙ A) := by
  intro i hi
  exact IsZero.of_iso (h i hi) (higherLimitEquivalenceIso R e A i).symm

end Sharpness
