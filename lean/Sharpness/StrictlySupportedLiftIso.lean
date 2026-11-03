import Mathlib.Algebra.Homology.Embedding.HomEquiv

/-! A complex supported on an embedded shape is isomorphic to the
extension of any explicitly isomorphic restricted complex. Boundary
lifting and invertibility are proved from actual zero components. -/
set_option autoImplicit false
noncomputable section
universe u v t t'
namespace Sharpness
open CategoryTheory CategoryTheory.Limits
variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasZeroObject C]
    {ι : Type t} {ι' : Type t'} {c : ComplexShape ι} {c' : ComplexShape ι'}
    (e : c.Embedding c') [e.IsRelIff]
    (K : HomologicalComplex C c') [K.IsStrictlySupported e]
    (L : HomologicalComplex C c) (φ : K.restriction e ≅ L)

theorem strictlySupported_hasLift : e.HasLift φ.hom := by
  intro j hj i hi
  exact (K.isZero_X_of_isStrictlySupported e i (hj.notMem hi)).eq_of_src _ _

def strictlySupportedLiftIso : K ≅ L.extend e := by
  let g := e.liftExtend φ.hom (strictlySupported_hasLift e K L φ)
  letI : ∀ i, IsIso (g.f i) := by
    intro i
    by_cases hi : ∃ j, e.f j = i
    · obtain ⟨j, hj⟩ := hi
      exact (e.isIso_liftExtend_f_iff φ.hom (strictlySupported_hasLift e K L φ) hj).mpr
        inferInstance
    · exact isIso_of_source_target_iso_zero _
        (K.isZero_X_of_isStrictlySupported e i (fun j hj => hi ⟨j, hj⟩)).isoZero
        (L.isZero_extend_X e i (fun j hj => hi ⟨j, hj⟩)).isoZero
  letI : IsIso g := HomologicalComplex.Hom.isIso_of_components g
  exact asIso g

end Sharpness
