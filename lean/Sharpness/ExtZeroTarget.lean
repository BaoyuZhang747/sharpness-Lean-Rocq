import Sharpness.HigherLimits

/-! Zero targets have zero actual mathlib Ext in every degree, computed
using a projective resolution. This includes degree zero and applies to
covariant coefficient categories as well as contravariant ones. -/
set_option autoImplicit false
noncomputable section
universe u v
namespace Sharpness
open CategoryTheory CategoryTheory.Limits Opposite
variable (R : Type u) [CommRing R]
    {C : Type v} [Category.{u} C] [Abelian C] [Linear R C] [EnoughProjectives C]

theorem ext_zero_of_isZero_target (X Y : C) (zero : IsZero Y) (n : ℕ) :
    IsZero (((Ext R C n).obj (op X)).obj Y) := by
  let P := CategoryTheory.projectiveResolution X
  have hmid : IsZero ((P.complex.linearYonedaObj R Y).X n) := by
    apply ModuleCat.isZero_iff_subsingleton.mpr
    apply subsingleton_of_forall_eq 0
    intro f
    exact zero.eq_of_tgt _ _
  exact IsZero.of_iso (HomologicalComplex.ExactAt.of_isZero hmid).isZero_homology (P.isoExt n Y)

variable {J : Type u} [Category.{u} J]

theorem functor_isZero_of_values_zero (D : J ⥤ ModuleCat.{u} R)
    (zero : ∀ X, IsZero (D.obj X)) : IsZero D := by
  rw [IsZero.iff_id_eq_zero]
  apply NatTrans.ext
  funext X
  exact (zero X).eq_of_tgt _ _

/-- Covariant higher limits, as required in Yalcin Remark 3.2 and Theorem
9.4. The functor category has the stated variance, without reversing J. -/
def covariantHigherLimit [EnoughProjectives (J ⥤ ModuleCat.{u} R)]
    (D : J ⥤ ModuleCat.{u} R) (n : ℕ) : ModuleCat.{u} R :=
  ((Ext R (J ⥤ ModuleCat.{u} R) n).obj
    (op ((Functor.const J).obj (ModuleCat.of R R)))).obj D

theorem covariantHigherLimit_zero_of_values_zero
    [EnoughProjectives (J ⥤ ModuleCat.{u} R)]
    (D : J ⥤ ModuleCat.{u} R) (zero : ∀ X, IsZero (D.obj X)) (n : ℕ) :
    IsZero (covariantHigherLimit R D n) :=
  ext_zero_of_isZero_target R _ D (functor_isZero_of_values_zero R D zero) n

end Sharpness
