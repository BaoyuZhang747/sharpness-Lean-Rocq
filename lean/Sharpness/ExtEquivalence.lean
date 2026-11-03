import Sharpness.HigherLimits
import Mathlib.CategoryTheory.Preadditive.Projective.Preserves
import Mathlib.Algebra.Homology.Linear

/-! Ext invariance under a linear equivalence, proved by mapping an actual
projective resolution and comparing its native linear-Yoneda complexes.
This is a proof, not an additional literature-comparison input. -/
set_option autoImplicit false
noncomputable section
universe u v w
namespace Sharpness
open CategoryTheory CategoryTheory.Limits Opposite
variable (R : Type u) [CommRing R]
    {C : Type v} [Category.{u} C] [Abelian C] [CategoryTheory.Linear R C]
    {D : Type w} [Category.{u} D] [Abelian D] [CategoryTheory.Linear R D]

def fullyFaithfulHomLinearEquiv (F : C ⥤ D) [F.Full] [F.Faithful]
    [F.Additive] [F.Linear R] (X Y : C) : (X ⟶ Y) ≃ₗ[R] (F.obj X ⟶ F.obj Y) :=
  LinearEquiv.ofBijective (F.mapLinearMap R) ⟨F.map_injective, F.map_surjective⟩

def linearYonedaComplexIso (F : C ⥤ D) [F.Full] [F.Faithful]
    [F.Additive] [F.Linear R] (P : ChainComplex C ℕ) (Y : C) :
    P.linearYonedaObj R Y ≅
      ChainComplex.linearYonedaObj ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P) R (F.obj Y) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (fullyFaithfulHomLinearEquiv R F (P.X n) Y).toModuleIso)
    (by
      intro i j hij
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro f
      change F.map (P.d j i) ≫ F.map f = F.map (P.d j i ≫ f)
      exact (F.map_comp _ _).symm)

variable [EnoughProjectives C] [EnoughProjectives D]

def extEquivalenceIso (e : C ≌ D) [e.functor.Additive] [e.functor.Linear R]
    (X Y : C) (n : ℕ) :
    ((Ext R C n).obj (op X)).obj Y ≅
      ((Ext R D n).obj (op (e.functor.obj X))).obj (e.functor.obj Y) := by
  let P := projectiveResolution X
  let Q := e.functor.mapProjectiveResolution P
  exact P.isoExt (R := R) n Y ≪≫
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℕ) n).mapIso
      (linearYonedaComplexIso R e.functor P.complex Y) ≪≫
    (Q.isoExt (R := R) n (e.functor.obj Y)).symm

end Sharpness
