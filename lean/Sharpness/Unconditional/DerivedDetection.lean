import Sharpness.Unconditional.ExtAdjunction
import Sharpness.Unconditional.InjectiveExt
import Sharpness.Unconditional.InjectiveContractible
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves

/-! Detection of Ext vanishing through a right adjoint. The input is acyclicity
of the right adjoint applied to an actual injective resolution. The conclusion
uses the original module-valued Ext. This is the homological part of the
centralizer-cover argument, independent of fusion systems. -/

set_option autoImplicit false
noncomputable section
universe u v w

namespace Sharpness
open CategoryTheory CategoryTheory.Limits Opposite

variable (R : Type u) [CommRing R]
    {C : Type v} [Category.{u} C] [Abelian C] [Linear R C]
    {D : Type w} [Category.{u} D] [Abelian D] [Linear R D]
    {L : C ⥤ D} {G : D ⥤ C} [L.Additive] [G.Additive] [G.Linear R]

/-- Adjunction identifies the complexes of morphisms into a cochain complex. -/
def adjunctionLinearCoyonedaComplexIso (adj : L ⊣ G) (X : C) (I : CochainComplex D ℕ) :
    (((linearCoyoneda R D).obj (op (L.obj X))).mapHomologicalComplex _).obj I ≅
      (((linearCoyoneda R C).obj (op X)).mapHomologicalComplex _).obj
        ((G.mapHomologicalComplex _).obj I) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (adjunctionHomLinearEquiv R adj X (I.X n)).toModuleIso)
    (by
      intro i j hij
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro f
      change adj.homEquiv X (I.X i) f ≫ G.map (I.d i j) =
        adj.homEquiv X (I.X j) (f ≫ I.d i j)
      exact (adj.homEquiv_naturality_right f (I.d i j)).symm)

/-- If an exact left adjoint has a right adjoint whose derived value at `Y`
is zero, all Ext groups from an object in the image of the left adjoint vanish.
Only preservation of monomorphisms by the left adjoint is needed here. -/
theorem ext_isZero_of_rightAdjoint_acyclic
    [EnoughProjectives D] [EnoughInjectives D] [L.PreservesMonomorphisms]
    (adj : L ⊣ G) (X : C) (Y : D) (I : InjectiveResolution Y)
    (hI : ∀ n, ((G.mapHomologicalComplex _).obj I.cocomplex).ExactAt n) (n : ℕ) :
    IsZero (((Ext R D n).obj (op (L.obj X))).obj Y) := by
  letI : G.PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms adj
  letI : ∀ n, Injective (((G.mapHomologicalComplex _).obj I.cocomplex).X n) :=
    fun n => G.injective_obj (I.cocomplex.X n)
  apply (ext_isZero_iff_injectiveHom_exactAt R (L.obj X) Y I n).mpr
  have h := map_acyclic_injective_exactAt ((linearCoyoneda R C).obj (op X))
    ((G.mapHomologicalComplex _).obj I.cocomplex) hI n
  exact h.of_iso (adjunctionLinearCoyonedaComplexIso R adj X I.cocomplex).symm

end Sharpness
