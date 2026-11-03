import Sharpness.ExtEquivalence
import Mathlib.CategoryTheory.Adjunction.Additive

/-! Derived adjunction for the module-valued Ext used in this project.
The proof maps an actual projective resolution and compares its Hom complexes.
No comparison with a different definition of Ext is assumed. -/

set_option autoImplicit false
noncomputable section
universe u v w

namespace Sharpness
open CategoryTheory CategoryTheory.Limits Opposite

variable (R : Type u) [CommRing R]
    {C : Type v} [Category.{u} C] [Abelian C] [Linear R C]
    {D : Type w} [Category.{u} D] [Abelian D] [Linear R D]
    {L : C ⥤ D} {G : D ⥤ C} [L.Additive] [G.Additive] [G.Linear R]

set_option backward.isDefEq.respectTransparency false in
/-- The Hom equivalence of an adjunction is linear when its right adjoint is. -/
def adjunctionHomLinearEquiv (adj : L ⊣ G) (X : C) (Y : D) :
    (L.obj X ⟶ Y) ≃ₗ[R] (X ⟶ G.obj Y) :=
  { adj.homAddEquiv X Y with
    map_smul' := fun r f => by
      change adj.unit.app X ≫ G.map (r • f) = r • (adj.unit.app X ≫ G.map f)
      rw [Functor.map_smul, Linear.comp_smul] }

/-- Adjunction identifies the two complexes computing the derived Hom. -/
def adjunctionLinearYonedaComplexIso (adj : L ⊣ G) (P : ChainComplex C ℕ) (Y : D) :
    ChainComplex.linearYonedaObj ((L.mapHomologicalComplex (ComplexShape.down ℕ)).obj P) R Y ≅
      P.linearYonedaObj R (G.obj Y) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (adjunctionHomLinearEquiv R adj (P.X n) Y).toModuleIso)
    (by
      intro i j hij
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro f
      change P.d j i ≫ adj.homEquiv (P.X i) Y f =
        adj.homEquiv (P.X j) Y (L.map (P.d j i) ≫ f)
      exact (adj.homEquiv_naturality_left (P.d j i) f).symm)

/-- Exact left adjoints with epi-preserving right adjoints induce derived
adjunction isomorphisms in every degree for the project's actual Ext. -/
def extAdjunctionIso [EnoughProjectives C] [EnoughProjectives D]
    [L.PreservesHomology] [G.PreservesEpimorphisms]
    (adj : L ⊣ G) (X : C) (Y : D) (n : ℕ) :
    ((Ext R D n).obj (op (L.obj X))).obj Y ≅
      ((Ext R C n).obj (op X)).obj (G.obj Y) := by
  letI : L.PreservesProjectiveObjects :=
    Functor.preservesProjectiveObjects_of_adjunction_of_preservesEpimorphisms adj
  let P := projectiveResolution X
  let Q := L.mapProjectiveResolution P
  exact Q.isoExt (R := R) n Y ≪≫
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℕ) n).mapIso
      (adjunctionLinearYonedaComplexIso R adj P.complex Y) ≪≫
    (P.isoExt (R := R) n (G.obj Y)).symm

end Sharpness
