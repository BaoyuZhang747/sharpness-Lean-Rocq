import Sharpness.Unconditional.RealizationNerveHomotopyNaturality
import Sharpness.Unconditional.NerveNaturalTransformation

/-! Actual geometric realization preserves simplicial homotopies. In particular,
every natural transformation induces a homotopy of realized category nerves.
The construction uses finite closed simplex prisms and compact-open descent. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v

namespace Sharpness
open CategoryTheory Simplicial Opposite

/-- Realize an actual simplicial homotopy as an actual continuous homotopy.
No preservation of arbitrary products is assumed. -/
def realizationHomotopy {X Y : SSet.{u}} {f g : X ⟶ Y} (H : SSet.Homotopy f g) :
    TopCat.Homotopy (SSet.toTop.map f) (SSet.toTop.map g) :=
  realizationHomotopyOfSimplexHomotopies
    (fun n x => RealizationPrism.simplexRealizationHomotopy H x)
    (by
      intro n m a x t z
      exact RealizationPrism.simplexRealizationPrism_naturality H a x t z)

/-- A natural transformation gives a homotopy between the geometric realizations
of the actual nerve maps, in arbitrary object and morphism universes. -/
def nerveRealizationHomotopy {C D : Type u} [Category.{v} C] [Category.{v} D]
    {T U : C ⥤ D} (α : T ⟶ U) :
    TopCat.Homotopy (SSet.toTop.map (nerveMap T)) (SSet.toTop.map (nerveMap U)) :=
  realizationHomotopy (nerveNaturalTransformationHomotopy α)

end Sharpness
