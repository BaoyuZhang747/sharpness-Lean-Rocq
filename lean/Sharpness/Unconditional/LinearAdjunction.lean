import Sharpness.Unconditional.ExtAdjunction

set_option autoImplicit false
noncomputable section
universe u v w
namespace Sharpness
open CategoryTheory CategoryTheory.Limits

variable (R : Type u) [CommRing R]
    {C : Type v} [Category.{u} C] [Abelian C] [Linear R C]
    {D : Type w} [Category.{u} D] [Abelian D] [Linear R D]
    {L : C ⥤ D} {G : D ⥤ C}

set_option backward.isDefEq.respectTransparency false in
/-- The right adjoint of a linear functor is linear. -/
theorem rightAdjointLinear [L.Linear R] (adj : L ⊣ G) : G.Linear R where
  map_smul {X Y} f r := by
    apply (adj.homEquiv (G.obj X) Y).symm.injective
    simp [Adjunction.homEquiv_counit, Functor.map_smul]

end Sharpness
