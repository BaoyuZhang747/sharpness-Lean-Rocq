import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-! Differential comparison through an actual degreewise epimorphism,
proved before instantiating the complexes to a concrete totalization. -/
set_option autoImplicit false
universe u v
namespace Sharpness
open CategoryTheory
variable {C : Type u} [Category.{v} C] [Abelian C]
    {V W : CochainComplex C ℕ} (π : V ⟶ W) (n m : ℕ)
    {X Y : C} (a : W.X n ⟶ X) (b : W.X m ⟶ Y) (d : X ⟶ Y)
    (f : V.X n ⟶ X) (g : V.X m ⟶ Y) [Epi (π.f n)]

theorem cochain_d_through_epi (ha : π.f n ≫ a = f) (hb : π.f m ≫ b = g)
    (hd : V.d n m ≫ g = f ≫ d) : W.d n m ≫ b = a ≫ d := by
  apply (cancel_epi (π.f n)).mp
  calc
    _ = (π.f n ≫ W.d n m) ≫ b := (Category.assoc _ _ _).symm
    _ = (V.d n m ≫ π.f m) ≫ b := congrArg (fun h => h ≫ b) (π.comm n m)
    _ = V.d n m ≫ (π.f m ≫ b) := Category.assoc _ _ _
    _ = V.d n m ≫ g := congrArg (fun h => V.d n m ≫ h) hb
    _ = f ≫ d := hd
    _ = (π.f n ≫ a) ≫ d := congrArg (fun h => h ≫ d) ha.symm
    _ = _ := Category.assoc _ _ _

end Sharpness
