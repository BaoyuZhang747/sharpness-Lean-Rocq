import Sharpness.ChainDualFunctor
import Sharpness.SingularCohomologyHomotopy
import Mathlib.Algebra.Homology.QuasiIso

/-! The actual chain-dual map preserves homotopies and reverses
homotopy equivalences, for every coefficient module A. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.SingularCohomology
open CategoryTheory
variable (R : Type u) [CommRing R] (A : ModuleCat.{u} R)
    {K L : ChainComplex (ModuleCat.{u} R) ℕ}

def chainDualHomotopy {f g : K ⟶ L} (H : Homotopy f g) :
    Homotopy (chainDualMap R f A) (chainDualMap R g A) :=
  ((((linearYoneda R (ModuleCat.{u} R)).obj A).rightOp).mapHomotopy H).unop

def chainDualHomotopyEquiv (e : HomotopyEquiv K L) :
    HomotopyEquiv (L.linearYonedaObj R A) (K.linearYonedaObj R A) where
  hom := chainDualMap R e.hom A
  inv := chainDualMap R e.inv A
  homotopyHomInvId := by
    rw [← chainDualMap_comp, ← chainDualMap_id]
    exact chainDualHomotopy R A e.homotopyInvHomId
  homotopyInvHomId := by
    rw [← chainDualMap_comp, ← chainDualMap_id]
    exact chainDualHomotopy R A e.homotopyHomInvId

theorem chainDualHomotopyEquiv_hom (e : HomotopyEquiv K L) :
    (chainDualHomotopyEquiv R A e).hom = chainDualMap R e.hom A := rfl

theorem chainDualHomotopyEquiv_inv (e : HomotopyEquiv K L) :
    (chainDualHomotopyEquiv R A e).inv = chainDualMap R e.inv A := rfl

end Sharpness.SingularCohomology
