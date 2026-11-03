import Sharpness.DualNatBicomplex
import Sharpness.NativeCoproductDual
import Sharpness.NatTotalIndex

/-! The chosen finite coproducts in the native chain and cochain
totalizations give the canonical degreewise dual isomorphism. Its
inverse has the actual chain-total inclusions as evaluation maps.
Compatibility with the total differential is a separate theorem. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory CategoryTheory.Limits
variable {R : Type u} [CommRing R]
    (K : HomologicalComplex₂ (ModuleCat.{u} R) (ComplexShape.down ℕ) (ComplexShape.down ℕ))
    (A : ModuleCat.{u} R)

def chainTotalDegreeFamily (n : ℕ) : NatTotalIndex n → ModuleCat.{u} R :=
  fun z => (K.X z.val.1).X z.val.2

set_option backward.isDefEq.respectTransparency false in
def totalDualDegreeIso (n : ℕ) :
    ((dualNatBicomplex K A).total (ComplexShape.up ℕ)).X n ≅
      ModuleCat.of R ((K.total (ComplexShape.down ℕ)).X n ⟶ A) :=
  nativeFiniteCoproductDualIso (chainTotalDegreeFamily K n) A

def dualTotalDegreeProjection (n : ℕ) (z : NatTotalIndex n) :
    ((dualNatBicomplex K A).total (ComplexShape.up ℕ)).X n ⟶
      ModuleCat.of R ((K.X z.val.1).X z.val.2 ⟶ A) :=
  (nativeCoproductPiIso (fun w : NatTotalIndex n => ModuleCat.of R ((chainTotalDegreeFamily K n w) ⟶ A))).hom ≫
    ModuleCat.ofHom (LinearMap.proj z)

set_option backward.isDefEq.respectTransparency false in
theorem totalDualDegreeIso_inv_projection (n : ℕ) (z : NatTotalIndex n)
    (f : (K.total (ComplexShape.down ℕ)).X n ⟶ A) :
    dualTotalDegreeProjection K A n z ((totalDualDegreeIso K A n).inv f) =
      K.ιTotal (ComplexShape.down ℕ) z.val.1 z.val.2 n z.property ≫ f :=
  congrArg (fun a => a f) (nativeFiniteCoproductDualIso_inv_evaluation (chainTotalDegreeFamily K n) A z)

end Sharpness
