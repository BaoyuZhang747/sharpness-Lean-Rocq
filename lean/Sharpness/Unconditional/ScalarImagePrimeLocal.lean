import Sharpness.Unconditional.ScalarImageHigherIso
import Sharpness.Unconditional.LocalSharpness

/-! The actual higher-limit isomorphism for `M → pM` over Z_(p),
with kernel acyclicity supplied by the unconditional characteristic-p
field theorem. The final prime-local sharpness theorem is not used. -/
set_option autoImplicit false
noncomputable section
universe u

namespace Sharpness.FusionSystem
open CategoryTheory

/-- The isomorphism asserted in the proof of manuscript `cor:local`,
for arbitrary Z_(p)-valued full Mackey functors and the actual map `M → pM`. -/
theorem prime_scalarToImage_higherLimit_isIso
    (p : ℕ) [Fact p.Prime] {S : Type u} [Group S] [Finite S]
    (F : FusionSystem S) (hS : IsPGroup p S) (sat : F.Saturated p)
    (M : MackeyModule.{u,u,u} (PrimeLocalRing.{u} p) F.Orbit F.mackeyShape)
    (i : ℕ) (hi : 0 < i) :
    IsIso ((higherLimitFunctor (PrimeLocalRing.{u} p) F.CentricOrbit i).map
      (F.centricCoefficientMap (M.scalarToImage (p : PrimeLocalRing.{u} p)))) := by
  apply F.scalarToImage_higherLimit_isIso M (p : PrimeLocalRing.{u} p) _ i hi
  exact F.prime_annihilated_mackey_acyclic_unconditional p hS sat
    (M.submodule (M.scalarKernel (p : PrimeLocalRing.{u} p)))
    (M.scalarKernel_killed (p : PrimeLocalRing.{u} p))

end Sharpness.FusionSystem
