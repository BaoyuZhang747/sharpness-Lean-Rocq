import Sharpness.Unconditional.CentricTheoremA
import Sharpness.Unconditional.CentricReduction
import Sharpness.Unconditional.CentralQuotientSharpness

/-! The unconditional Díaz–Park sharpness theorem. All previously external
structural, category-cohomological and centric-acyclicity inputs are proved
within this import closure. The coefficient modules may have any dimension. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem
open CategoryTheory

/-- The Díaz–Park conjecture for every saturated fusion system on a finite
p-group, over every field of characteristic p and for all Mackey modules. -/
theorem saturated_fusion_sharpness_unconditional
    (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
    {S : Type u} [Group S] [Finite S] (F : FusionSystem S)
    (hS : IsPGroup p S) (sat : F.Saturated p) : F.Sharp (R := k) :=
  F.sharpness_of_centric_acyclicity p k
    (fun U _ _ G hU hG => G.provedDiazParkTheoremAInput p hU hG) hS sat

end Sharpness.FusionSystem
