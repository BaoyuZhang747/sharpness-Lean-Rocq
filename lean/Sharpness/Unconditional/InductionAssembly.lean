import Sharpness.Unconditional.CentralQuotientCriterion
import Sharpness.Unconditional.CentralizerDetectionCriterion
import Sharpness.Unconditional.QuotientSaturationComplete
import Sharpness.CentralizerCentral
import Sharpness.Induction

/-! Cardinal induction after constructing centralizer detection, central
quotients, and the bar resolution. This intermediate assembly isolates the
two mathematical lemmas: centric supported acyclicity and atomic vanishing
at nonradical objects. `Unconditional.MainTheorem` supplies their proofs. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem
open CategoryTheory CategoryTheory.Limits Opposite

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]

theorem sharpness_of_supported_and_atomic
    (supported : ∀ (U : Type u) [Group U] [Finite U] (G : FusionSystem U),
      IsPGroup p U → G.Saturated p → G.SupportedCentricBridge (k := k))
    (atomic : ∀ (U : Type u) [Group U] [Finite U] (G : FusionSystem U),
      IsPGroup p U → G.Saturated p →
      ∀ Q : G.CentricOrbit, ¬ G.IsRadical p Q.obj.as.subgroup →
        ∀ A : CoefficientCategory k G.CentricOrbit,
        (∀ P, ¬ Nonempty (P ≅ Q) → IsZero (A.obj (op P))) →
        ∀ n, IsZero (higherLimit A n))
    {S : Type u} [Group S] [Finite S] (F : FusionSystem S)
    (hS : IsPGroup p S) (sat : F.Saturated p) : F.Sharp (R := k) := by
  classical
  let B := Unconditional.barCalculationInput p k
  have induction : ∀ n : ℕ, ∀ (U : Type u) [Group U] [Finite U]
      (G : FusionSystem U) (hU : IsPGroup p U) (hG : G.Saturated p),
      Nat.card U = n → G.Sharp (R := k) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro U _ _ G hU hG hn
      apply G.centralizer_sharpness_of_local p hU hG (supported U G hU hG)
        (B.model k G.CentricOrbit) (B.comparison k G.CentricOrbit)
      intro E
      let T := G.centralizerGroup p E
      let C := G.akoCentralizerInput p hU hG E
      let Z := G.elementaryInCentralizer p E
      have hZ : C.system.CentralSubgroup Z := G.centralizer_central_subgroup p hU hG E C
      letI : Z.Normal := C.system.central_normal hZ
      let hT : IsPGroup p T := hU.to_subgroup T
      let Q := C.system.akoQuotientInput hZ p hT C.AKO_I_5_5
      haveI : Nontrivial Z := (Z.nontrivial_iff_ne_bot).mpr
        (G.elementaryInCentralizer_nontrivial p E)
      have hcardZ : 1 < Nat.card Z := by
        letI := Fintype.ofFinite Z
        simpa only [Nat.card_eq_fintype_card] using (Fintype.one_lt_card (α := Z))
      have smaller : Nat.card (T ⧸ Z) < n :=
        (quotient_card_lt_ambient U T Z hcardZ).trans_eq hn
      have quotientSharp : Q.system.Sharp (R := k) :=
        ih (Nat.card (T ⧸ Z)) smaller (T ⧸ Z) Q.system (hT.to_quotient Z)
          Q.quotient_saturated rfl
      exact C.system.central_quotient_sharpness_of_atomic hZ p hT C.AKO_I_5_5 Q
        (atomic T C.system hT C.AKO_I_5_5) quotientSharp
  exact induction (Nat.card S) S F hS sat rfl

end Sharpness.FusionSystem
