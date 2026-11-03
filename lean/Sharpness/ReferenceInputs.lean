import Sharpness.HigherLimits
import Sharpness.CentricStable
import Sharpness.FusionMinimal

/-!
Published results used as explicit inputs, in accordance with the user's
instruction not to formalize their proofs. The fields below do not include
the manuscript's central-quotient theorem, criterion, or general sharpness.
-/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory CategoryTheory.Limits

namespace MackeyModule
variable {R : Type u} [Ring R] {C : Type u} [Category.{u} C]
    {B : MackeyShape C} (M : MackeyModule.{u,u,u} R C B)

def automorphismAction (P : C) : Aut P →* Module.End R (M.Value P) where
  toFun a := M.push a.hom
  map_one' := M.push_id P
  map_mul' a b := M.push_comp b.hom a.hom

end MackeyModule

namespace FusionSystem
variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)

def topOrbit : F.Orbit := F.toOrbit.obj ⟨⊤⟩

def toTop (P : F.Orbit) : P ⟶ F.topOrbit := F.toOrbit.map (F.inclusion le_top)

theorem toTop_top : F.toTop F.topOrbit = 𝟙 F.topOrbit := by
  change F.toOrbit.map (F.inclusion (show (⊤ : Subgroup S) ≤ ⊤ from le_refl _)) = _
  have h : F.inclusion (show (⊤ : Subgroup S) ≤ ⊤ from le_refl _) =
      𝟙 (⟨⊤⟩ : F.Object) := by
    apply Subtype.ext
    ext x
    rfl
  rw [h, F.toOrbit.map_id]
  rfl

theorem top_centric : F.IsCentric ⊤ := by
  intro P _ e _
  have hcard : Nat.card P = Nat.card S :=
    (Nat.card_congr e.toEquiv).symm.trans Subgroup.card_top
  have hP := P.eq_top_of_card_eq hcard
  rw [hP]
  exact le_top

abbrev centricProperty : ObjectProperty F.Orbit := fun P => F.IsCentric P.as.subgroup

variable {k : Type u} [Field k]

/-- The minimal label and simple automorphism module supplied by
DP Propositions 3.1--3.2. There is no higher-limit conclusion in this record. -/
structure SimpleLabel (M : MackeyModule.{u,u,u} k F.Orbit F.mackeyShape) where
  Q : F.Orbit
  simple : M.IsSimple
  nonzero : ∃ x : M.Value Q, x ≠ 0
  small_zero : ∀ P, F.orbitOrder P < F.orbitOrder Q → ∀ x : M.Value P, x = 0
  simple_at_Q : ∀ A : Submodule k (M.Value Q),
    (∀ g : Aut Q, ∀ x ∈ A, M.automorphismAction Q g x ∈ A) → A = ⊥ ∨ A = ⊤

variable [EnoughProjectives (CoefficientCategory k F.CentricOrbit)]

/-- The cited DP classification and support inputs. -/
structure DiazParkInputs where
  propositions_3_1_3_2 : ∀ M : MackeyModule.{u,u,u} k F.Orbit F.mackeyShape,
    M.IsSimple → Nonempty (F.SimpleLabel M)
  proposition_3_3 : ∀ (M : MackeyModule.{u,u,u} k F.Orbit F.mackeyShape)
    (label : F.SimpleLabel M), F.IsCentric label.Q.as.subgroup →
      ∀ P, ¬ F.IsCentric P.as.subgroup → ∀ x : M.Value P, x = 0

/-- The supported-coefficient bridge, packaged separately from literature
inputs. `CentricSimple.supportedCentricBridge` constructs this package by
proving the truncated formula and scalar comparison and applying the exact
Z_(p)-valued DP Theorem A. This is an internally proved result, not an
accepted bibliography input. -/
structure SupportedCentricBridge where
  acyclic_of_supported : ∀ M : MackeyModule.{u,u,u} k F.Orbit F.mackeyShape,
    (∀ P, ¬ F.IsCentric P.as.subgroup → ∀ x : M.Value P, x = 0) →
      Acyclic (F.centricCoefficient M)

/-- Internal assembly for Proposition 2.3. The bridge is constructed in
`CentricSimple`; the public endpoint there takes only the stated references. -/
theorem centric_simple_acyclic (DP : F.DiazParkInputs (k := k))
    (bridge : F.SupportedCentricBridge (k := k))
    (M : MackeyModule.{u,u,u} k F.Orbit F.mackeyShape) (label : F.SimpleLabel M)
    (centric : F.IsCentric label.Q.as.subgroup) : Acyclic (F.centricCoefficient M) :=
  bridge.acyclic_of_supported M (DP.proposition_3_3 M label centric)

/-- BLO Theorem A.10, as the factorization data actually used by this paper.
Only arrows and their generation are asserted; no stable-element result is
assumed. Inclusions are handled by the concrete image factorization. -/
structure AlperinInput where
  theorem_A_10 : ∀ {P Q : F.Orbit} (f : P ⟶ Q),
    AlperinGenerated F.centricProperty F.topOrbit F.toTop f

/-- The degree-zero bar/Ext identification from AKO III.5.3.
This is about arbitrary coefficients, not about stable elements. -/
structure DegreeZeroInput where
  AKO_III_5_3 : ∀ M : MackeyModule.{u,u,u} k F.Orbit F.mackeyShape,
    higherLimit (F.centricCoefficient M) 0 ≅
      ModuleCat.of k (((F.coefficientData M).onFull F.centricProperty).limit)

/-- Manuscript Lemma 3.5 on the concrete fusion orbit category. Its stability
propagation is proved in `CentricStable`; the only generation input is BLO. -/
def stableElementsEquiv (BLO : F.AlperinInput)
    (M : MackeyModule.{u,u,u} k F.Orbit F.mackeyShape) :
    ((F.coefficientData M).onFull F.centricProperty).limit ≃ₗ[k]
      (F.coefficientData M).arrowStable F.topOrbit F.toTop :=
  (F.coefficientData M).limitCentricEquivStable F.centricProperty F.topOrbit F.toTop
    F.top_centric F.toTop_top BLO.theorem_A_10

end FusionSystem
end Sharpness
