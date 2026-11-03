import Sharpness.V29.MainCentralizer
import Sharpness.V29.MainCentralQuotient
import Sharpness.Unconditional.QuotientSaturationComplete
import Sharpness.CentralizerCentral
import Sharpness.Induction
import Sharpness.Unconditional.ScalarHigherLimits
import Sharpness.PrimeFieldMackey
import Sharpness.LocalReduction

/-! The manuscript-facing v2.9 route. Cardinal induction uses the new
composition-series reduction, trace-summand detection and vanishing. Both
arbitrary-value extensions use the actual filtered-direct-limit comparison. -/
set_option autoImplicit false
noncomputable section
universe u

namespace Sharpness.FusionSystem.V29
open CategoryTheory CategoryTheory.Limits

theorem primeField_sharpness (p : ℕ) [Fact p.Prime]
    {S : Type u} [Group S] [Finite S] (F : FusionSystem S)
    (hS : IsPGroup p S) (sat : F.Saturated p) :
    F.Sharp (R := PrimeField.{u} p) := by
  classical
  have induction : ∀ n : ℕ, ∀ (U : Type u) [Group U] [Finite U]
      (G : FusionSystem U) (hU : IsPGroup p U) (hG : G.Saturated p),
      Nat.card U = n → G.Sharp (R := PrimeField.{u} p) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro U _ _ G hU hG hn
      apply centralizer_sharpness_of_local G p hU hG
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
      have quotientSharp : Q.system.Sharp (R := PrimeField.{u} p) :=
        ih (Nat.card (T ⧸ Z)) smaller (T ⧸ Z) Q.system (hT.to_quotient Z)
          Q.quotient_saturated rfl
      exact central_quotient_sharpness C.system p hT C.AKO_I_5_5 hZ quotientSharp
  exact induction (Nat.card S) S F hS sat rfl

theorem prime_annihilated_mackey_acyclic (p : ℕ) [Fact p.Prime]
    {S : Type u} [Group S] [Finite S] (F : FusionSystem S)
    (hS : IsPGroup p S) (sat : F.Saturated p)
    (M : MackeyModule.{u,u,u} (PrimeLocalRing.{u} p) F.Orbit F.mackeyShape)
    (killed : ∀ P (x : M.Value P), (p : PrimeLocalRing.{u} p) • x = 0) :
    Acyclic (F.centricCoefficient M) := by
  let B := Unconditional.barCalculationInput p (PrimeField.{u} p)
  let N := M.primeFieldMackey p killed
  have fieldVanishing : Acyclic (F.centricCoefficient N) :=
    primeField_sharpness p F hS sat N
  have restricted := (B.scalar F.CentricOrbit).acyclic_restrict_of
    (F.centricCoefficient N)
    (B.comparison (PrimeLocalRing.{u} p) F.CentricOrbit)
    (B.comparison (PrimeField.{u} p) F.CentricOrbit) fieldVanishing
  have hn : Acyclic (F.centricCoefficient (N.restrictScalars (PrimeLocalRing.{u} p))) :=
    acyclic_of_iso (F.centricRestrictScalarsIso N) restricted
  exact acyclic_of_iso (F.centricCoefficientIso (M.primeFieldMackeyRestrictIso p killed)) hn

/-- The main theorem over the localized integers. The finite-value scalar
and Nakayama argument is retained; arbitrary values now pass through the
proved higher-limit/direct-limit comparison of Lemma 2.6(ii). -/
theorem primeLocal_sharpness (p : ℕ) [Fact p.Prime]
    {S : Type u} [Group S] [Finite S] (F : FusionSystem S)
    (hS : IsPGroup p S) (sat : F.Saturated p) :
    F.Sharp (R := PrimeLocalRing.{u} p) := by
  intro M n hn
  apply F.higherLimit_isZero_of_fg_subfunctors_v29 M n
  intro N hfg
  haveI (P : F.Orbit) : Module.Finite (PrimeLocalRing.{u} p)
      ((M.submodule N).Value P) := Module.Finite.of_fg (hfg P)
  let B := Unconditional.barCalculationInput p (PrimeField.{u} p)
  let bar := B.model (PrimeLocalRing.{u} p) F.CentricOrbit
  have exactN := F.finite_local_exact_of_killed_exact bar (p : PrimeLocalRing.{u} p)
    (fun A killed => (bar.acyclic_iff
      (B.comparison (PrimeLocalRing.{u} p) F.CentricOrbit) _).mp
      (prime_annihilated_mackey_acyclic p F hS sat A killed))
    (primeLocal_prime_mem_jacobson p) (M.submodule N)
  exact ((bar.acyclic_iff (B.comparison (PrimeLocalRing.{u} p) F.CentricOrbit) _).mpr
    exactN) n hn

theorem field_sharpness_of_primeLocal (p : ℕ) [Fact p.Prime]
    (k : Type u) [Field k] [CharP k p]
    {S : Type u} [Group S] [Finite S] (F : FusionSystem S)
    (hS : IsPGroup p S) (sat : F.Saturated p) : F.Sharp (R := k) := by
  intro M
  have hM := primeLocal_sharpness p F hS sat (M.restrictScalars (PrimeLocalRing.{u} p))
  have hrestricted : Acyclic
      (F.centricCoefficient M ⋙ ModuleCat.restrictScalars
        (algebraMap (PrimeLocalRing.{u} p) k)) :=
    acyclic_of_iso (F.centricRestrictScalarsIso M).symm hM
  intro n hn
  have hz : IsZero ((ModuleCat.restrictScalars
      (algebraMap (PrimeLocalRing.{u} p) k)).obj
        (higherLimit (F.centricCoefficient M) n)) :=
    IsZero.of_iso (hrestricted n hn)
      (Unconditional.scalarHigherLimitIso (R := PrimeLocalRing.{u} p)
        (F.centricCoefficient M) n)
  exact (ModuleCat.isZero_iff_subsingleton (R := k)).mpr
    ((ModuleCat.isZero_iff_subsingleton (R := PrimeLocalRing.{u} p)).mp hz)

theorem diaz_park_conjecture (p : ℕ) [Fact p.Prime]
    {S : Type u} [Group S] [Finite S] (F : FusionSystem S)
    (hS : IsPGroup p S) (sat : F.Saturated p)
    (M : MackeyModule.{u,u,u} (PrimeField.{u} p) F.Orbit F.mackeyShape)
    [∀ P, FiniteDimensional (PrimeField.{u} p) (M.Value P)] :
    Acyclic (F.centricCoefficient M) :=
  field_sharpness_of_primeLocal p (PrimeField.{u} p) F hS sat M

end Sharpness.FusionSystem.V29
