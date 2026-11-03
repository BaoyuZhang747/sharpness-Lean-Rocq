import Sharpness.Unconditional.QuotientSaturationExtension
import Sharpness.Unconditional.CentralizerSaturationReceptive
import Sharpness.Unconditional.SaturationCharacterization

/-! Saturation of the constructed central quotient and the unconditional
constructor for the existing AKO quotient interface. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem
open CategoryTheory
variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)
    {Z : Subgroup S} [Z.Normal] (hZ : F.CentralSubgroup Z)

theorem centralQuotient_receptive (p : ℕ) [Fact p.Prime]
    (hS : IsPGroup p S) (sat : F.Saturated p)
    (A : Subgroup (S ⧸ Z)) (hA : (F.centralQuotient hZ).FullyNormalized A) :
    (F.centralQuotient hZ).Receptive A := by
  intro B e he
  obtain ⟨N, hBN, hN, f, hf, hext⟩ :=
    F.centralQuotient_extension_fullyNormalized hZ p hS sat e he hA
  have hle : (F.centralQuotient hZ).extensionDomainSubgroup e ≤ N := by
    intro x hx
    rw [← SetLike.mem_coe, hN]
    exact hx
  exact ⟨f.comp (subgroupInclusion _ _ hle),
    (F.centralQuotient hZ).comp_mem _ _ ((F.centralQuotient hZ).inclusion_mem hle) hf,
    hext⟩

theorem centralQuotient_fullyCentralized (p : ℕ) [Fact p.Prime]
    (hS : IsPGroup p S) (sat : F.Saturated p)
    (A : Subgroup (S ⧸ Z)) (hA : (F.centralQuotient hZ).FullyNormalized A) :
    (F.centralQuotient hZ).FullyCentralized A :=
  (F.centralQuotient_receptive hZ p hS sat A hA).fullyCentralized

/-- A central quotient of a saturated fusion system is saturated. -/
theorem centralQuotient_saturated (p : ℕ) [Fact p.Prime]
    (hS : IsPGroup p S) (sat : F.Saturated p) :
    (F.centralQuotient hZ).Saturated p :=
  (F.centralQuotient hZ).saturated_of_fullyNormalized_sylow_receptive p
    (hS.to_quotient Z) (F.centralQuotient_sylow hZ p sat)
    (F.centralQuotient_receptive hZ p hS sat)

/-- AKO II.5.5 for central subgroups, proved from the fusion and saturation
axioms, with no additional mathematical input. -/
def akoQuotientInput (p : ℕ) [Fact p.Prime]
    (hS : IsPGroup p S) (sat : F.Saturated p) :
    F.AKOQuotientInput (p := p) hZ hS sat where
  system := F.centralQuotient hZ
  isHom_iff := F.centralQuotient_isHom_iff hZ
  quotient_saturated := F.centralQuotient_saturated hZ p hS sat

end Sharpness.FusionSystem
