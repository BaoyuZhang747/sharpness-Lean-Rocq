import Sharpness.Unconditional.CentralizerSaturationNormalized
import Sharpness.Unconditional.CentralizerSaturationSylow

/-! Saturation of the actual centralizer fusion system at a fully centralized
elementary abelian subgroup, proving AKO I.5.5 in the required case. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem
variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)

theorem centralizerSystem_saturated (p : ℕ) [Fact p.Prime]
    (hS : IsPGroup p S) (sat : F.Saturated p) (E : F.ElementaryCategory p) :
    (F.centralizerSystem p E).Saturated p where
  fully_normalized P hP := by
    have hPK := F.centralizerSystem_fullyKNormalized p sat E P hP
    have hJ := (F.fullyKNormalized_properties p hS sat _ _ hPK).1
    have hrec := F.centralizerSystem_receptive_of_join_fullyCentralized p sat E P hJ
    exact ⟨Receptive.fullyCentralized _ hrec,
      F.centralizer_sylow_of_fullyKNormalized p hS sat E P hPK⟩
  extension e he hQ := by
    obtain ⟨f, hf, hfe⟩ := F.centralizerSystem_receptive_of_fullyCentralized p sat E _ hQ _ e he
    exact ⟨(F.centralizerSystem p E).extensionDomainSubgroup e,
      (F.centralizerSystem p E).le_extensionDomainSubgroup e, rfl, f, hf, hfe⟩

/-- The previously external centralizer package, now constructed from the
ambient fusion-system axioms and its actual saturation proof. -/
def akoCentralizerInput (p : ℕ) [Fact p.Prime]
    (hS : IsPGroup p S) (sat : F.Saturated p) (E : F.ElementaryCategory p) :
    F.AKOCentralizerInput p hS sat E where
  system := F.centralizerSystem p E
  hom_iff := F.centralizerSystem_hom_iff p E
  AKO_I_5_5 := F.centralizerSystem_saturated p hS sat E

end Sharpness.FusionSystem
