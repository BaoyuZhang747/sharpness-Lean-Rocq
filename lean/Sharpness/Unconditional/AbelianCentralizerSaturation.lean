import Sharpness.Unconditional.AbelianCentralizerNormalized
import Sharpness.Unconditional.AbelianCentralizerSylow
import Sharpness.Unconditional.SaturationCharacterization

/-! Saturation of the actual centralizer at every fully centralized abelian
subgroup, including the trivial subgroup. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem
variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)

theorem abelianCentralizerSystem_saturated (p : ℕ) [Fact p.Prime]
    (hS : IsPGroup p S) (sat : F.Saturated p) (E : F.AbelianCentralizerData)
    (hE : F.FullyCentralized E.subgroup) :
    (F.abelianCentralizerSystem E).Saturated p := by
  apply (F.abelianCentralizerSystem E).saturated_of_fullyNormalized_sylow_receptive
    p (hS.to_subgroup (F.abelianCentralizerGroup E))
  · intro P hP
    exact F.abelianCentralizer_sylow_of_fullyKNormalized p hS sat E P
      (F.abelianCentralizerSystem_fullyKNormalized p sat E hE P hP)
  · intro P hP
    have hPK := F.abelianCentralizerSystem_fullyKNormalized p sat E hE P hP
    have hJ := (F.fullyKNormalized_properties p hS sat _ _ hPK).1
    exact F.abelianCentralizerSystem_receptive_of_join_fullyCentralized p sat E P hJ

/-- Centralizer saturation at an arbitrary fully centralized abelian subgroup. -/
theorem centralizerOfAbelian_saturated (p : ℕ) [Fact p.Prime]
    (hS : IsPGroup p S) (sat : F.Saturated p) (E : Subgroup S)
    (hab : ∀ x y : E, x * y = y * x) (hE : F.FullyCentralized E) :
    (F.centralizerOfAbelian E hab).Saturated p :=
  F.abelianCentralizerSystem_saturated p hS sat ⟨E, hab⟩ hE

/-- The full conclusion of manuscript `lem:centralizer-saturated`. -/
theorem centralizerOfAbelian_saturated_and_central (p : ℕ) [Fact p.Prime]
    (hS : IsPGroup p S) (sat : F.Saturated p) (E : Subgroup S)
    (hab : ∀ x y : E, x * y = y * x) (hE : F.FullyCentralized E) :
    (F.centralizerOfAbelian E hab).Saturated p ∧
      (F.centralizerOfAbelian E hab).CentralSubgroup
        (E.subgroupOf (Subgroup.centralizer (E : Set S))) :=
  ⟨F.centralizerOfAbelian_saturated p hS sat E hab hE,
    F.centralizerOfAbelian_central E hab⟩

end Sharpness.FusionSystem
