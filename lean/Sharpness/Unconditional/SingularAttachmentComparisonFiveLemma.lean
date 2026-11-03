import Sharpness.Unconditional.SingularChainExcisionRelative

/-! The native middle-map comparison for short exact sequences of chain
complexes. This supplies the algebraic induction step for cell attachments. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
universe v u

namespace Sharpness.SingularAttachmentComparison
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence

variable {C : Type u} [Category.{v} C] [Abelian C]
  {S T : ShortComplex (ChainComplex C ℕ)}

/-- The missing middle position of the native long-exact-sequence comparison. -/
theorem shortExact_middle_quasiIso (φ : S ⟶ T) (hS : S.ShortExact) (hT : T.ShortExact)
    [QuasiIso φ.τ₁] [QuasiIso φ.τ₃] : QuasiIso φ.τ₂ := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  haveI : Mono (homologyMap φ.τ₂ n) := by
    apply Abelian.mono_of_epi_of_mono_of_mono
      ((δ₀Functor ⋙ δ₀Functor).map (mapComposableArrows₅ φ hS hT (n + 1) n rfl))
    · exact (composableArrows₅_exact hS (n + 1) n rfl).δ₀.δ₀
    · exact (composableArrows₅_exact hT (n + 1) n rfl).δ₀.δ₀
    · change Epi (homologyMap φ.τ₃ (n + 1)); infer_instance
    · change Mono (homologyMap φ.τ₁ n); infer_instance
    · change Mono (homologyMap φ.τ₃ n); infer_instance
  haveI : Epi (homologyMap φ.τ₂ n) := by
    cases n with
    | zero =>
      apply Abelian.epi_of_epi_of_epi_of_epi (mapComposableArrows₂ φ 0)
        (composableArrows₂_exact hT 0)
      · dsimp
        haveI := hS.epi_g
        apply epi_homologyMap_of_epi_of_not_rel
        intro j hj
        change j + 1 = 0 at hj
        omega
      · change Epi (homologyMap φ.τ₁ 0); infer_instance
      · change Epi (homologyMap φ.τ₃ 0); infer_instance
    | succ n =>
      apply Abelian.epi_of_epi_of_epi_of_mono
        ((δlastFunctor ⋙ δlastFunctor).map (mapComposableArrows₅ φ hS hT (n + 1) n rfl))
      · exact (composableArrows₅_exact hS (n + 1) n rfl).δlast.δlast
      · exact (composableArrows₅_exact hT (n + 1) n rfl).δlast.δlast
      · change Epi (homologyMap φ.τ₁ (n + 1)); infer_instance
      · change Epi (homologyMap φ.τ₃ (n + 1)); infer_instance
      · change Mono (homologyMap φ.τ₁ n); infer_instance
  exact isIso_of_mono_of_epi _

end Sharpness.SingularAttachmentComparison
