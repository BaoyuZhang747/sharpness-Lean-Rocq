import Sharpness.SpectralSequenceVanishing

/-! Transport of finite convergence along an actual isomorphism of
abutment modules. The filtration is its literal image, and the graded
comparison is constructed on the corresponding module quotients. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory
variable {R V W : Type u} [CommRing R]
    [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]

theorem submoduleQuotientTransport_map (e : V ≃ₗ[R] W) (P Q : Submodule R V) :
    (Q.comap P.subtype).map (e.submoduleMap P).toLinearMap =
      (Q.map e.toLinearMap).comap (P.map e.toLinearMap).subtype := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.val, hx, rfl⟩
  · rintro ⟨x, hx, he⟩
    refine ⟨(e.submoduleMap P).symm y, ?_, (e.submoduleMap P).apply_symm_apply y⟩
    have hi : e ((e.submoduleMap P).symm y).val = y.val :=
      congrArg Subtype.val ((e.submoduleMap P).apply_symm_apply y)
    change ((e.submoduleMap P).symm y).val ∈ Q
    rw [e.injective (hi.trans he.symm)]
    exact hx

def submoduleQuotientTransportIso (e : V ≃ₗ[R] W) (P Q : Submodule R V) :
    ModuleCat.of R (P ⧸ Q.comap P.subtype) ≅
      ModuleCat.of R ((P.map e.toLinearMap) ⧸
        (Q.map e.toLinearMap).comap (P.map e.toLinearMap).subtype) :=
  (Submodule.Quotient.equiv _ _ (e.submoduleMap P)
    (submoduleQuotientTransport_map e P Q)).toModuleIso

variable {E : E₂CohomologicalSpectralSequenceNat (ModuleCat.{u} R)}
    {A B : ℕ → ModuleCat.{u} R}

def FiniteSpectralConvergence.transport (conv : FiniteSpectralConvergence E A)
    (e : ∀ n, A n ≅ B n) : FiniteSpectralConvergence E B where
  filtration n k := (conv.filtration n k).map (e n).toLinearEquiv.toLinearMap
  antitone n a b h := Submodule.map_mono (conv.antitone n h)
  start n := by
    rw [conv.start, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr (e n).toLinearEquiv.surjective
  stop n := by rw [conv.stop, Submodule.map_bot]
  graded n i hi :=
    (submoduleQuotientTransportIso (e n).toLinearEquiv
      (conv.filtration n i) (conv.filtration n (i+1))).symm ≪≫ conv.graded n i hi

end Sharpness
