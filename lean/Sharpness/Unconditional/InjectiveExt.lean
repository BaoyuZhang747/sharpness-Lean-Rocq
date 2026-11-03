import Sharpness.Unconditional.ExtVanishingComparison
import Mathlib.CategoryTheory.Abelian.Injective.Ext
import Mathlib.CategoryTheory.Abelian.RightDerived

/-! Computation of vanishing of the project's Ext using injective resolutions.
The proof compares explicit cocycles with derived-category Ext; it does not
replace the definition of higher limits or assume a balanced-Ext theorem. -/

set_option autoImplicit false
noncomputable section
universe u v

namespace Sharpness
open CategoryTheory CategoryTheory.Limits Opposite

variable (R : Type u) [CommRing R]
    {C : Type v} [Category.{u} C] [Abelian C] [Linear R C]
    [EnoughProjectives C] [EnoughInjectives C]

/-- The actual complex of linear morphisms into an injective resolution. -/
abbrev injectiveHomComplex (X Y : C) (I : InjectiveResolution Y) :
    CochainComplex (ModuleCat.{u} R) ℕ :=
  (((linearCoyoneda R C).obj (op X)).mapHomologicalComplex _).obj I.cocomplex

/-- All degrees of the project's Ext can be tested by exactness of the Hom
complex of any injective resolution. -/
theorem ext_isZero_iff_injectiveHom_exactAt (X Y : C) (I : InjectiveResolution Y) (n : ℕ) :
    IsZero (((Ext R C n).obj (op X)).obj Y) ↔
      (injectiveHomComplex R X Y I).ExactAt n := by
  letI : HasExt.{u} C := hasExt_of_enoughProjectives.{u, u, v} C
  cases n with
  | zero =>
    let H := (linearCoyoneda R C).obj (op X)
    letI : PreservesFiniteLimits (H ⋙ forget (ModuleCat R)) :=
      inferInstanceAs (PreservesFiniteLimits (coyoneda.obj (op X)))
    letI : PreservesFiniteLimits H :=
      preservesFiniteLimits_of_reflects_of_preserves H (forget (ModuleCat R))
    let e : ((Ext R C 0).obj (op X)).obj Y ≅
        (injectiveHomComplex R X Y I).homology 0 :=
      extZeroHomIso R X Y ≪≫ (H.rightDerivedZeroIsoSelf.app Y).symm ≪≫
        I.isoRightDerivedObj H 0
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    exact ⟨fun h => IsZero.of_iso h e.symm, fun h => IsZero.of_iso h e⟩
  | succ n =>
    rw [ext_succ_isZero_iff_subsingleton R,
      HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp),
      ShortComplex.moduleCat_exact_iff]
    change Subsingleton (Abelian.Ext.{u} X Y (n + 1)) ↔
      (∀ (f : X ⟶ I.cocomplex.X (n + 1)),
        f ≫ I.cocomplex.d (n + 1) (n + 2) = 0 →
          ∃ g : X ⟶ I.cocomplex.X n, g ≫ I.cocomplex.d n (n + 1) = f)
    constructor
    · intro h f hf
      exact (I.extMk_eq_zero_iff f (n + 2) rfl hf n rfl).mp (h.elim _ 0)
    · intro h
      apply subsingleton_of_forall_eq 0
      intro α
      obtain ⟨f, hf, rfl⟩ := I.extMk_surjective α (n + 2) rfl
      exact (I.extMk_eq_zero_iff f (n + 2) rfl hf n rfl).mpr (h f hf)

end Sharpness
