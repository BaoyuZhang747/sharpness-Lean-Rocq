import Sharpness.Unconditional.InjectiveExt
import Sharpness.Unconditional.HomologyPresentation
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear

/-! The full module-valued computation of positive Ext by any injective
resolution, obtained from its explicit cocycles and boundaries. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v
namespace Sharpness
open CategoryTheory CategoryTheory.Limits Opposite
variable (R : Type u) [CommRing R]
    {C : Type v} [Category.{u} C] [Abelian C] [Linear R C] [HasExt.{u} C]
    {Y : C} (I : InjectiveResolution Y) (X : C)

theorem injectiveExtMk_smul (n : ℕ) (f : X ⟶ I.cocomplex.X n)
    (hf : f ≫ I.cocomplex.d n (n + 1) = 0) (r : R) :
    I.extMk (r • f) (n + 1) rfl (by simp [hf]) =
      r • I.extMk f (n + 1) rfl hf := by
  simpa only [Linear.smul_comp, Category.id_comp, Abelian.Ext.mk₀_smul,
    Abelian.Ext.smul_comp, Abelian.Ext.mk₀_id_comp] using
    (I.mk₀_comp_extMk f (n + 1) rfl hf (r • 𝟙 X)).symm

def injectiveCycleToExt (n : ℕ) :
    cochainKernel (injectiveHomComplex R X Y I) n →ₗ[R] Abelian.Ext X Y n where
  toFun f := I.extMk f.val (n + 1) rfl f.property
  map_add' f g := (I.add_extMk f.val g.val (n + 1) rfl f.property g.property).symm
  map_smul' r f := injectiveExtMk_smul R I X n f.val f.property r

theorem injectiveCycleToExt_surjective (n : ℕ) :
    Function.Surjective (injectiveCycleToExt R I X n) := by
  intro a
  obtain ⟨f, hf, he⟩ := I.extMk_surjective a (n + 1) rfl
  exact ⟨⟨f, hf⟩, he⟩

theorem injectiveCycleToExt_ker (n : ℕ) :
    LinearMap.ker (injectiveCycleToExt R I X (n + 1)) =
      cochainBoundaries (injectiveHomComplex R X Y I) (n + 1) := by
  ext f
  change I.extMk f.val (n + 1 + 1) rfl f.property = 0 ↔ _
  rw [I.extMk_eq_zero_iff f.val (n + 1 + 1) rfl f.property n rfl]
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨g, Subtype.ext hg⟩
  · rintro ⟨g, hg⟩
    exact ⟨g, congrArg Subtype.val hg⟩

def injectiveHomologyIsoDerivedExt (n : ℕ) :
    (injectiveHomComplex R X Y I).homology (n + 1) ≅
      ModuleCat.of R (Abelian.Ext X Y (n + 1)) :=
  cochainHomologyIsoOfPresentation _ _ _ (injectiveCycleToExt R I X (n + 1))
    (injectiveCycleToExt_surjective R I X (n + 1))
    (injectiveCycleToExt_ker R I X n)

end Sharpness
