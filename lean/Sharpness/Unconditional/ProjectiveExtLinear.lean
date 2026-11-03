import Sharpness.Unconditional.HomologyPresentation
import Mathlib.CategoryTheory.Abelian.Ext
import Mathlib.CategoryTheory.Abelian.Projective.Ext
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives

/-! A module isomorphism, not merely a vanishing equivalence, between the
native projective-resolution Ext and derived-category Ext in positive degrees. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v
namespace Sharpness
open CategoryTheory Opposite
variable (R : Type u) [CommRing R]
    {C : Type v} [Category.{u} C] [Abelian C] [Linear R C] [HasExt.{u} C]

def projectiveExtCocycleMap {X : C} (P : ProjectiveResolution X) (Y : C) (n : ℕ) :
    cochainKernel (P.complex.linearYonedaObj R Y) (n + 1) →ₗ[R]
      Abelian.Ext.{u} X Y (n + 1) where
  toFun f := P.extMk f.val (n + 2) rfl f.property
  map_add' f g := (P.add_extMk f.val g.val (n + 2) rfl f.property g.property).symm
  map_smul' r f := by
    change P.extMk (r • f.val) (n + 2) rfl _ =
      r • P.extMk f.val (n + 2) rfl f.property
    rw [Abelian.Ext.smul_eq_comp_mk₀, P.extMk_comp_mk₀]
    simp only [Linear.comp_smul, Category.comp_id]

theorem projectiveExtCocycleMap_surjective {X : C}
    (P : ProjectiveResolution X) (Y : C) (n : ℕ) :
    Function.Surjective (projectiveExtCocycleMap R P Y n) := by
  intro α
  obtain ⟨f, hf, hα⟩ := P.extMk_surjective α (n + 2) rfl
  exact ⟨⟨f, hf⟩, hα⟩

theorem projectiveExtCocycleMap_ker {X : C}
    (P : ProjectiveResolution X) (Y : C) (n : ℕ) :
    LinearMap.ker (projectiveExtCocycleMap R P Y n) =
      cochainBoundaries (P.complex.linearYonedaObj R Y) (n + 1) := by
  ext f
  have hb : f ∈ cochainBoundaries (P.complex.linearYonedaObj R Y) (n + 1) ↔
      ∃ g : P.complex.X n ⟶ Y, P.complex.d (n + 1) n ≫ g = f.val := by
    change (∃ g : (P.complex.linearYonedaObj R Y).X ((n + 1) - 1),
      (cochainShort (P.complex.linearYonedaObj R Y) (n + 1)).moduleCatToCycles g = f) ↔ _
    simp only [cochainShort]
    constructor
    · rintro ⟨g, hg⟩
      exact ⟨g, congrArg Subtype.val hg⟩
    · rintro ⟨g, hg⟩
      exact ⟨g, Subtype.ext hg⟩
  change P.extMk f.val (n + 2) rfl f.property = 0 ↔ _
  exact (P.extMk_eq_zero_iff f.val (n + 2) rfl f.property n rfl).trans hb.symm

/-- The actual cohomology of the Hom complex is the derived Ext module. -/
def projectiveHomologyIsoDerivedExt {X : C}
    (P : ProjectiveResolution X) (Y : C) (n : ℕ) :
    (P.complex.linearYonedaObj R Y).homology (n + 1) ≅
      ModuleCat.of R (Abelian.Ext.{u} X Y (n + 1)) :=
  cochainHomologyIsoOfPresentation _ _ _ (projectiveExtCocycleMap R P Y n)
    (projectiveExtCocycleMap_surjective R P Y n)
    (projectiveExtCocycleMap_ker R P Y n)

variable [EnoughProjectives C]

/-- Positive-degree native module-valued Ext agrees with derived-category Ext. -/
def nativeExtIsoDerivedExt (X Y : C) (n : ℕ) :
    ((Ext R C (n + 1)).obj (op X)).obj Y ≅
      ModuleCat.of R (Abelian.Ext.{u} X Y (n + 1)) :=
  (projectiveResolution X).isoExt (R := R) (n + 1) Y ≪≫
    projectiveHomologyIsoDerivedExt R (projectiveResolution X) Y n

end Sharpness
