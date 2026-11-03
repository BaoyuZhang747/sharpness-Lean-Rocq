import Sharpness.Limits
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
Manuscript Lemma 3.5 from the Alperin generation input. The published theorem
is used only to supply a decomposition into restrictions of centric
automorphisms. Stability is propagated along that decomposition here.
-/
set_option autoImplicit false
noncomputable section
universe u v w
namespace Sharpness
open CategoryTheory

inductive AlperinGenerated {C : Type v} [Category.{v} C]
    (K : ObjectProperty C) (T : C) (inc : ∀ P : C, P ⟶ T) :
    {P Q : C} → (P ⟶ Q) → Prop
  | inclusion {P Q} (f : P ⟶ Q) (comm : f ≫ inc Q = inc P) : AlperinGenerated K T inc f
  | centricRestriction {P Q A} (f : P ⟶ Q) (hA : K A) (a : Aut A)
      (i : P ⟶ A) (j : Q ⟶ A) (hi : i ≫ inc A = inc P) (hj : j ≫ inc A = inc Q)
      (comm : f ≫ j = i ≫ a.hom) : AlperinGenerated K T inc f
  | comp {P Q U} (f : P ⟶ Q) (g : Q ⟶ U)
      (hf : AlperinGenerated K T inc f) (hg : AlperinGenerated K T inc g) :
      AlperinGenerated K T inc (f ≫ g)

namespace Coefficient
variable {R : Type u} [Ring R] {C : Type v} [Category.{v} C]
    (D : Coefficient.{u,v,w} R C) (K : ObjectProperty C)
    (T : C) (inc : ∀ P : C, P ⟶ T)

def onFull : Coefficient R K.FullSubcategory where
  Value P := D.Value P.obj
  valueAddCommGroup P := D.valueAddCommGroup P.obj
  valueModule P := D.valueModule P.obj
  pull f := D.pull f.hom
  pull_id P := D.pull_id P.obj
  pull_comp f g := D.pull_comp f.hom g.hom

theorem stable_on_generated (x : D.Value T)
    (stable_centric : ∀ A : C, K A → ∀ a : Aut A,
      D.pull a.hom (D.pull (inc A) x) = D.pull (inc A) x)
    {P Q : C} (f : P ⟶ Q) (generated : AlperinGenerated K T inc f) :
    D.pull f (D.pull (inc Q) x) = D.pull (inc P) x := by
  induction generated with
  | inclusion f comm =>
    rw [← LinearMap.comp_apply, ← D.pull_comp, comm]
  | centricRestriction f hA a i j hi hj comm =>
    calc
      D.pull f (D.pull (inc _) x) = D.pull (f ≫ j) (D.pull (inc _) x) := by
        simp only [← hj, D.pull_comp, LinearMap.comp_apply]
      _ = D.pull (i ≫ a.hom) (D.pull (inc _) x) := by rw [comm]
      _ = D.pull i (D.pull a.hom (D.pull (inc _) x)) := by
        rw [D.pull_comp, LinearMap.comp_apply]
      _ = D.pull i (D.pull (inc _) x) := by rw [stable_centric _ hA a]
      _ = D.pull (inc _) x := by rw [← LinearMap.comp_apply, ← D.pull_comp, hi]
  | comp f g _ _ ihf ihg =>
    rw [D.pull_comp, LinearMap.comp_apply, ihg, ihf]

/-- The explicit epsilon/eta maps for the centric subcategory, after using
the cited Alperin theorem as generation data. -/
def limitCentricEquivStable (hT : K T) (inc_id : inc T = 𝟙 T)
    (alperin : ∀ {P Q : C} (f : P ⟶ Q), AlperinGenerated K T inc f) :
    (D.onFull K).limit ≃ₗ[R] D.arrowStable T inc where
  toFun c := ⟨c.val ⟨T, hT⟩, by
    intro P Q f
    apply D.stable_on_generated K T inc _ _ f (alperin f)
    intro A hA a
    have hinc := c.property (show (⟨A, hA⟩ : K.FullSubcategory) ⟶ ⟨T, hT⟩ from ⟨inc A⟩)
    have haut := c.property
      (show (⟨A, hA⟩ : K.FullSubcategory) ⟶ ⟨A, hA⟩ from ⟨a.hom⟩)
    change D.pull (inc A) (c.val ⟨T, hT⟩) = c.val ⟨A, hA⟩ at hinc
    change D.pull a.hom (c.val ⟨A, hA⟩) = c.val ⟨A, hA⟩ at haut
    rw [hinc, haut]⟩
  invFun x := ⟨fun P => D.pull (inc P.obj) x.val, by
    intro P Q f
    exact x.property f.hom⟩
  left_inv c := by
    apply Subtype.ext
    funext P
    exact c.property (show P ⟶ (⟨T, hT⟩ : K.FullSubcategory) from ⟨inc P.obj⟩)
  right_inv x := by
    apply Subtype.ext
    change D.pull (inc T) x.val = x.val
    rw [inc_id, D.pull_id]
    rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end Coefficient
end Sharpness
