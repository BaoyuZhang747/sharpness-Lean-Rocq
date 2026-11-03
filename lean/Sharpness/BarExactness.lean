import Sharpness.FiniteBar

/-! Cocycle proofs of extension closure and coordinatewise exactness.
These are proofs, not fields of the literature interface. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FiniteBarModel
open CategoryTheory
variable {R : Type u} [CommRing R] {C : Type u} [Category.{u} C]
    (B : FiniteBarModel R C)

theorem map_injective {D E : CoefficientCategory R C} (f : D ⟶ E)
    (h : ∀ P, Function.Injective (f.app P)) (n : ℕ) :
    Function.Injective (B.map f n) := by
  intro x y hxy
  funext i
  exact h (B.source n i) (congrFun hxy i)

theorem map_surjective {D E : CoefficientCategory R C} (f : D ⟶ E)
    (h : ∀ P, Function.Surjective (f.app P)) (n : ℕ) :
    Function.Surjective (B.map f n) := by
  intro y
  choose x hx using fun i => h (B.source n i) (y i)
  exact ⟨x, funext hx⟩

theorem map_exact {D E F : CoefficientCategory R C} (f : D ⟶ E) (g : E ⟶ F)
    (h : ∀ P, Function.Exact (f.app P) (g.app P)) (n : ℕ) :
    Function.Exact (B.map f n) (B.map g n) := by
  intro y
  constructor
  · intro hy
    choose x hx using fun i => (h (B.source n i) (y i)).mp (congrFun hy i)
    exact ⟨x, funext hx⟩
  · rintro ⟨x, rfl⟩
    funext i
    exact (h (B.source n i)).apply_apply_eq_zero (x i)

/-- The extension step used in Lemma 2.4. It is established directly by
lifting and subtracting coboundaries in the actual finite bar cochains. -/
theorem exactPositive_extension {D E F : CoefficientCategory R C}
    (f : D ⟶ E) (g : E ⟶ F)
    (hf : ∀ P, Function.Injective (f.app P))
    (hg : ∀ P, Function.Surjective (g.app P))
    (hex : ∀ P, Function.Exact (f.app P) (g.app P))
    (hD : B.ExactPositive D) (hF : B.ExactPositive F) : B.ExactPositive E := by
  intro n z hz
  have hzF : B.d F (n+1) (B.map g (n+1) z) = 0 := by
    rw [← B.map_d, hz, map_zero]
  obtain ⟨c, hc⟩ := hF n (B.map g (n+1) z) hzF
  obtain ⟨b, hb⟩ := B.map_surjective g hg n c
  let t := z - B.d E n b
  have ht : B.map g (n+1) t = 0 := by
    change B.map g (n+1) (z - B.d E n b) = 0
    rw [map_sub, B.map_d, hb, hc, sub_self]
  obtain ⟨a, ha⟩ := (B.map_exact f g hex (n+1) t).mp ht
  have hat : B.d D (n+1) a = 0 := by
    apply B.map_injective f hf (n+2)
    rw [map_zero, B.map_d, ha]
    change B.d E (n+1) (z - B.d E n b) = 0
    rw [map_sub, hz]
    have hh := LinearMap.congr_fun (B.dd E n) b
    change B.d E (n+1) (B.d E n b) = 0 at hh
    rw [hh, sub_self]
  obtain ⟨a₀, ha₀⟩ := hD n a hat
  refine ⟨b + B.map f n a₀, ?_⟩
  rw [map_add, ← B.map_d, ha₀, ha]
  dsimp [t]
  abel

end Sharpness.FiniteBarModel
