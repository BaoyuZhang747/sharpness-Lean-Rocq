import Sharpness.Unconditional.RealizationSeparationPushout
import Mathlib.CategoryTheory.Limits.Types.Filtered

/-! Closed embeddings and T1 separation pass through an actual sequential
colimit of closed embeddings. The injectivity proof uses the native filtered
colimit equality criterion; topology uses the genuine final closed-set test. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
universe u

namespace Sharpness.RealizationSeparation
open CategoryTheory CategoryTheory.Limits Topology Set

variable (F : ℕ ⥤ TopCat.{u})
  (he : ∀ n, IsClosedEmbedding (F.map (homOfLE (Nat.le_succ n))))
include he

theorem sequential_map_isClosedEmbedding {n m : ℕ} (h : n ≤ m) :
    IsClosedEmbedding (F.map (homOfLE h)) := by
  induction m, h using Nat.le_induction with
  | base =>
    have heq : F.map (homOfLE (le_refl n)) = 𝟙 (F.obj n) := by
      exact F.map_id n
    rw [heq]
    exact IsClosedEmbedding.id
  | succ m h ih =>
    have heq : F.map (homOfLE (Nat.le_succ_of_le h)) =
        F.map (homOfLE h) ≫ F.map (homOfLE (Nat.le_succ m)) :=
      F.map_comp _ _
    rw [heq]
    exact (he m).comp ih

variable (c : Cocone F) (hc : IsColimit c)
include hc

theorem sequential_inclusion_injective (n : ℕ) : Function.Injective (c.ι.app n) := by
  intro x y hxy
  obtain ⟨m, f, hf⟩ := (Types.FilteredColimit.isColimit_eq_iff'
    (isColimitOfPreserves (forget TopCat) hc) x y).mp hxy
  exact (sequential_map_isClosedEmbedding F he (leOfHom f)).injective hf

theorem sequential_inclusion_isClosedEmbedding (n : ℕ) : IsClosedEmbedding (c.ι.app n) := by
  have hinj := sequential_inclusion_injective F he c hc
  apply IsClosedEmbedding.of_continuous_injective_isClosedMap (c.ι.app n).hom.continuous (hinj n)
  intro s hs
  apply (TopCat.isClosed_iff_of_isColimit c hc _).mpr
  intro m
  obtain hmn | hnm := le_total m n
  · have hpoint (x : F.obj m) : c.ι.app n (F.map (homOfLE hmn) x) = c.ι.app m x :=
      ConcreteCategory.congr_hom (c.w (homOfLE hmn)) x
    have hpre : c.ι.app m ⁻¹' (c.ι.app n '' s) = F.map (homOfLE hmn) ⁻¹' s := by
      ext x
      constructor
      · rintro ⟨y, hy, heq⟩
        have heq' : y = F.map (homOfLE hmn) x := (hinj n) (heq.trans (hpoint x).symm)
        change F.map (homOfLE hmn) x ∈ s
        rw [← heq']
        exact hy
      · intro hx
        exact ⟨F.map (homOfLE hmn) x, hx, hpoint x⟩
    rw [hpre]
    exact hs.preimage (F.map (homOfLE hmn)).hom.continuous
  · have hpoint (x : F.obj n) : c.ι.app m (F.map (homOfLE hnm) x) = c.ι.app n x :=
      ConcreteCategory.congr_hom (c.w (homOfLE hnm)) x
    have hpre : c.ι.app m ⁻¹' (c.ι.app n '' s) = F.map (homOfLE hnm) '' s := by
      ext x
      constructor
      · rintro ⟨y, hy, heq⟩
        exact ⟨y, hy, (hinj m) ((hpoint y).trans heq)⟩
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y, hy, (hpoint y).symm⟩
    rw [hpre]
    exact (sequential_map_isClosedEmbedding F he hnm).isClosedMap s hs

theorem sequential_colimit_t1Space (hT : ∀ n, T1Space (F.obj n)) : T1Space c.pt where
  t1 z := by
    obtain ⟨n, y, hy⟩ := Types.jointly_surjective_of_isColimit
      (isColimitOfPreserves (forget TopCat) hc) z
    letI := hT n
    have hyclosed : IsClosed ({y} : Set (F.obj n)) := isClosed_singleton
    have himage := (sequential_inclusion_isClosedEmbedding F he c hc n).isClosedMap {y} hyclosed
    change c.ι.app n y = z at hy
    simpa only [Set.image_singleton, hy] using himage

end Sharpness.RealizationSeparation
