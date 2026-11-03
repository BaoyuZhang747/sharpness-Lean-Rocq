import Mathlib.Topology.Category.TopCat.Limits.Basic
import Mathlib.Topology.Category.TopCat.EpiMono
import Mathlib.CategoryTheory.Limits.Types.Pushouts
import Mathlib.Topology.Separation.Basic

/-! Separation and closed embeddings for genuine topological attachment
pushouts. These lemmas use the actual underlying pushout equivalence relation
and the final topology of the pushout. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
universe u

namespace Sharpness.RealizationSeparation
open CategoryTheory CategoryTheory.Limits Set Topology

private theorem types_pushout_inl_eq_inl {A B C : Type u} (f : A ⟶ B) (g : A ⟶ C)
    (c : PushoutCocone f g) (hc : IsColimit c) (hf : Function.Injective f) (x y : B) :
    c.inl x = c.inl y ↔ x = y ∨
      ∃ a b : A, g a = g b ∧ x = f a ∧ y = f b := by
  letI : Mono f := (CategoryTheory.mono_iff_injective f).mpr hf
  let e := IsColimit.coconePointUniqueUpToIso hc (Types.Pushout.isColimitCocone f g)
  have he (z : B) : e.hom (c.inl z) = Types.Pushout.inl f g z :=
    ConcreteCategory.congr_hom
      (IsColimit.comp_coconePointUniqueUpToIso_hom hc (Types.Pushout.isColimitCocone f g)
        WalkingSpan.left) z
  rw [← e.toEquiv.injective.eq_iff]
  change e.hom (c.inl x) = e.hom (c.inl y) ↔ _
  rw [he x, he y]
  change (Quot.mk _ (Sum.inl x) : Types.Pushout f g) = Quot.mk _ (Sum.inl y) ↔ _
  simpa only [exists_prop] using
    (Types.Pushout.quot_mk_eq_iff f g (Sum.inl x) (Sum.inl y)).trans
      (Types.Pushout.inl_rel'_inl_iff f g x y)

variable {A B C D : TopCat.{u}} {t : A ⟶ B} {l : A ⟶ C} {r : B ⟶ D} {b : C ⟶ D}

/-- The final closed-set criterion for the two actual legs of a pushout. -/
theorem isClosed_of_isPushout (h : IsPushout t l r b) (s : Set D)
    (hr : IsClosed (r ⁻¹' s)) (hb : IsClosed (b ⁻¹' s)) : IsClosed s := by
  apply (TopCat.isClosed_iff_of_isColimit _ h.isColimit s).mpr
  intro j
  cases j with
  | none =>
    change IsClosed ((fun a => r (t a)) ⁻¹' s)
    exact hr.preimage t.hom.continuous
  | some j => cases j with
    | left => exact hr
    | right => exact hb

/-- Pushing out an actual closed embedding gives an actual closed embedding. -/
theorem isClosedEmbedding_of_isPushout (h : IsPushout t l r b)
    (hl : IsClosedEmbedding l) : IsClosedEmbedding r := by
  let ht := h.map (forget TopCat)
  have hinj : Function.Injective r :=
    Types.pushoutCocone_inr_injective_of_isColimit ht.flip.isColimit hl.injective
  have hcross (z : C) (y : B) : b z = r y ↔ ∃ a, l a = z ∧ t a = y :=
    Types.pushoutCocone_inl_eq_inr_iff_of_isColimit ht.flip.isColimit hl.injective z y
  apply IsClosedEmbedding.of_continuous_injective_isClosedMap r.hom.continuous hinj
  intro s hs
  apply isClosed_of_isPushout h (r '' s)
  · simpa only [Set.preimage_image_eq _ hinj] using hs
  · have heq : b ⁻¹' (r '' s) = l '' (t ⁻¹' s) := by
      ext z
      constructor
      · rintro ⟨y, hy, he⟩
        obtain ⟨a, ha, hat⟩ := (hcross z y).mp he.symm
        refine ⟨a, ?_, ha⟩
        change t a ∈ s
        rw [hat]
        exact hy
      · rintro ⟨a, ha, rfl⟩
        exact ⟨t a, ha, ((hcross (l a) (t a)).mpr ⟨a, rfl, rfl⟩).symm⟩
    rw [heq]
    exact hl.isClosedMap _ (hs.preimage t.hom.continuous)

private theorem attachment_fiber_outside (h : IsPushout t l r b)
    (hl : Function.Injective l) (z : C) (hz : z ∉ Set.range l) :
    b ⁻¹' ({b z} : Set D) = {z} := by
  let ht := h.map (forget TopCat)
  ext y
  change b y = b z ↔ y = z
  have he := types_pushout_inl_eq_inl _ _ _ ht.flip.isColimit hl y z
  change b y = b z ↔ y = z ∨ ∃ a a' : A, t a = t a' ∧ y = l a ∧ z = l a' at he
  rw [he]
  constructor
  · rintro (hy | ⟨a, a', haa', hay, haz⟩)
    · exact hy
    · exact (hz ⟨a', haz.symm⟩).elim
  · exact Or.inl

/-- Attaching a T1 space along a closed embedding to a T1 space preserves T1. -/
theorem t1Space_of_isPushout (h : IsPushout t l r b)
    (hl : IsClosedEmbedding l) [T1Space B] [T1Space C] : T1Space D where
  t1 z := by
    let ht := h.map (forget TopCat)
    obtain ⟨y, rfl⟩ | ⟨y, rfl, hy⟩ := Types.eq_or_eq_of_isPushout' ht z
    · change IsClosed ({r y} : Set D)
      simpa only [Set.image_singleton] using
        (isClosedEmbedding_of_isPushout h hl).isClosedMap {y} isClosed_singleton
    · apply isClosed_of_isPushout h {b y}
      · have hempty : r ⁻¹' ({b y} : Set D) = ∅ := by
          ext z
          constructor
          · intro hz
            obtain ⟨a, ha, _⟩ :=
              (Types.pushoutCocone_inl_eq_inr_iff_of_isColimit ht.flip.isColimit
                hl.injective y z).mp hz.symm
            exact (hy ⟨a, ha⟩).elim
          · intro hz
            exact hz.elim
        rw [hempty]
        exact isClosed_empty
      · rw [attachment_fiber_outside h hl.injective y hy]
        exact isClosed_singleton

end Sharpness.RealizationSeparation
