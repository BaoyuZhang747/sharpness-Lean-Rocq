import Sharpness.Unconditional.RealizationSeparationPushout
import Mathlib.Topology.Homeomorph.Lemmas

/-! Actual complement homeomorphism for a closed topological attachment. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
universe u

namespace Sharpness.RealizationSeparation
open CategoryTheory CategoryTheory.Limits Set Topology

variable {A B C D : TopCat.{u}} {t : A ⟶ B} {l : A ⟶ C} {r : B ⟶ D} {b : C ⟶ D}

theorem isOpen_of_isPushout (h : IsPushout t l r b) (s : Set D)
    (hr : IsOpen (r ⁻¹' s)) (hb : IsOpen (b ⁻¹' s)) : IsOpen s := by
  rw [← isClosed_compl_iff]
  exact isClosed_of_isPushout h sᶜ hr.isClosed_compl hb.isClosed_compl

theorem isOpenEmbedding_of_isPushout (h : IsPushout t l r b)
    (hl : IsOpenEmbedding l) : IsOpenEmbedding r := by
  let ht := h.map (forget TopCat)
  have hinj : Function.Injective r :=
    Types.pushoutCocone_inr_injective_of_isColimit ht.flip.isColimit hl.injective
  have hcross (z : C) (y : B) : b z = r y ↔ ∃ a, l a = z ∧ t a = y :=
    Types.pushoutCocone_inl_eq_inr_iff_of_isColimit ht.flip.isColimit hl.injective z y
  apply IsOpenEmbedding.of_continuous_injective_isOpenMap r.hom.continuous hinj
  intro s hs
  apply isOpen_of_isPushout h (r '' s)
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
    exact hl.isOpenMap _ (hs.preimage t.hom.continuous)

theorem pushout_preimage_range (h : IsPushout t l r b) (hl : Function.Injective l) :
    b ⁻¹' Set.range r = Set.range l := by
  let ht := h.map (forget TopCat)
  ext x
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨a, ha, _⟩ := (Types.pushoutCocone_inl_eq_inr_iff_of_isColimit
      ht.flip.isColimit hl x y).mp hy.symm
    exact ⟨a, ha⟩
  · rintro ⟨a, rfl⟩
    exact ⟨t a, ConcreteCategory.congr_hom h.w a⟩

theorem pushout_outside_injective (h : IsPushout t l r b) {x y : C}
    (hx : x ∉ Set.range l) (hy : y ∉ Set.range l) (hxy : b x = b y) : x = y := by
  classical
  let ht := h.map (forget TopCat)
  let q : C → Option C := fun z => if z ∈ Set.range l then none else some z
  let c : PushoutCocone ((forget TopCat).map t) ((forget TopCat).map l) :=
    PushoutCocone.mk (TypeCat.ofHom (fun _ : B => (none : Option C))) (TypeCat.ofHom q)
      (by ext a; simp [q])
  have hfac (z : C) : ht.isColimit.desc c (b z) = q z :=
    ConcreteCategory.congr_hom (ht.isColimit.fac c WalkingSpan.right) z
  have heq := congrArg (ht.isColimit.desc c) hxy
  rw [hfac, hfac] at heq
  have heq' : some x = some y := by simpa only [q, if_neg hx, if_neg hy] using heq
  exact Option.some.inj heq'

def pushoutComplementMap (_h : IsPushout t l r b) : ↥((Set.range l)ᶜ) → D := fun z => b z.val

theorem pushoutComplementMap_range (h : IsPushout t l r b) (hl : Function.Injective l) :
    Set.range (pushoutComplementMap h) = (Set.range r)ᶜ := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    have hp := congrArg (fun s : Set C => x.val ∈ s) (pushout_preimage_range h hl)
    exact fun hz => x.property (hp.mp hz)
  · intro hz
    obtain ⟨y, hy⟩ | ⟨x, hx, hxout⟩ := Types.eq_or_eq_of_isPushout' (h.map (forget TopCat)) z
    · exact (hz ⟨y, hy⟩).elim
    · exact ⟨⟨x, hxout⟩, hx⟩

theorem pushoutComplementMap_isOpenEmbedding (h : IsPushout t l r b)
    (hl : IsClosedEmbedding l) : IsOpenEmbedding (pushoutComplementMap h) := by
  have hinj : Function.Injective (pushoutComplementMap h) := by
    intro x y hxy
    exact Subtype.ext (pushout_outside_injective h x.property y.property hxy)
  apply IsOpenEmbedding.of_continuous_injective_isOpenMap
    (b.hom.continuous.comp continuous_subtype_val) hinj
  intro s hs
  have hsC : IsOpen (Subtype.val '' s : Set C) :=
    hl.isClosed_range.isOpen_compl.isOpenEmbedding_subtypeVal.isOpenMap s hs
  apply isOpen_of_isPushout h (pushoutComplementMap h '' s)
  · have heq : r ⁻¹' (pushoutComplementMap h '' s) = ∅ := by
      ext y
      constructor
      · rintro ⟨x, hx, hxy⟩
        have hz : pushoutComplementMap h x ∈ (Set.range r)ᶜ := by
          rw [← pushoutComplementMap_range h hl.injective]
          exact ⟨x, rfl⟩
        exact (hz ⟨y, hxy.symm⟩).elim
      · intro hy
        exact hy.elim
    rw [heq]
    exact isOpen_empty
  · have heq : b ⁻¹' (pushoutComplementMap h '' s) = Subtype.val '' s := by
      ext z
      constructor
      · rintro ⟨x, hx, hxz⟩
        have hz : z ∉ Set.range l := by
          intro hz
          have hbz : b z ∈ Set.range r := by
            rw [← pushout_preimage_range h hl.injective] at hz
            exact hz
          have hbx : pushoutComplementMap h x ∈ (Set.range r)ᶜ := by
            rw [← pushoutComplementMap_range h hl.injective]
            exact ⟨x, rfl⟩
          exact hbx (hxz ▸ hbz)
        exact ⟨x, hx, pushout_outside_injective h x.property hz hxz⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x, hx, rfl⟩
    rw [heq]
    exact hsC

def pushoutComplementHomeo (h : IsPushout t l r b) (hl : IsClosedEmbedding l) :
    ↥((Set.range l)ᶜ) ≃ₜ ↥((Set.range r)ᶜ) :=
  (pushoutComplementMap_isOpenEmbedding h hl).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (pushoutComplementMap_range h hl.injective))

@[simp] theorem pushoutComplementHomeo_apply_val (h : IsPushout t l r b)
    (hl : IsClosedEmbedding l) (x : ↥((Set.range l)ᶜ)) :
    (pushoutComplementHomeo h hl x).val = b x.val := rfl

end Sharpness.RealizationSeparation
