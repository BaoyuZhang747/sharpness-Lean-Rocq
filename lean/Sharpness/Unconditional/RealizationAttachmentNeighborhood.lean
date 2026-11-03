import Sharpness.Unconditional.RealizationAttachmentRetraction
import Sharpness.Unconditional.RealizationSeparationComplement

/-! The actual open attachment neighborhood is a smaller pushout. This
identifies its literal image and descends the boundary-fixed deformation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
universe u
namespace Sharpness.AttachmentHomotopy
open CategoryTheory CategoryTheory.Limits Topology

variable {A N B X Y : TopCat.{u}} {i : A ⟶ B} {l : A ⟶ X} {r : B ⟶ Y} {b : X ⟶ Y}
    (h : IsPushout i l r b) (a : A ⟶ N) (e : N ⟶ B) (w : a ≫ e = i)

def neighborhoodMap : pushout a l ⟶ Y :=
  (IsPushout.of_hasPushout a l).desc (e ≫ r) b
    (by rw [← Category.assoc, w, h.w])

@[reassoc] theorem neighborhoodMap_inl :
    pushout.inl a l ≫ neighborhoodMap h a e w = e ≫ r :=
  (IsPushout.of_hasPushout a l).inl_desc _ _ _

@[reassoc] theorem neighborhoodMap_inr :
    pushout.inr a l ≫ neighborhoodMap h a e w = b :=
  (IsPushout.of_hasPushout a l).inr_desc _ _ _

theorem neighborhood_right_isPushout :
    IsPushout e (pushout.inl a l) r (neighborhoodMap h a e w) := by
  have hh : IsPushout (a ≫ e) l r b := w ▸ h
  exact hh.of_left' (IsPushout.of_hasPushout a l)

variable (he : IsOpenEmbedding e)

include he in
theorem neighborhoodMap_isOpenEmbedding : IsOpenEmbedding (neighborhoodMap h a e w) :=
  RealizationSeparation.isOpenEmbedding_of_isPushout
    (neighborhood_right_isPushout h a e w).flip he

def attachmentNeighborhood : Set Y := Set.range (neighborhoodMap h a e w)

include he in
theorem isOpen_attachmentNeighborhood : IsOpen (attachmentNeighborhood h a e w) :=
  (neighborhoodMap_isOpenEmbedding h a e w he).isOpen_range

include he in
theorem attachmentNeighborhood_preimage :
    r ⁻¹' attachmentNeighborhood h a e w = Set.range e := by
  have hr := (neighborhood_right_isPushout h a e w).map (forget TopCat)
  have hcross (y : B) (p : (pushout a l : TopCat)) :
      r y = neighborhoodMap h a e w p ↔ ∃ n, e n = y ∧ pushout.inl a l n = p :=
    Types.pushoutCocone_inl_eq_inr_iff_of_isColimit hr.isColimit he.injective y p
  ext y
  constructor
  · rintro ⟨p, hp⟩
    obtain ⟨n, hn, _⟩ := (hcross y p).mp hp.symm
    exact ⟨n, hn⟩
  · rintro ⟨n, rfl⟩
    exact ⟨pushout.inl a l n, ((hcross (e n) (pushout.inl a l n)).mpr
      ⟨n, rfl, rfl⟩).symm⟩

include he in
theorem attachmentNeighborhood_mapsTo : Set.MapsTo r (Set.range e)
    (attachmentNeighborhood h a e w) := by
  intro y hy
  rw [← attachmentNeighborhood_preimage h a e w he] at hy
  exact hy

include a w in
theorem source_collar_cover (y : B) : y ∉ Set.range i ∨ y ∈ Set.range e := by
  by_cases hy : y ∈ Set.range i
  · right
    obtain ⟨x, rfl⟩ := hy
    exact ⟨a x, (ConcreteCategory.congr_hom w x)⟩
  · exact Or.inl hy

theorem attachment_neighborhood_cover (y : Y) :
    y ∉ Set.range b ∨ y ∈ attachmentNeighborhood h a e w := by
  by_cases hy : y ∈ Set.range b
  · right
    obtain ⟨x, rfl⟩ := hy
    exact ⟨pushout.inr a l x, ConcreteCategory.congr_hom (neighborhoodMap_inr h a e w) x⟩
  · exact Or.inl hy

variable (q : N ⟶ A) (hq : a ≫ q = 𝟙 A)
    (H : TopCat.Homotopy (𝟙 N) (q ≫ a))
    (hfix : ∀ (s : unitInterval) (x : A), H (s, a x) = a x)

def sourceCollarHomotopyEquiv : ContinuousMap.HomotopyEquiv A (Set.range e) :=
  ({ toFun := a.hom
     invFun := q.hom
     left_inv := by
       change (a ≫ q).hom.Homotopic (ContinuousMap.id A)
       rw [hq]
       exact ContinuousMap.Homotopic.refl _
     right_inv := ⟨H.symm⟩ } : ContinuousMap.HomotopyEquiv A N).trans
      he.toIsEmbedding.toHomeomorph.toHomotopyEquiv

include w in
theorem sourceCollarHomotopyEquiv_apply_val (x : A) :
    (sourceCollarHomotopyEquiv a e he q hq H x).val = i x :=
  ConcreteCategory.congr_hom w x

def neighborhoodHomotopyEquiv :
    ContinuousMap.HomotopyEquiv X (attachmentNeighborhood h a e w) :=
  (attachmentHomotopyEquiv (IsPushout.of_hasPushout a l) q hq H hfix).trans
    (neighborhoodMap_isOpenEmbedding h a e w he).toIsEmbedding.toHomeomorph.toHomotopyEquiv

theorem neighborhoodHomotopyEquiv_apply_val (x : X) :
    (neighborhoodHomotopyEquiv h a e w he q hq H hfix x).val = b x :=
  ConcreteCategory.congr_hom (neighborhoodMap_inr h a e w) x

end Sharpness.AttachmentHomotopy
