import Sharpness.Unconditional.SingularAttachmentComparisonCollars
import Sharpness.Unconditional.RealizationAttachmentComplements

/-! Excision for an actual topological attachment with a boundary-fixed
collar. All relative comparison maps are the original pushout maps. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
universe u

namespace Sharpness.SingularAttachmentComparison
open CategoryTheory CategoryTheory.Limits Topology
open Sharpness.SingularChainExcision Sharpness.AttachmentHomotopy

variable (R : Type u) [CommRing R]
  {A N B X Y : TopCat.{u}} {i : A ⟶ B} {l : A ⟶ X} {r : B ⟶ Y} {b : X ⟶ Y}
  (h : IsPushout i l r b) (hi : IsClosedEmbedding i)
  (a : A ⟶ N) (e : N ⟶ B) (w : a ≫ e = i) (he : IsOpenEmbedding e)
  (q : N ⟶ A) (hq : a ≫ q = 𝟙 A)
  (H : TopCat.Homotopy (𝟙 N) (q ≫ a))
  (hfix : ∀ (s : unitInterval) (x : A), H (s, a x) = a x)

include hi a e w he q hq H hfix

/-- The actual relative singular-chain map of a collared attachment is a
quasi-isomorphism, for arbitrary commutative coefficients. -/
theorem collaredPushout_relative_quasiIso :
    QuasiIso (relativeArrowMap R i b l r h.w) := by
  have hb : IsClosedEmbedding b :=
    RealizationSeparation.isClosedEmbedding_of_isPushout h.flip hi
  letI : Mono i := (TopCat.mono_iff_injective i).mpr hi.injective
  letI : Mono b := (TopCat.mono_iff_injective b).mpr hb.injective
  let hU := attachmentComplement_mapsTo h hi
  let hN := attachmentNeighborhood_mapsTo h a e w he
  have heU : restrictedMap r hU =
      (TopCat.isoOfHomeo (attachmentComplementHomeo h hi)).hom := by
    ext x
    rfl
  have heI : restrictedMap r (intersectionMapsTo r hU hN) =
      (TopCat.isoOfHomeo (attachmentComplementIntersectionHomeo h hi a e w he)).hom := by
    ext x
    rfl
  letI : IsIso (restrictedMap r hU) := heU ▸ inferInstance
  letI : IsIso (restrictedMap r (intersectionMapsTo r hU hN)) := heI ▸ inferInstance
  exact relativeAttachmentMap_quasiIso R i b l r h.w hN
    (sourceCollarHomotopyEquiv a e he q hq H)
    (neighborhoodHomotopyEquiv h a e w he q hq H hfix)
    (by ext x; exact sourceCollarHomotopyEquiv_apply_val a e w he q hq H x)
    (by ext x; exact neighborhoodHomotopyEquiv_apply_val h a e w he q hq H hfix x)
    hU hi.isClosed_range.isOpen_compl he.isOpen_range (source_collar_cover a e w)
    hb.isClosed_range.isOpen_compl (isOpen_attachmentNeighborhood h a e w he)
    (attachment_neighborhood_cover h a e w)

end Sharpness.SingularAttachmentComparison


