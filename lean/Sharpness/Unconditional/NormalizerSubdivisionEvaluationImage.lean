import Sharpness.Unconditional.NormalizerSubdivisionCommaLifts

/-! The actual image factorization used to normalize objects of the
undercategories of normalizer subdivision evaluation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness.FusionSystem.CentricLinkingSystem
open CategoryTheory
variable {S : Type u} [Group S] [Finite S] {F : FusionSystem S}
    (L : F.CentricLinkingSystem)

/-- The image of an actual linking morphism is again an actual centric object. -/
def normalizerLinkingImage {P Q : L.Object} (f : P ⟶ Q) : L.Object := by
  let f' := L.projection.map f
  let e : P.as.val ≃* F.imageSubgroup f' :=
    MonoidHom.ofInjective (Subtype.val_injective.comp (F.injective _ f'.property))
  exact ⟨⟨F.imageSubgroup (L.projection.map f),
    F.isoSystem.centricIn_of_iso e (F.toImage f').property P.as.property⟩⟩

omit [Finite S] in
theorem normalizerLinkingImage_le {P Q : L.Object} (f : P ⟶ Q) :
    (L.normalizerLinkingImage f).as.val ≤ Q.as.val :=
  F.image_le (L.projection.map f)

theorem normalizer_exists_image_factorization {P Q : L.Object} (f : P ⟶ Q) :
    ∃ a : P ≅ L.normalizerLinkingImage f,
      a.hom ≫ L.inclusionLift (L.normalizerLinkingImage_le f) = f := by
  let a : P ≅ L.normalizerLinkingImage f :=
    L.normalizerLinkingIsoLift (F.imageIso (L.projection.map f))
  have hp : L.projection.map
      (a.hom ≫ L.inclusionLift (L.normalizerLinkingImage_le f)) =
      L.projection.map f := by
    rw [L.projection.map_comp, L.normalizerLinkingIsoLift_projection,
      L.projection_inclusionLift]
    exact F.image_factorization (L.projection.map f)
  obtain ⟨z, hz, _⟩ := (L.central_fiber
    (a.hom ≫ L.inclusionLift (L.normalizerLinkingImage_le f)) f).mp hp
  refine ⟨(L.distinguished P z.val).trans a, ?_⟩
  exact (Category.assoc _ _ _).trans hz

/-- The unique linking isomorphism in the chosen image factorization. -/
def normalizerLinkingImageIso {P Q : L.Object} (f : P ⟶ Q) :
    P ≅ L.normalizerLinkingImage f :=
  Classical.choose (L.normalizer_exists_image_factorization f)

theorem normalizerLinkingImage_factorization {P Q : L.Object} (f : P ⟶ Q) :
    (L.normalizerLinkingImageIso f).hom ≫
      L.inclusionLift (L.normalizerLinkingImage_le f) = f :=
  Classical.choose_spec (L.normalizer_exists_image_factorization f)

theorem normalizerLinkingImageIso_unique {P Q : L.Object} (f : P ⟶ Q)
    (a : P ≅ L.normalizerLinkingImage f)
    (h : a.hom ≫ L.inclusionLift (L.normalizerLinkingImage_le f) = f) :
    a = L.normalizerLinkingImageIso f := by
  apply Iso.ext
  exact L.cancel_right _ _ (L.inclusionLift (L.normalizerLinkingImage_le f))
    (h.trans (L.normalizerLinkingImage_factorization f).symm)

/-- A commutative triangle induces an isomorphism of its two actual images. -/
def normalizerLinkingImageTriangleIso {P Q T : L.Object}
    (f : P ⟶ Q) (g : P ⟶ T) :
    L.normalizerLinkingImage f ≅ L.normalizerLinkingImage g :=
  (L.normalizerLinkingImageIso f).symm.trans (L.normalizerLinkingImageIso g)

theorem normalizerLinkingImageTriangleIso_square {P Q T : L.Object}
    (f : P ⟶ Q) (g : P ⟶ T) (b : Q ⟶ T) (h : f ≫ b = g) :
    (L.normalizerLinkingImageTriangleIso f g).hom ≫
        L.inclusionLift (L.normalizerLinkingImage_le g) =
      L.inclusionLift (L.normalizerLinkingImage_le f) ≫ b := by
  apply (cancel_epi (L.normalizerLinkingImageIso f).hom).mp
  change (L.normalizerLinkingImageIso f).hom ≫
      (((L.normalizerLinkingImageIso f).inv ≫
        (L.normalizerLinkingImageIso g).hom) ≫ _) = _
  simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp,
    L.normalizerLinkingImage_factorization, h]

theorem normalizerLinkingImageTriangleIso_refl {P Q : L.Object} (f : P ⟶ Q) :
    L.normalizerLinkingImageTriangleIso f f = Iso.refl _ := by
  apply Iso.ext
  exact (L.normalizerLinkingImageIso f).inv_hom_id

theorem normalizerLinkingImageTriangleIso_trans {P Q T V : L.Object}
    (f : P ⟶ Q) (g : P ⟶ T) (h : P ⟶ V) :
    (L.normalizerLinkingImageTriangleIso f g).trans
      (L.normalizerLinkingImageTriangleIso g h) =
      L.normalizerLinkingImageTriangleIso f h := by
  apply Iso.ext
  change ((L.normalizerLinkingImageIso f).inv ≫ (L.normalizerLinkingImageIso g).hom) ≫
      ((L.normalizerLinkingImageIso g).inv ≫ (L.normalizerLinkingImageIso h).hom) =
    (L.normalizerLinkingImageIso f).inv ≫ (L.normalizerLinkingImageIso h).hom
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

omit [Finite S] in
/-- An actual linking arrow over an invertible fusion arrow is itself invertible. -/
theorem normalizer_exists_iso_of_projection {P Q : L.Object} (f : P ⟶ Q)
    (e : L.projection.obj P ≅ L.projection.obj Q)
    (he : L.projection.map f = e.hom) : ∃ a : P ≅ Q, a.hom = f := by
  let a := L.normalizerLinkingIsoLift e
  have hp : L.projection.map a.hom = L.projection.map f :=
    (L.normalizerLinkingIsoLift_projection e).trans he.symm
  obtain ⟨z, hz, _⟩ := (L.central_fiber a.hom f).mp hp
  exact ⟨(L.distinguished P z.val).trans a, hz⟩

def normalizerLinkingIsoOfEqualCard {P Q : L.Object} (f : P ⟶ Q)
    (h : Nat.card P.as.val = Nat.card Q.as.val) : P ≅ Q :=
  Classical.choose (L.normalizer_exists_iso_of_projection f
    (F.isoOfEqualOrder (L.projection.map f) h) rfl)

theorem normalizerLinkingIsoOfEqualCard_hom {P Q : L.Object} (f : P ⟶ Q)
    (h : Nat.card P.as.val = Nat.card Q.as.val) :
    (L.normalizerLinkingIsoOfEqualCard f h).hom = f :=
  Classical.choose_spec (L.normalizer_exists_iso_of_projection f
    (F.isoOfEqualOrder (L.projection.map f) h) rfl)

theorem normalizerLinkingImage_card {P Q : L.Object} (f : P ⟶ Q) :
    Nat.card (L.normalizerLinkingImage f).as.val = Nat.card P.as.val := by
  let a := L.normalizerLinkingImageIso f
  exact le_antisymm (F.order_mono (L.projection.map a.inv))
    (F.order_mono (L.projection.map a.hom))

theorem normalizerLinkingImage_lt {P Q : L.Object} (f : P ⟶ Q)
    (h : Nat.card P.as.val ≠ Nat.card Q.as.val) :
    (L.normalizerLinkingImage f).as.val < Q.as.val := by
  apply lt_of_le_of_ne (L.normalizerLinkingImage_le f)
  intro he
  exact h ((L.normalizerLinkingImage_card f).symm.trans
    (congrArg (fun H : Subgroup S => Nat.card H) he))

end Sharpness.FusionSystem.CentricLinkingSystem
