import Sharpness.Unconditional.CommaKanExact

/-! The actual right-Kan transpose and its pointwise projection formula.
Naturality is inherited from the adjunction, before any pointwise isomorphism
is considered. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness.NormalizerRan
open CategoryTheory CategoryTheory.Limits
variable {R C D : Type u} [CommRing R] [Category.{u} C] [Category.{u} D]
    (p : C ⥤ D) {N : D ⥤ ModuleCat.{u} R} {M : C ⥤ ModuleCat.{u} R}

def transpose (θ : p ⋙ N ⟶ M) : N ⟶ p.ran.obj M :=
  ((p.ranAdjunction (ModuleCat.{u} R)).homEquiv N M) θ

@[reassoc] theorem transpose_counit (θ : p ⋙ N ⟶ M) (X : C) :
    (transpose p θ).app (p.obj X) ≫ (p.ranCounit.app M).app X = θ.app X := by
  have h := ((p.ranAdjunction (ModuleCat.{u} R)).homEquiv N M).symm_apply_apply θ
  rw [Adjunction.homEquiv_counit, p.ranAdjunction_counit] at h
  exact congr_app h X

@[reassoc] theorem transpose_projection (θ : p ⋙ N ⟶ M) (d : D)
    (X : StructuredArrow d p) :
    (transpose p θ).app d ≫ (p.ranObjObjIsoLimit M d).hom ≫
      limit.π (StructuredArrow.proj d p ⋙ M) X =
        N.map X.hom ≫ θ.app X.right := by
  rw [p.ranObjObjIsoLimit_hom_π,
    ← Category.assoc, ← (transpose p θ).naturality, Category.assoc,
    transpose_counit]

/-- Restriction to an actual initial comma model retains the exact same
component maps of the adjunction transpose. -/
@[reassoc] theorem transpose_initial_projection
    {B : Type u} [Category.{u} B] (θ : p ⋙ N ⟶ M) (d : D)
    (J : B ⥤ StructuredArrow d p) [J.Initial] (X : B) :
    (transpose p θ).app d ≫
      ((p.ranObjObjIsoLimit M d) ≪≫
        (Functor.Initial.limitIso J (StructuredArrow.proj d p ⋙ M)).symm).hom ≫
          limit.π (J ⋙ StructuredArrow.proj d p ⋙ M) X =
      N.map (J.obj X).hom ≫ θ.app (J.obj X).right := by
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.Initial.limitIso_inv, Category.assoc]
  rw [limit.pre_π]
  exact transpose_projection p θ d (J.obj X)

end Sharpness.NormalizerRan

