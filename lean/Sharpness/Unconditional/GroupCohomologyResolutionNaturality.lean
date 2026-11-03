import Sharpness.Unconditional.GroupCohomologyResolutionComparison

/-! Naturality of Mathlib's actual Ext comparison isomorphism under
explicit comparison maps of projective resolutions. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
universe u
namespace Sharpness.OrdinaryCohomology
open CategoryTheory
variable {R G : Type u} [CommRing R] [Group G]

theorem homologyUnop_inv_naturality
    {X Y : ChainComplex (ModuleCat R)ᵒᵖ ℕ} (f : X ⟶ Y) (n : ℕ) :
    (HomologicalComplex.homologyMap f n).unop ≫ (HomologicalComplex.homologyUnop X n).inv =
      (HomologicalComplex.homologyUnop Y n).inv ≫
        HomologicalComplex.homologyMap
          ((HomologicalComplex.unopFunctor (ModuleCat R) (ComplexShape.down ℕ)).map f.op) n := by
  let ψ := (HomologicalComplex.unopFunctor (ModuleCat R) (ComplexShape.down ℕ)).map f.op
  have h := congrArg Quiver.Hom.unop (HomologicalComplex.homologyOp_hom_naturality ψ n)
  have h' : (HomologicalComplex.homologyUnop Y n).hom ≫
      (HomologicalComplex.homologyMap f n).unop =
      HomologicalComplex.homologyMap ψ n ≫ (HomologicalComplex.homologyUnop X n).hom := by
    exact h
  apply (cancel_epi (HomologicalComplex.homologyUnop Y n).hom).mp
  rw [← Category.assoc, h', Category.assoc, Iso.hom_inv_id, Category.comp_id,
    Iso.hom_inv_id_assoc]

/-- Canonical Ext-to-Hom cohomology comparisons commute with any
explicit comparison map lifting the identity. -/
theorem isoExt_hom_precomp {Z : Rep R G}
    (P Q : ProjectiveResolution Z) (V : Rep R G)
    (φ : P.complex ⟶ Q.complex)
    (hφ : φ.f 0 ≫ Q.π.f 0 = P.π.f 0) (n : ℕ) :
    (Q.isoExt n V).hom ≫ HomologicalComplex.homologyMap (homComplexPrecomp V φ) n =
      (P.isoExt n V).hom := by
  let F := ((linearYoneda R (Rep R G)).obj V).rightOp
  have hφ' : φ.f 0 ≫ Q.π.f 0 = P.π.f 0 ≫ 𝟙 Z :=
    hφ.trans (Category.comp_id (P.π.f 0)).symm
  have hd := ProjectiveResolution.isoLeftDerivedObj_inv_naturality
    (𝟙 Z) P Q φ hφ' F n
  rw [(F.leftDerived n).map_id, Category.comp_id] at hd
  have hdu := congrArg Quiver.Hom.unop hd
  have hdu' : (P.isoLeftDerivedObj F n).inv.unop =
      (Q.isoLeftDerivedObj F n).inv.unop ≫
        (HomologicalComplex.homologyMap ((F.mapHomologicalComplex _).map φ) n).unop := hdu
  have hn : (HomologicalComplex.homologyUnop ((F.mapHomologicalComplex _).obj Q.complex) n).inv ≫
      HomologicalComplex.homologyMap (homComplexPrecomp V φ) n =
      (HomologicalComplex.homologyMap ((F.mapHomologicalComplex _).map φ) n).unop ≫
        (HomologicalComplex.homologyUnop ((F.mapHomologicalComplex _).obj P.complex) n).inv :=
    (homologyUnop_inv_naturality ((F.mapHomologicalComplex _).map φ) n).symm
  change ((Q.isoLeftDerivedObj F n).inv.unop ≫
      (HomologicalComplex.homologyUnop ((F.mapHomologicalComplex _).obj Q.complex) n).inv) ≫ _ =
    (P.isoLeftDerivedObj F n).inv.unop ≫
      (HomologicalComplex.homologyUnop ((F.mapHomologicalComplex _).obj P.complex) n).inv
  rw [Category.assoc, hn, ← Category.assoc, ← hdu']

theorem groupCohomologyIso_hom_precomp
    (P Q : ProjectiveResolution (Rep.trivial R G R)) (V : Rep R G)
    (φ : P.complex ⟶ Q.complex)
    (hφ : φ.f 0 ≫ Q.π.f 0 = P.π.f 0) (n : ℕ) :
    (groupCohomologyIso V n Q).hom ≫
        HomologicalComplex.homologyMap (homComplexPrecomp V φ) n =
      (groupCohomologyIso V n P).hom := by
  change ((groupCohomologyIsoExt V n).hom ≫ (Q.isoExt n V).hom) ≫ _ =
    (groupCohomologyIsoExt V n).hom ≫ (P.isoExt n V).hom
  rw [Category.assoc, isoExt_hom_precomp P Q V φ hφ n]

theorem groupCohomologyIso_bar_hom (V : Rep R G) (n : ℕ) :
    (groupCohomologyIso V n (Rep.barResolution R G)).hom =
      HomologicalComplex.homologyMap (groupCohomology.inhomogeneousCochainsIso V).hom n := by
  simp [groupCohomologyIso, groupCohomologyIsoExt, Rep.barResolution.extIso,
    HomotopyEquiv.ofIso]

end Sharpness.OrdinaryCohomology
