import Sharpness.LinkingMonomorphisms

/-! Isomorphisms lift through the actual linking projection. The proof
uses precisely projection surjectivity, the central fiber axiom, and
the already proved cancellation of actual linking morphisms. -/
set_option autoImplicit false
noncomputable section
universe u

namespace Sharpness.FusionSystem.CentricLinkingSystem
open CategoryTheory
variable {S : Type u} [Group S] {F : FusionSystem S} (L : F.CentricLinkingSystem)

def BLODiagramIsoOfProjection {P Q : L.Object} (f : P ⟶ Q)
    (e : L.projection.obj P ≅ L.projection.obj Q)
    (hf : L.projection.map f = e.hom) : P ≅ Q := by
  let g := Classical.choose (L.projection_surjective Q P e.inv)
  have hg := Classical.choose_spec (L.projection_surjective Q P e.inv)
  have hp : L.projection.map (𝟙 P) = L.projection.map (f ≫ g) := by
    rw [L.projection.map_id, L.projection.map_comp, hf, hg, e.hom_inv_id]
  let z := Classical.choose ((L.central_fiber (𝟙 P) (f ≫ g)).mp hp)
  have hz : (L.distinguished P z.val).hom ≫ (𝟙 P) = f ≫ g :=
    (Classical.choose_spec ((L.central_fiber (𝟙 P) (f ≫ g)).mp hp)).1
  have hfg : f ≫ g = (L.distinguished P z.val).hom := by
    simpa only [Category.comp_id] using hz.symm
  let g' : Q ⟶ P := g ≫ (L.distinguished P z.val).inv
  have hfg' : f ≫ g' = 𝟙 P := by
    dsimp only [g']
    rw [← Category.assoc, hfg, Iso.hom_inv_id]
  have hg'f : g' ≫ f = 𝟙 Q := by
    apply L.cancel_right (g' ≫ f) (𝟙 Q) g'
    rw [Category.assoc, hfg', Category.comp_id, Category.id_comp]
  exact ⟨f, g', hfg', hg'f⟩

theorem BLODiagramIsoOfProjection_hom {P Q : L.Object} (f : P ⟶ Q)
    (e : L.projection.obj P ≅ L.projection.obj Q)
    (hf : L.projection.map f = e.hom) :
    (L.BLODiagramIsoOfProjection f e hf).hom = f := rfl

def BLODiagramLiftIso {P Q : L.Object} (e : L.projection.obj P ≅ L.projection.obj Q) :
    P ≅ Q :=
  L.BLODiagramIsoOfProjection
    (Classical.choose (L.projection_surjective P Q e.hom)) e
    (Classical.choose_spec (L.projection_surjective P Q e.hom))

theorem BLODiagramLiftIso_projection {P Q : L.Object}
    (e : L.projection.obj P ≅ L.projection.obj Q) :
    L.projection.map (L.BLODiagramLiftIso e).hom = e.hom := by
  rw [BLODiagramLiftIso, L.BLODiagramIsoOfProjection_hom]
  exact Classical.choose_spec (L.projection_surjective P Q e.hom)

end Sharpness.FusionSystem.CentricLinkingSystem
