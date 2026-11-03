import Sharpness.LinkingOrbitLifts
import Sharpness.Unconditional.BurnsidePullbackUniqueness

/-! The actual orbit fibres of a centric linking system are torsors for
postcomposition with the distinguished target subgroup. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness.FusionSystem.CentricLinkingSystem
open CategoryTheory
variable {S : Type u} [Group S] {F : FusionSystem S} (L : F.CentricLinkingSystem)

theorem linking_distinguished_stabilizer {P Q : L.Object} (f : P ⟶ Q)
    (z : Q.as.val) (hz : f ≫ (L.distinguished Q z).hom = f) : z = 1 := by
  let φ : P.as.val →* Q.as.val := (L.projection.map f).val
  have hp := congrArg (fun t => L.projection.map t) hz
  rw [L.projection.map_comp, L.project_distinguished] at hp
  have hc : ∀ x, z * φ x = φ x * z := by
    intro x
    have hx := congrArg (fun t => t.val x) hp
    change z⁻¹⁻¹ * φ x * z⁻¹ = φ x at hx
    rw [inv_inv] at hx
    exact (mul_inv_eq_iff_eq_mul).mp hx
  obtain ⟨x, hx⟩ := F.centric_map_centralizer_mem_range P.as.property
    (L.projection.map f) z hc
  have hxc : x ∈ Subgroup.center P.as.val := by
    apply Subgroup.mem_center_iff.mpr
    intro y
    apply F.injective (L.projection.map f).val (L.projection.map f).property
    simp only [map_mul, hx]
    exact (hc y).symm
  let x' : Subgroup.center P.as.val := ⟨x, hxc⟩
  obtain ⟨w, _, hw⟩ := (L.central_fiber f f).mp rfl
  have hxf : (L.distinguished P x'.val).hom ≫ f = f := by
    rw [L.commutation]
    change f ≫ (L.distinguished Q ((L.projection.map f).val x)).hom = f
    rw [hx]
    exact hz
  have h1 : (L.distinguished P (1 : Subgroup.center P.as.val).val).hom ≫ f = f := by
    simp only [Subgroup.coe_one, map_one]
    exact Category.id_comp f
  have hx1 : x' = 1 := (hw x' hxf).trans (hw 1 h1).symm
  have hx1' : x = 1 := congrArg Subtype.val hx1
  simpa only [hx1', map_one] using hx.symm

theorem linking_distinguished_post_injective {P Q : L.Object} (f : P ⟶ Q) :
    Function.Injective (fun z : Q.as.val => f ≫ (L.distinguished Q z).hom) := by
  intro a b hab
  have h : f ≫ (L.distinguished Q (b⁻¹ * a)).hom = f := by
    have hh := congrArg (fun t => t ≫ (L.distinguished Q b).inv) hab
    rw [map_mul, map_inv]
    change f ≫ ((L.distinguished Q a).hom ≫ (L.distinguished Q b).inv) = f
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using hh
  have hone := L.linking_distinguished_stabilizer f (b⁻¹ * a) h
  exact (inv_mul_eq_one.mp hone).symm

theorem linking_orbit_fiber {P Q : L.Object} (f g : P ⟶ Q)
    (hfg : L.orbitProjection.map f = L.orbitProjection.map g) :
    ∃! z : Q.as.val, f ≫ (L.distinguished Q z).hom = g := by
  have ho : F.toOrbit.map (L.projection.map f) = F.toOrbit.map (L.projection.map g) :=
    congrArg (fun t => t.hom) hfg
  obtain ⟨r, hr⟩ := (F.orbit_map_eq_iff _ _).mp ho
  have hp : L.projection.map (f ≫ (L.distinguished Q r⁻¹).hom) = L.projection.map g := by
    rw [L.projection.map_comp, L.project_distinguished]
    apply Subtype.ext
    apply MonoidHom.ext
    intro x
    change r⁻¹⁻¹⁻¹ * (L.projection.map f).val x * r⁻¹⁻¹ = (L.projection.map g).val x
    simpa only [inv_inv] using (hr x).symm
  obtain ⟨z, hz, _⟩ := (L.central_fiber (f ≫ (L.distinguished Q r⁻¹).hom) g).mp hp
  have hout : f ≫ (L.distinguished Q (r⁻¹ * (L.projection.map f).val z.val)).hom = g := by
    rw [map_mul]
    change f ≫ ((L.distinguished Q ((L.projection.map f).val z.val)).hom ≫
      (L.distinguished Q r⁻¹).hom) = g
    rw [← Category.assoc, ← L.commutation f z.val]
    exact (Category.assoc _ _ _).trans hz
  refine ⟨r⁻¹ * (L.projection.map f).val z.val, hout, ?_⟩
  intro w hw
  exact L.linking_distinguished_post_injective f (hw.trans hout.symm)

end Sharpness.FusionSystem.CentricLinkingSystem
