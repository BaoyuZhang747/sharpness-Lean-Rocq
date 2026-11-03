import Sharpness.SubsystemMackey

/-! The actual inclusion into the ambient centric orbit category, and the
restricted full Mackey coefficient comparison. The centric inclusion is
the hypothesis of manuscript Lemma 3.6, supplied by Yalcin 8.11 later. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem
open CategoryTheory CategoryTheory.Limits
variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S) (T : Subgroup S)
    (H : FusionSystem T) (h : F.SubsystemEmbedding T H)

theorem subsystemRaw_reflects_inner {P Q : H.Object} (f g : P ⟶ Q)
    (same : (F.subsystemRawFunctor T H h ⋙ F.toOrbit).map f =
      (F.subsystemRawFunctor T H h ⋙ F.toOrbit).map g) : H.targetInner f g := by
  obtain ⟨r', hr⟩ := (F.orbit_map_eq_iff _ _).mp same
  obtain ⟨r, rfl⟩ := (subgroupAmbientEquiv T Q.subgroup).surjective r'
  refine ⟨r, ?_⟩
  intro x
  apply (subgroupAmbientEquiv T Q.subgroup).injective
  have he := hr (subgroupAmbientEquiv T P.subgroup x)
  change ambientHom T g.val (subgroupAmbientEquiv T P.subgroup x) =
    (subgroupAmbientEquiv T Q.subgroup r)⁻¹ *
      ambientHom T f.val (subgroupAmbientEquiv T P.subgroup x) * subgroupAmbientEquiv T Q.subgroup r at he
  rw [ambientHom_apply, ambientHom_apply] at he
  simpa only [map_mul, map_inv] using he

instance subsystemOrbitFunctor_faithful : (F.subsystemOrbitFunctor T H h).Faithful where
  map_injective := by
    rintro ⟨P⟩ ⟨Q⟩ f g same
    obtain ⟨f₀, rfl⟩ := H.toOrbit.map_surjective f
    obtain ⟨g₀, rfl⟩ := H.toOrbit.map_surjective g
    exact (H.orbit_map_eq_iff _ _).mpr (F.subsystemRaw_reflects_inner T H h f₀ g₀ same)

variable (centric : ∀ P : Subgroup T, H.IsCentric P → F.IsCentric (ambientSubgroup T P))

def subsystemCentricFunctor : H.CentricOrbit ⥤ F.CentricOrbit where
  obj P := ⟨(F.subsystemOrbitFunctor T H h).obj P.obj, centric P.obj.as.subgroup P.property⟩
  map f := ObjectProperty.homMk ((F.subsystemOrbitFunctor T H h).map f.hom)
  map_id P := by
    apply InducedCategory.hom_ext
    exact (F.subsystemOrbitFunctor T H h).map_id P.obj
  map_comp f g := by
    apply InducedCategory.hom_ext
    exact (F.subsystemOrbitFunctor T H h).map_comp f.hom g.hom

variable {k : Type u} [CommRing k] (M : MackeyModule.{u,u,u} k F.Orbit F.mackeyShape)

def subsystemCentricCoefficientIso : H.centricCoefficient (F.subsystemMackey T H h M) ≅
    (F.subsystemCentricFunctor T H h centric).op ⋙ F.centricCoefficient M :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)

theorem subsystemCoefficient_acyclic_of_sharp
    [EnoughProjectives (CoefficientCategory k H.CentricOrbit)] (sharp : H.Sharp (R := k)) :
    Acyclic ((F.subsystemCentricFunctor T H h centric).op ⋙ F.centricCoefficient M) :=
  acyclic_of_iso (F.subsystemCentricCoefficientIso T H h centric M).symm
    (sharp (F.subsystemMackey T H h M))

end Sharpness.FusionSystem
