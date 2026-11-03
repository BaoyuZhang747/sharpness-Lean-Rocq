import Sharpness.SubsystemEmbedding
import Sharpness.DoubleCosetTwist

/-! The double-coset bijection for a subsystem embedding is induced by
the actual group isomorphism from a subgroup to its ambient image. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem
open CategoryTheory
variable {S : Type u} [Group S] (F : FusionSystem S) (T : Subgroup S)
    (H : FusionSystem T) (h : F.SubsystemEmbedding T H)
    {P Q R : H.Object} (f : P ⟶ R) (g : Q ⟶ R)

def subsystemDoubleCosetMap : H.RawDoubleCosetTerm f g →
    F.RawDoubleCosetTerm ((F.subsystemRawFunctor T H h).map f)
      ((F.subsystemRawFunctor T H h).map g) :=
  Quotient.map (subgroupAmbientEquiv T R.subgroup) (by
    intro u v related
    obtain ⟨c, hc, d, hd, hv⟩ := DoubleCoset.rel_iff.mp related
    obtain ⟨a, rfl⟩ := hc
    obtain ⟨b, rfl⟩ := hd
    apply DoubleCoset.rel_iff.mpr
    refine ⟨ambientHom T f.val (subgroupAmbientEquiv T P.subgroup a),
      ⟨subgroupAmbientEquiv T P.subgroup a, rfl⟩,
      ambientHom T g.val (subgroupAmbientEquiv T Q.subgroup b),
      ⟨subgroupAmbientEquiv T Q.subgroup b, rfl⟩, ?_⟩
    rw [ambientHom_apply, ambientHom_apply, hv, map_mul, map_mul]
    rfl)

theorem subsystemDoubleCosetMap_injective :
    Function.Injective (F.subsystemDoubleCosetMap T H h f g) := by
  intro x y
  refine Quotient.inductionOn₂ x y fun u v he => ?_
  apply Quotient.sound
  obtain ⟨c, hc, d, hd, hv⟩ := DoubleCoset.rel_iff.mp (Quotient.exact he)
  obtain ⟨a', rfl⟩ := hc
  obtain ⟨b', rfl⟩ := hd
  obtain ⟨a, rfl⟩ := (subgroupAmbientEquiv T P.subgroup).surjective a'
  obtain ⟨b, rfl⟩ := (subgroupAmbientEquiv T Q.subgroup).surjective b'
  change subgroupAmbientEquiv T R.subgroup v =
    ambientHom T f.val (subgroupAmbientEquiv T P.subgroup a) *
      subgroupAmbientEquiv T R.subgroup u * ambientHom T g.val (subgroupAmbientEquiv T Q.subgroup b) at hv
  rw [ambientHom_apply, ambientHom_apply] at hv
  apply DoubleCoset.rel_iff.mpr
  refine ⟨f.val a, ⟨a, rfl⟩, g.val b, ⟨b, rfl⟩, ?_⟩
  apply (subgroupAmbientEquiv T R.subgroup).injective
  simpa only [map_mul] using hv

theorem subsystemDoubleCosetMap_surjective :
    Function.Surjective (F.subsystemDoubleCosetMap T H h f g) := by
  intro i
  refine Quotient.inductionOn i fun u => ?_
  obtain ⟨v, rfl⟩ := (subgroupAmbientEquiv T R.subgroup).surjective u
  exact ⟨DoubleCoset.mk f.val.range g.val.range v, rfl⟩

def subsystemDoubleCosetEquiv : H.RawDoubleCosetTerm f g ≃
    F.RawDoubleCosetTerm ((F.subsystemRawFunctor T H h).map f)
      ((F.subsystemRawFunctor T H h).map g) :=
  Equiv.ofBijective (F.subsystemDoubleCosetMap T H h f g)
    ⟨F.subsystemDoubleCosetMap_injective T H h f g,
      F.subsystemDoubleCosetMap_surjective T H h f g⟩

end Sharpness.FusionSystem
