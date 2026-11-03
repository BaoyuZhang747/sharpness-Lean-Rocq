import Sharpness.Unconditional.FiniteGroupFusionConjugates

/-! Actual normalizer transports used in the finite-group saturation proof. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
universe u
namespace Sharpness
variable {G : Type u} [Group G]

abbrev finiteGroupAmbientNormalizer (S : Subgroup G) (P : Subgroup S) : Subgroup G :=
  Subgroup.normalizer (finiteGroupAmbientSubgroup S P : Set G)

abbrev finiteGroupNormalizerSubgroup (S : Subgroup G) (P : Subgroup S) :
    Subgroup (finiteGroupAmbientNormalizer S P) :=
  S.subgroupOf (finiteGroupAmbientNormalizer S P)

def finiteGroupNormalizerEquiv (S : Subgroup G) (P : Subgroup S) :
    Subgroup.normalizer (P : Set S) ≃* finiteGroupNormalizerSubgroup S P where
  toFun n := ⟨⟨n.val.val, by
      change n.val ∈ (finiteGroupAmbientNormalizer S P).comap S.subtype
      rw [finiteGroupAmbient_normalizer_comap]
      exact n.property⟩, n.val.property⟩
  invFun n := ⟨⟨n.val.val, n.property⟩, by
      rw [← finiteGroupAmbient_normalizer_comap S P]
      exact n.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

@[simp]
theorem finiteGroupNormalizerEquiv_apply (S : Subgroup G) (P : Subgroup S)
    (n : Subgroup.normalizer (P : Set S)) :
    ((finiteGroupNormalizerEquiv S P n).val : G) = (n.val : G) := rfl

/-- Conjugating a subgroup of N_G(P) into S produces a subgroup of the
normalizer in S of the actual conjugate of P. -/
def finiteGroupConjugatedNormalizerMap (S : Subgroup G) (P : Subgroup S)
    (T : Subgroup (finiteGroupAmbientNormalizer S P)) (g : G)
    (hP : (finiteGroupAmbientSubgroup S P).map (MulAut.conj g).toMonoidHom ≤ S)
    (hT : (T.map (finiteGroupAmbientNormalizer S P).subtype).map
      (MulAut.conj g).toMonoidHom ≤ S) :
    T →* Subgroup.normalizer (finiteGroupConjugate S P g hP : Set S) where
  toFun x := ⟨⟨g*(x.val.val)*g⁻¹, hT ⟨x.val.val, ⟨x.val, x.property, rfl⟩, rfl⟩⟩, by
      rw [← finiteGroupAmbient_normalizer_comap, finiteGroupConjugate_ambient]
      have hn : g*x.val.val*g⁻¹ ∈
          (Subgroup.normalizer (finiteGroupAmbientSubgroup S P : Set G)).map
            (MulAut.conj g).toMonoidHom := ⟨x.val.val, x.val.property, rfl⟩
      rw [Subgroup.map_equiv_normalizer_eq] at hn
      exact hn⟩
  map_one' := by
    apply Subtype.ext
    apply Subtype.ext
    simp
  map_mul' x y := by
    apply Subtype.ext
    apply Subtype.ext
    simp [mul_assoc]

theorem finiteGroupConjugatedNormalizerMap_injective (S : Subgroup G) (P : Subgroup S)
    (T : Subgroup (finiteGroupAmbientNormalizer S P)) (g : G)
    (hP : (finiteGroupAmbientSubgroup S P).map (MulAut.conj g).toMonoidHom ≤ S)
    (hT : (T.map (finiteGroupAmbientNormalizer S P).subtype).map
      (MulAut.conj g).toMonoidHom ≤ S) :
    Function.Injective (finiteGroupConjugatedNormalizerMap S P T g hP hT) := by
  intro x y hxy
  apply Subtype.ext
  apply Subtype.ext
  exact (MulAut.conj g).injective (congrArg (fun z => (z.val : G)) hxy)

end Sharpness
