import Sharpness.Unconditional.FiniteGroupFusion

/-! Ambient subgroup and conjugate transports for group-induced fusion. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
universe u
namespace Sharpness
variable {G : Type u} [Group G]

@[simp]
theorem finiteGroupAmbientSubgroup_comap (S : Subgroup G) (P : Subgroup S) :
    (finiteGroupAmbientSubgroup S P).comap S.subtype = P :=
  Subgroup.comap_map_eq_self_of_injective Subtype.coe_injective P

theorem finiteGroupAmbient_normalizer_comap (S : Subgroup G) (P : Subgroup S) :
    (Subgroup.normalizer (finiteGroupAmbientSubgroup S P : Set G)).comap S.subtype =
      Subgroup.normalizer (P : Set S) := by
  have h : finiteGroupAmbientSubgroup S P ≤ S.subtype.range := Subgroup.map_le_range _ _
  rw [Subgroup.comap_normalizer_eq_of_le_range (f := S.subtype) h,
    finiteGroupAmbientSubgroup_comap]

/-- The G-conjugate of P, regarded as a subgroup of S whenever it lies in S. -/
def finiteGroupConjugate (S : Subgroup G) (P : Subgroup S) (g : G)
    (_h : (finiteGroupAmbientSubgroup S P).map (MulAut.conj g).toMonoidHom ≤ S) : Subgroup S :=
  ((finiteGroupAmbientSubgroup S P).map (MulAut.conj g).toMonoidHom).subgroupOf S

def finiteGroupConjugateEquiv (S : Subgroup G) (P : Subgroup S) (g : G)
    (h : (finiteGroupAmbientSubgroup S P).map (MulAut.conj g).toMonoidHom ≤ S) :
    P ≃* finiteGroupConjugate S P g h :=
  (finiteGroupAmbientEquiv S P).trans
    (((finiteGroupAmbientSubgroup S P).equivMapOfInjective
      (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).trans
      (Subgroup.subgroupOfEquivOfLe h).symm)

@[simp]
theorem finiteGroupConjugateEquiv_apply (S : Subgroup G) (P : Subgroup S) (g : G)
    (h : (finiteGroupAmbientSubgroup S P).map (MulAut.conj g).toMonoidHom ≤ S) (x : P) :
    ((finiteGroupConjugateEquiv S P g h x).val : G) = g * (x.val : G) * g⁻¹ := rfl

theorem finiteGroupConjugateEquiv_allowed (S : Subgroup G) (P : Subgroup S) (g : G)
    (h : (finiteGroupAmbientSubgroup S P).map (MulAut.conj g).toMonoidHom ≤ S) :
    (finiteGroupFusion S).IsHom (finiteGroupConjugateEquiv S P g h).toMonoidHom :=
  ⟨g, fun _ => rfl⟩

@[simp]
theorem finiteGroupConjugate_ambient (S : Subgroup G) (P : Subgroup S) (g : G)
    (h : (finiteGroupAmbientSubgroup S P).map (MulAut.conj g).toMonoidHom ≤ S) :
    finiteGroupAmbientSubgroup S (finiteGroupConjugate S P g h) =
      (finiteGroupAmbientSubgroup S P).map (MulAut.conj g).toMonoidHom :=
  Subgroup.map_subgroupOf_eq_of_le h

/-- Every p-subgroup of a finite group has an actual conjugate in a chosen Sylow. -/
theorem finiteGroup_pSubgroup_conjugates_into [Finite G] (p : ℕ) [Fact p.Prime]
    (S : Sylow p G) (T : Subgroup G) (hT : IsPGroup p T) :
    ∃ g : G, T.map (MulAut.conj g).toMonoidHom ≤ S := by
  obtain ⟨U, hTU⟩ := hT.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G U S
  refine ⟨g, ?_⟩
  have hg' : (U : Subgroup G).map (MulAut.conj g).toMonoidHom = S := by
    exact congrArg Sylow.toSubgroup hg
  rw [← hg']
  exact Subgroup.map_mono hTU

end Sharpness
