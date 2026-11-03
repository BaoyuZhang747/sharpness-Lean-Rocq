import Sharpness.Radical

/-! The literal outer-automorphism and p-core formulation of radicality.

The inner subgroup is the image of conjugation by elements of P itself.
It is the kernel of the existing homomorphism to automorphisms in the orbit
category. The finite-group p-core is constructed as the join of all normal
p-subgroups, and is proved to be a normal p-subgroup.
-/
set_option autoImplicit false
noncomputable section
universe u

namespace Sharpness.V28

variable (p : ℕ) (G : Type u) [Group G]

/-- The join of all normal p-subgroups. For finite G it is itself a p-group. -/
def normalPCore : Subgroup G :=
  ⨆ N : {N : Subgroup G // N.Normal ∧ IsPGroup p N}, N.val

instance normalPCore_normal : (normalPCore p G).Normal := by
  letI : ∀ N : {N : Subgroup G // N.Normal ∧ IsPGroup p N}, N.val.Normal :=
    fun N => N.property.1
  exact Subgroup.iSup_normal _

theorem le_normalPCore (N : Subgroup G) (hN : N.Normal) (hp : IsPGroup p N) :
    N ≤ normalPCore p G :=
  le_iSup (fun M : {M : Subgroup G // M.Normal ∧ IsPGroup p M} => M.val) ⟨N, hN, hp⟩

theorem normalPCore_isPGroup [Finite G] : IsPGroup p (normalPCore p G) := by
  classical
  let I := {N : Subgroup G // N.Normal ∧ IsPGroup p N}
  letI := Fintype.ofFinite I
  have hfinite : ∀ s : Finset I, IsPGroup p (s.sup (fun N => N.val) : Subgroup G) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      rw [Finset.sup_empty]
      exact IsPGroup.of_bot
    | @insert N s _ ih =>
      letI : N.val.Normal := N.property.1
      rw [Finset.sup_insert]
      exact N.property.2.to_sup_of_normal_left ih
  have heq : (Finset.univ.sup (fun N : I => N.val) : Subgroup G) = normalPCore p G := by
    rw [Finset.sup_eq_iSup]
    simp only [Finset.mem_univ, iSup_pos, normalPCore]
    rfl
  exact heq ▸ hfinite Finset.univ

theorem normalPCore_eq_bot_iff :
    normalPCore p G = ⊥ ↔ HasTrivialNormalPSubgroups p G := by
  constructor
  · intro h N hN hp
    exact le_antisymm (h ▸ le_normalPCore p G N hN hp) bot_le
  · intro h
    apply le_antisymm _ bot_le
    exact iSup_le fun N => (h N.val N.property.1 N.property.2).le

end Sharpness.V28

namespace Sharpness.FusionSystem.V28
open CategoryTheory
variable {S : Type u} [Group S] (F : FusionSystem S)

/-- Conjugation by P, with codomain the fusion automorphism group of P. -/
def innerAutomorphismHom (P : Subgroup S) : P →* F.automorphismSubgroup P :=
  (MulAut.conj : P →* MulAut P).codRestrict (F.automorphismSubgroup P) (by
    intro r
    change F.IsHom (MulAut.conj r).toMonoidHom
    convert F.normalizerAut_allowed P ⟨r.val, Subgroup.le_normalizer r.property⟩ using 1
    ext x
    rfl)

/-- The actual inner automorphism subgroup Inn(P) inside Aut_F(P). -/
def innerAutomorphismSubgroup (P : Subgroup S) : Subgroup (F.automorphismSubgroup P) :=
  (innerAutomorphismHom F P).range

theorem innerAutomorphismSubgroup_eq_ker (P : Subgroup S) :
    innerAutomorphismSubgroup F P = (F.automorphismToOrbitAut P).ker := by
  ext a
  constructor
  · rintro ⟨r, rfl⟩
    change F.automorphismToOrbitAut P (innerAutomorphismHom F P r) = 1
    apply Iso.ext
    change F.toOrbit.map _ = 𝟙 _
    convert F.inner_orbit_eq_id (⟨P⟩ : F.Object) r⁻¹ using 1
    congr 1
    apply Subtype.ext
    ext x
    change r.val * x.val * r.val⁻¹ = (r.val⁻¹)⁻¹ * x.val * r.val⁻¹
    rw [inv_inv]
  · intro ha
    change F.automorphismToOrbitAut P a = 1 at ha
    have he : F.toOrbit.map (F.isoOfMulEquiv a.val a.property).hom =
        F.toOrbit.map (𝟙 (⟨P⟩ : F.Object)) := by
      calc
        F.toOrbit.map (F.isoOfMulEquiv a.val a.property).hom =
            (1 : Aut (F.toOrbit.obj ⟨P⟩)).hom := congrArg Iso.hom ha
        _ = F.toOrbit.map (𝟙 (⟨P⟩ : F.Object)) := (F.toOrbit.map_id _).symm
    obtain ⟨r, hr⟩ := (F.orbit_map_eq_iff _ _).mp he
    refine ⟨r, ?_⟩
    apply Subtype.ext
    apply MulEquiv.ext
    intro x
    change r * x * r⁻¹ = a.val x
    have hx := hr x
    change x = r⁻¹ * a.val x * r at hx
    calc
      r * x * r⁻¹ = r * (r⁻¹ * a.val x * r) * r⁻¹ := by rw [← hx]
      _ = a.val x := by simp [mul_assoc]

instance innerAutomorphismSubgroup_normal (P : Subgroup S) :
    (innerAutomorphismSubgroup F P).Normal := by
  rw [innerAutomorphismSubgroup_eq_ker]
  infer_instance

/-- The orbit automorphism group is Aut_F(P)/Inn(P), with its group law. -/
def outerAutomorphismEquivOrbitAut [Finite S] (P : Subgroup S) :
    (F.automorphismSubgroup P ⧸ innerAutomorphismSubgroup F P) ≃*
      Aut (F.toOrbit.obj ⟨P⟩) :=
  (QuotientGroup.quotientMulEquivOfEq (innerAutomorphismSubgroup_eq_ker F P)).trans
    (QuotientGroup.quotientKerEquivOfSurjective (F.automorphismToOrbitAut P)
      (F.automorphismToOrbitAut_surjective P))

theorem outerAutomorphismEquivOrbitAut_mk [Finite S] (P : Subgroup S)
    (a : F.automorphismSubgroup P) :
    outerAutomorphismEquivOrbitAut F P (QuotientGroup.mk a) =
      F.automorphismToOrbitAut P a := rfl

/-- Agreement with the manuscript's O_p(Out_F(P)) = 1 definition. -/
theorem isRadical_iff_normalPCore_eq_bot [Finite S] (p : ℕ) (P : Subgroup S) :
    F.IsRadical p P ↔ Sharpness.V28.normalPCore p
      (F.automorphismSubgroup P ⧸ innerAutomorphismSubgroup F P) = ⊥ := by
  rw [Sharpness.V28.normalPCore_eq_bot_iff]
  exact ⟨HasTrivialNormalPSubgroups.of_mulEquiv (outerAutomorphismEquivOrbitAut F P).symm,
    HasTrivialNormalPSubgroups.of_mulEquiv (outerAutomorphismEquivOrbitAut F P)⟩

end Sharpness.FusionSystem.V28
