import Sharpness.ReferenceInputs
import Sharpness.GroupTrace

set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem
open CategoryTheory
open scoped BigOperators
variable {S : Type u} [Group S] (F : FusionSystem S)

def isoOfMulEquiv {P Q : Subgroup S} (e : P ≃* Q)
    (he : F.IsHom e.toMonoidHom) : (⟨P⟩ : F.Object) ≅ ⟨Q⟩ where
  hom := ⟨e.toMonoidHom, he⟩
  inv := ⟨e.symm.toMonoidHom, F.inverse_mem e he⟩
  hom_inv_id := by apply Subtype.ext; ext x; exact congrArg Subtype.val (e.symm_apply_apply x)
  inv_hom_id := by apply Subtype.ext; ext x; exact congrArg Subtype.val (e.apply_symm_apply x)

theorem normalizerAut_allowed (L : Subgroup S) (u : Subgroup.normalizer (L : Set S)) :
    F.IsHom (L.normalizerMonoidHom u).toMonoidHom := by
  have h : ∀ x ∈ L, (u.val⁻¹)⁻¹ * x * u.val⁻¹ ∈ L := by
    intro x hx
    rw [inv_inv]
    exact (u.property x).mp hx
  convert F.conjugation_mem L L u.val⁻¹ h using 1
  ext x
  simp [subgroupConjugation]

def normalizerToOrbitAut (L : Subgroup S) :
    Subgroup.normalizer (L : Set S) →* Aut (F.toOrbit.obj ⟨L⟩) where
  toFun u := F.toOrbit.mapIso (F.isoOfMulEquiv (L.normalizerMonoidHom u)
    (F.normalizerAut_allowed L u))
  map_one' := by
    apply Iso.ext
    change F.toOrbit.map _ = 𝟙 _
    rw [← F.toOrbit.map_id]
    congr 1
    apply Subtype.ext
    ext x
    change (1 : S) * x.val * (1 : S)⁻¹ = x.val
    simp
  map_mul' a b := by
    apply Iso.ext
    change F.toOrbit.map _ = F.toOrbit.map _ ≫ F.toOrbit.map _
    rw [← F.toOrbit.map_comp]
    congr 1
    apply Subtype.ext
    ext x
    change (a.val * b.val) * x.val * (a.val * b.val)⁻¹ =
      a.val * (b.val * x.val * b.val⁻¹) * a.val⁻¹
    simp [mul_assoc]

def relativeNormalizer (_F : FusionSystem S) (T L : Subgroup S) :=
  Subgroup.normalizer (L : Set S) ⊓ T

instance normal_in_relativeNormalizer (T L : Subgroup S) :
    (L.subgroupOf (F.relativeNormalizer T L)).Normal :=
  Subgroup.normal_subgroupOf_of_le_normalizer inf_le_left

def relativeNormalizerToAut (T L : Subgroup S) :
    F.relativeNormalizer T L →* Aut (F.toOrbit.obj ⟨L⟩) :=
  (F.normalizerToOrbitAut L).comp (Subgroup.inclusion inf_le_left)

theorem subgroup_killed_by_normalizerAut (T L : Subgroup S) :
    L.subgroupOf (F.relativeNormalizer T L) ≤ (F.relativeNormalizerToAut T L).ker := by
  intro x hx
  change F.relativeNormalizerToAut T L x = 1
  apply Iso.ext
  change F.toOrbit.map _ = 𝟙 _
  have hinner := F.inner_orbit_eq_id (⟨L⟩ : F.Object) (⟨x.val, hx⟩⁻¹)
  convert hinner using 1
  congr 1
  apply Subtype.ext
  ext y
  change x.val * y.val * x.val⁻¹ = (x.val⁻¹)⁻¹ * y.val * x.val⁻¹
  rw [inv_inv]

abbrev NormalizerQuotient (T L : Subgroup S) :=
  F.relativeNormalizer T L ⧸ L.subgroupOf (F.relativeNormalizer T L)

def normalizerQuotientToAut (T L : Subgroup S) :
    F.NormalizerQuotient T L →* Aut (F.toOrbit.obj ⟨L⟩) :=
  QuotientGroup.lift _ (F.relativeNormalizerToAut T L)
    (F.subgroup_killed_by_normalizerAut T L)

theorem centralizer_killed (T L : Subgroup S)
    (c : F.relativeNormalizer T L) (hc : c.val ∈ Subgroup.centralizer (L : Set S)) :
    F.relativeNormalizerToAut T L c = 1 := by
  apply Iso.ext
  change F.toOrbit.map _ = 𝟙 _
  rw [← F.toOrbit.map_id]
  congr 1
  apply Subtype.ext
  ext x
  change c.val * x.val * c.val⁻¹ = x.val
  have h := (Subgroup.mem_centralizer_iff.mp hc) x.val x.property
  rw [← h, mul_assoc, mul_inv_cancel, mul_one]

variable [Finite S] {k : Type u} [Field k]
    (M : MackeyModule.{u,u,u} k F.Orbit F.mackeyShape)

def normalizerTrace (T L : Subgroup S) :
    M.Value (F.toOrbit.obj ⟨L⟩) →ₗ[k] M.Value (F.toOrbit.obj ⟨L⟩) :=
  letI : Fintype (F.NormalizerQuotient T L) := Fintype.ofFinite _
  ∑ a : F.NormalizerQuotient T L, M.push (F.normalizerQuotientToAut T L a).hom

theorem normalizerTrace_zero (p : ℕ) [Fact p.Prime] [CharP k p]
    (hS : IsPGroup p S) (T L : Subgroup S)
    (bad : ¬ Subgroup.centralizer (L : Set S) ⊓ T ≤ L) :
    F.normalizerTrace M T L = 0 := by
  classical
  have witness : ∃ c : S, c ∈ Subgroup.centralizer (L : Set S) ⊓ T ∧ c ∉ L := by
    simpa only [SetLike.not_le_iff_exists] using bad
  obtain ⟨c, hc, hcL⟩ := witness
  let cN : F.relativeNormalizer T L :=
    ⟨c, Subgroup.centralizer_le_normalizer _ hc.1, hc.2⟩
  let a : F.NormalizerQuotient T L := QuotientGroup.mk cN
  have ha : a ≠ 1 := by
    intro h
    exact hcL ((QuotientGroup.eq_one_iff cN).mp h)
  let ρ : F.NormalizerQuotient T L →* Module.End k (M.Value (F.toOrbit.obj ⟨L⟩)) :=
    (M.automorphismAction _).comp (F.normalizerQuotientToAut T L)
  have hρ : ρ a = 1 := by
    change M.automorphismAction _ (F.relativeNormalizerToAut T L cN) = 1
    rw [F.centralizer_killed T L cN hc.1, map_one]
  apply LinearMap.ext
  intro x
  have hp : IsPGroup p (F.NormalizerQuotient T L) :=
    (hS.to_subgroup (F.relativeNormalizer T L)).to_quotient _
  simp only [normalizerTrace, LinearMap.sum_apply, LinearMap.zero_apply]
  exact group_trace_zero_of_kernel p hp ρ a ha hρ x

end Sharpness.FusionSystem
