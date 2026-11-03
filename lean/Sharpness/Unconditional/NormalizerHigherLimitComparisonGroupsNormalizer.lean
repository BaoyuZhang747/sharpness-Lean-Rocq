import Sharpness.Unconditional.NormalizerHigherLimitComparisonGroupsStabilizer

/-! The actual simultaneous normalizer of the chain equals the existing
K-normalizer of the top subgroup. Distinguished automorphisms of S admit
unique restrictions to normalized centric subgroups. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness.FusionSystem.CentricChain
variable {S : Type u} [Group S] [Finite S] {F : FusionSystem S}

def normalizerSubgroup (σ : F.CentricChain) : Subgroup S :=
  ⨅ i : Fin (σ.length + 1), Subgroup.normalizer (σ.subgroup i : Set S)

omit [Finite S] in
theorem mem_normalizerSubgroup (σ : F.CentricChain) (s : S) :
    s ∈ σ.normalizerSubgroup ↔ ∀ i, s ∈ Subgroup.normalizer (σ.subgroup i : Set S) :=
  Subgroup.mem_iInf

theorem normalizerSubgroup_eq_kNormalizer (σ : F.CentricChain) :
    σ.normalizerSubgroup = F.kNormalizer σ.topSubgroup σ.fusionStabilizer := by
  ext s
  rw [σ.mem_normalizerSubgroup, F.mem_kNormalizer_iff]
  constructor
  · intro hs
    refine ⟨hs (Fin.last σ.length), ?_⟩
    intro i x
    exact (Subgroup.mem_normalizer_iff.mp (hs i)) x.val
  · rintro ⟨ht, hK⟩ i
    apply Subgroup.mem_normalizer_iff.mpr
    intro x
    constructor
    · intro hx
      exact (hK i ⟨x, σ.subgroup_mono (Fin.le_last i) hx⟩).mp hx
    · intro hx
      have hxt : x ∈ σ.topSubgroup :=
        (Subgroup.mem_normalizer_iff.mp ht x).mpr (σ.subgroup_mono (Fin.le_last i) hx)
      exact (hK i ⟨x, hxt⟩).mpr hx

end Sharpness.FusionSystem.CentricChain

namespace Sharpness.FusionSystem.CentricLinkingSystem
open CategoryTheory
variable {S : Type u} [Group S] [Finite S] {F : FusionSystem S}
    (L : F.CentricLinkingSystem)

def topDistinguished (s : S) : Aut L.topObject :=
  L.distinguished L.topObject ⟨s, Subgroup.mem_top s⟩

theorem topDistinguished_one : L.topDistinguished 1 = 1 :=
  map_one (L.distinguished L.topObject)

theorem topDistinguished_mul (s t : S) : L.topDistinguished (s * t) =
    L.topDistinguished s * L.topDistinguished t := by
  exact map_mul (L.distinguished L.topObject)
    (⟨s, Subgroup.mem_top s⟩ : (⊤ : Subgroup S)) ⟨t, Subgroup.mem_top t⟩

theorem exists_normalizerAut_over_top (P : L.Object)
    (s : Subgroup.normalizer (P.as.val : Set S)) :
    ∃ a : Aut P, a.hom ≫ L.topInclusionLift P =
      L.topInclusionLift P ≫ (L.topDistinguished s.val).hom := by
  let e := F.isoOfMulEquiv (P.as.val.normalizerMonoidHom s) (F.normalizerAut_allowed P.as.val s)
  let a : Aut P := L.normalizerLinkingIsoLift e
  have hp : L.projection.map (a.hom ≫ L.topInclusionLift P) =
      L.projection.map (L.topInclusionLift P ≫ (L.topDistinguished s.val).hom) := by
    rw [L.projection.map_comp, L.projection.map_comp, L.normalizerLinkingIsoLift_projection,
      L.projection_topInclusionLift]
    change e.hom ≫ F.inclusion le_top =
      F.inclusion le_top ≫ L.projection.map (L.distinguished L.topObject _).hom
    rw [L.project_distinguished]
    apply Subtype.ext
    apply MonoidHom.ext
    intro x
    apply Subtype.ext
    change s.val * x.val * s.val⁻¹ = (s.val⁻¹)⁻¹ * x.val * s.val⁻¹
    rw [inv_inv]
  obtain ⟨z, hz, _⟩ := (L.central_fiber (a.hom ≫ L.topInclusionLift P)
    (L.topInclusionLift P ≫ (L.topDistinguished s.val).hom)).mp hp
  exact ⟨(L.distinguished P z.val).trans a, (Category.assoc _ _ _).trans hz⟩

def normalizerAutOverTop (P : L.Object) (s : Subgroup.normalizer (P.as.val : Set S)) : Aut P :=
  Classical.choose (L.exists_normalizerAut_over_top P s)

theorem normalizerAutOverTop_square (P : L.Object)
    (s : Subgroup.normalizer (P.as.val : Set S)) :
    (L.normalizerAutOverTop P s).hom ≫ L.topInclusionLift P =
      L.topInclusionLift P ≫ (L.topDistinguished s.val).hom :=
  Classical.choose_spec (L.exists_normalizerAut_over_top P s)

theorem normalizerAutOverTop_unique (P : L.Object)
    (s : Subgroup.normalizer (P.as.val : Set S)) (a : Aut P)
    (ha : a.hom ≫ L.topInclusionLift P =
      L.topInclusionLift P ≫ (L.topDistinguished s.val).hom) :
    a = L.normalizerAutOverTop P s := by
  apply Iso.ext
  exact L.cancel_right _ _ (L.topInclusionLift P)
    (ha.trans (L.normalizerAutOverTop_square P s).symm)

/-- A genuine group homomorphism, with coherence supplied by uniqueness. -/
def normalizerToLinkingAut (P : L.Object) :
    Subgroup.normalizer (P.as.val : Set S) →* Aut P where
  toFun := L.normalizerAutOverTop P
  map_one' := by
    symm
    apply L.normalizerAutOverTop_unique
    rw [Subgroup.coe_one, L.topDistinguished_one]
    change 𝟙 P ≫ _ = _ ≫ 𝟙 L.topObject
    simp only [Category.id_comp, Category.comp_id]
  map_mul' s t := by
    symm
    apply L.normalizerAutOverTop_unique
    change ((L.normalizerAutOverTop P t).hom ≫ (L.normalizerAutOverTop P s).hom) ≫ _ = _
    rw [Category.assoc, L.normalizerAutOverTop_square, ← Category.assoc,
      L.normalizerAutOverTop_square, Category.assoc]
    rw [Subgroup.coe_mul, L.topDistinguished_mul]
    rfl

theorem normalizerToLinkingAut_projection (P : L.Object)
    (s : Subgroup.normalizer (P.as.val : Set S)) :
    L.linkingAutProjection P (L.normalizerToLinkingAut P s) = F.kNormalizerAction P.as.val s := by
  have h := congrArg (fun f => L.projection.map f) (L.normalizerAutOverTop_square P s)
  rw [L.projection.map_comp, L.projection.map_comp, L.projection_topInclusionLift] at h
  change L.projection.map (L.normalizerAutOverTop P s).hom ≫ F.inclusion le_top =
    F.inclusion le_top ≫ L.projection.map (L.distinguished L.topObject _).hom at h
  rw [L.project_distinguished] at h
  apply Subtype.ext
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  have hx := congrArg (fun f => (f.val x).val) h
  change ((L.projection.map (L.normalizerAutOverTop P s).hom).val x).val =
    (s.val⁻¹)⁻¹ * x.val * s.val⁻¹ at hx
  change ((L.projection.map (L.normalizerAutOverTop P s).hom).val x).val =
    s.val * x.val * s.val⁻¹
  simpa only [inv_inv] using hx

theorem normalizerToLinkingAut_of_mem (P : L.Object)
    (s : Subgroup.normalizer (P.as.val : Set S)) (hs : s.val ∈ P.as.val) :
    L.normalizerToLinkingAut P s = L.distinguished P ⟨s.val, hs⟩ := by
  symm
  apply L.normalizerAutOverTop_unique
  have h := L.commutation (L.topInclusionLift P) ⟨s.val, hs⟩
  rw [L.projection_topInclusionLift] at h
  exact h

theorem normalizerToLinkingAut_injective (P : L.Object) :
    Function.Injective (L.normalizerToLinkingAut P) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro s hs
  have hs' : L.normalizerToLinkingAut P s = 1 := hs
  have hp := congrArg (L.linkingAutProjection P) hs'
  rw [L.normalizerToLinkingAut_projection, map_one] at hp
  have hc : s.val ∈ Subgroup.centralizer (P.as.val : Set S) := by
    apply Subgroup.mem_centralizer_iff.mpr
    intro x hx
    have h := congrArg (fun a : F.automorphismSubgroup P.as.val => (a.val ⟨x, hx⟩).val) hp
    change s.val * x * s.val⁻¹ = x at h
    calc
      x * s.val = (s.val * x * s.val⁻¹) * s.val := by rw [h]
      _ = s.val * x := by group
  have hcent : Subgroup.centralizer (P.as.val : Set S) ≤ P.as.val := by
    have h := P.as.property P.as.val le_top (MulEquiv.refl P.as.val) (F.id_mem P.as.val)
    simpa only [inf_top_eq] using h
  have hsP := hcent hc
  rw [L.normalizerToLinkingAut_of_mem P s hsP] at hs'
  have he := L.distinguished_injective P (hs'.trans (map_one (L.distinguished P)).symm)
  change s = 1
  apply Subtype.ext
  exact congrArg (fun x : P.as.val => x.val) he

end Sharpness.FusionSystem.CentricLinkingSystem
