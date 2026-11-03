import Sharpness.Unconditional.NormalizerHigherLimitComparisonLocalLimitMaps

/-! The actual same-chain category limit has the actual group-cohomology
restriction map at every object, without choosing an abstract fibre model. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness.FusionSystem.CentricLinkingSystem
open CategoryTheory CategoryTheory.Limits Opposite
variable {S R A : Type u} [Group S] [Finite S] [CommRing R]
    [AddCommGroup A] [Module R A] {F : FusionSystem S}
    (L : F.CentricLinkingSystem)

def normalizerAtChainGroupHom (σ : F.CentricChain) (P : F.NormalizerOrbitAtChain σ) :
    P.obj.centric.obj.as.subgroup →* L.ChainAut σ := by
  have hN : P.obj.centric.obj.as.subgroup ≤ σ.normalizerSubgroup := by
    intro x hx
    apply (σ.mem_normalizerSubgroup x).mpr
    intro i
    have hn := P.obj.normalizes
    rw [P.property] at hn
    exact hn i hx
  exact (L.chainNormalizerToAut σ).comp (subgroupInclusion _ _ hN)

variable (p : ℕ) [Fact p.Prime] (hS : IsPGroup p S) (sat : F.Saturated p)
    (σ : F.CentricChain) (hindex : IsUnit ((L.chainNormalizerToAut σ).range.index : R))

theorem normalizerAtChainGroupHom_local (P : (L.normalizerAmbientCollection p hS sat σ).Orbit) :
    L.normalizerAtChainGroupHom σ ((L.normalizerLocalToPair p hS sat σ).obj P) =
      L.normalizerAmbientGroupHom p hS sat σ P := by
  apply MonoidHom.ext
  intro x
  apply congrArg (L.chainNormalizerToAut σ)
  apply Subtype.ext
  exact (subgroupAmbientEquiv_symm_val σ.normalizerSubgroup P.obj.as.subgroup x).symm

def normalizerAtChainLimitIso (n : ℕ) :
    limit (F.normalizerAtChainCohomologyCoefficient R A σ n) ≅
      OrdinaryCohomology.value R (L.ChainAut σ) A n :=
  asIso (limit.pre (F.normalizerAtChainCohomologyCoefficient R A σ n)
    (L.normalizerLocalPairEquivalence p hS sat σ).functor.op) ≪≫
  L.normalizerAmbientLimitIso p hS sat σ hindex n

theorem normalizerAtChainLimitIso_hom_pull_local (n : ℕ)
    (P : (L.normalizerAmbientCollection p hS sat σ).Orbit) :
    (L.normalizerAtChainLimitIso (R := R) (A := A) p hS sat σ hindex n).hom ≫
      OrdinaryCohomology.pull (L.normalizerAmbientGroupHom p hS sat σ P) n =
      limit.π (F.normalizerAtChainCohomologyCoefficient R A σ n)
        (op ((L.normalizerLocalToPair p hS sat σ).obj P)) := by
  simp only [normalizerAtChainLimitIso, Iso.trans_hom, asIso_hom, Category.assoc]
  rw [L.normalizerAmbientLimitIso_hom_pull]
  exact limit.pre_π _ _ _

theorem normalizerAtChainLimitIso_hom_pull (n : ℕ) (P : F.NormalizerOrbitAtChain σ) :
    (L.normalizerAtChainLimitIso (R := R) (A := A) p hS sat σ hindex n).hom ≫
      OrdinaryCohomology.pull (L.normalizerAtChainGroupHom σ P) n =
      limit.π (F.normalizerAtChainCohomologyCoefficient R A σ n) (op P) := by
  obtain ⟨Q, rfl⟩ := L.normalizerLocalToPair_obj_surjective p hS sat σ P
  rw [L.normalizerAtChainGroupHom_local p hS sat σ]
  exact L.normalizerAtChainLimitIso_hom_pull_local p hS sat σ hindex n Q

theorem normalizerAtChainLimitIso_inv_component (n : ℕ) (P : F.NormalizerOrbitAtChain σ) :
    (L.normalizerAtChainLimitIso (R := R) (A := A) p hS sat σ hindex n).inv ≫
      limit.π (F.normalizerAtChainCohomologyCoefficient R A σ n) (op P) =
      OrdinaryCohomology.pull (L.normalizerAtChainGroupHom σ P) n := by
  rw [← L.normalizerAtChainLimitIso_hom_pull p hS sat σ hindex n P, Iso.inv_hom_id_assoc]

variable (k : Type u) [Field k] [CharP k p]
    {B : Type u} [AddCommGroup B] [Module k B]

def normalizerRepresentativeAtChainLimitIso (d : F.NormalizerCategory) (n : ℕ) :
    limit (F.normalizerAtChainCohomologyCoefficient k B
      (L.normalizerSylowRepresentative p hS sat d) n) ≅
        OrdinaryCohomology.value k (L.ChainAut (L.normalizerSylowRepresentative p hS sat d)) B n :=
  L.normalizerAtChainLimitIso p hS sat (L.normalizerSylowRepresentative p hS sat d)
    (L.normalizerRepresentativeIndexIsUnit p hS sat k d) n

theorem normalizerRepresentativeAtChainLimitIso_inv_component (d : F.NormalizerCategory) (n : ℕ)
    (P : F.NormalizerOrbitAtChain (L.normalizerSylowRepresentative p hS sat d)) :
    (L.normalizerRepresentativeAtChainLimitIso (B := B) p hS sat k d n).inv ≫
      limit.π (F.normalizerAtChainCohomologyCoefficient k B
        (L.normalizerSylowRepresentative p hS sat d) n) (op P) =
      OrdinaryCohomology.pull
        (L.normalizerAtChainGroupHom (L.normalizerSylowRepresentative p hS sat d) P) n :=
  L.normalizerAtChainLimitIso_inv_component p hS sat _ _ n P

end Sharpness.FusionSystem.CentricLinkingSystem
