import Sharpness.Unconditional.LinkingNormalizerExtension

/-! Exact restrictions and conjugation domains for linking automorphisms. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness.FusionSystem.CentricLinkingSystem
open CategoryTheory
variable {S : Type u} [Group S] [Finite S] {F : FusionSystem S}
    (L : F.CentricLinkingSystem)

/-- Restrict a linking morphism while retaining its actual fusion automorphism. -/
theorem exists_linking_normalizer_restriction {P Q T : L.Object}
    (hPQ : P.as.val ≤ Q.as.val) (hPT : P.as.val ≤ T.as.val)
    (a : F.automorphismSubgroup P.as.val) (b : Q ⟶ T)
    (hb : L.projection.map (L.inclusionLift hPQ ≫ b) =
      (F.isoOfMulEquiv a.val a.property).hom ≫ F.inclusion hPT) :
    ∃ c : Aut P, L.linkingAutProjection P c = a ∧
      L.inclusionLift hPQ ≫ b = c.hom ≫ L.inclusionLift hPT := by
  obtain ⟨c, hc⟩ := L.linkingAutProjection_surjective P a
  have he : L.projection.map c.hom = (F.isoOfMulEquiv a.val a.property).hom := by
    apply Subtype.ext
    apply MonoidHom.ext
    intro x
    exact congrArg (fun z : F.automorphismSubgroup P.as.val => z.val x) hc
  have hp : L.projection.map (c.hom ≫ L.inclusionLift hPT) =
      L.projection.map (L.inclusionLift hPQ ≫ b) := by
    rw [L.projection.map_comp, he, L.projection_inclusionLift, hb]
  obtain ⟨z, hz, _⟩ := (L.central_fiber (c.hom ≫ L.inclusionLift hPT)
    (L.inclusionLift hPQ ≫ b)).mp hp
  refine ⟨(L.distinguished P z.val).trans c, ?_, ?_⟩
  · change L.linkingAutProjection P (c * L.distinguished P z.val) = a
    rw [map_mul, L.distinguished_center_projection, mul_one, hc]
  · exact hz.symm.trans (Category.assoc _ _ _).symm

/-- Conjugation in the linking group agrees with the distinguished action. -/
theorem linkingAut_conjugates_distinguished (P : L.Object) (a : Aut P) (x : P.as.val) :
    a * L.distinguished P x * a⁻¹ =
      L.distinguished P ((L.linkingAutProjection P a).val x) := by
  have h : a * L.distinguished P x =
      L.distinguished P ((L.linkingAutProjection P a).val x) * a := by
    apply Iso.ext
    exact L.commutation a.hom x
  rw [h]
  group

/-- The ambient elements whose linking conjugate is represented in T form
an actual subgroup. This permits a join, without a factorization choice. -/
def linkingNormalizerConjugationDomain (P T : L.Object)
    (hTN : T.as.val ≤ Subgroup.normalizer (P.as.val : Set S)) (a : Aut P) : Subgroup S :=
  ((L.normalizerToLinkingAut P).comp
    (subgroupInclusion T.as.val (Subgroup.normalizer (P.as.val : Set S)) hTN)).range.comap
      ((MulAut.conj a).toMonoidHom.comp (L.normalizerToLinkingAut P)) |>.map
        (Subgroup.normalizer (P.as.val : Set S)).subtype

theorem mem_linkingNormalizerConjugationDomain (P T : L.Object)
    (hTN : T.as.val ≤ Subgroup.normalizer (P.as.val : Set S)) (a : Aut P) (x : S) :
    x ∈ L.linkingNormalizerConjugationDomain P T hTN a ↔
      ∃ hx : x ∈ Subgroup.normalizer (P.as.val : Set S), ∃ y : T.as.val,
        L.normalizerToLinkingAut P ⟨y.val, hTN y.property⟩ =
          a * L.normalizerToLinkingAut P ⟨x, hx⟩ * a⁻¹ := by
  constructor
  · rintro ⟨z, ⟨y, hy⟩, rfl⟩
    exact ⟨z.property, y, hy⟩
  · rintro ⟨hx, y, hy⟩
    exact ⟨⟨x, hx⟩, ⟨y, hy⟩, rfl⟩

theorem le_linkingNormalizerConjugationDomain {P T : L.Object}
    (hPT : P.as.val ≤ T.as.val)
    (hTN : T.as.val ≤ Subgroup.normalizer (P.as.val : Set S)) (a : Aut P) :
    P.as.val ≤ L.linkingNormalizerConjugationDomain P T hTN a := by
  intro x hx
  rw [L.mem_linkingNormalizerConjugationDomain]
  let y := (L.linkingAutProjection P a).val ⟨x, hx⟩
  refine ⟨Subgroup.le_normalizer hx, ⟨y.val, hPT y.property⟩, ?_⟩
  rw [L.normalizerToLinkingAut_of_mem P _ y.property,
    L.normalizerToLinkingAut_of_mem P _ hx]
  exact (L.linkingAut_conjugates_distinguished P a ⟨x, hx⟩).symm

end Sharpness.FusionSystem.CentricLinkingSystem


