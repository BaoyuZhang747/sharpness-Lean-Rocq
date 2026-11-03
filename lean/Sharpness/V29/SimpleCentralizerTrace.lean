import Sharpness.V29.SimpleFunctor

/-! The intermediate subgroup in the Grazian–Marmo trace argument.
We first prove transitivity of finite group traces through an arbitrary
subgroup, then use the image of `L C_U(L)` in `N_U(L)/L`. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v w

namespace Sharpness
open scoped BigOperators

/-- Coset coordinates with a literal multiplication formula for the
inverse, used to expose transitivity of traces. -/
def traceCosetEquiv {G : Type v} [Group G] (K : Subgroup G) : G ≃ (G ⧸ K) × K where
  toFun g := ⟨QuotientGroup.mk g,
    ⟨(Quotient.out (QuotientGroup.mk g : G ⧸ K))⁻¹ * g,
      QuotientGroup.eq.mp (Quotient.out_eq _)⟩⟩
  invFun qa := qa.1.out * qa.2.val
  left_inv g := by simp
  right_inv qa := by
    obtain ⟨q, a⟩ := qa
    apply Prod.ext
    · exact (QuotientGroup.mk_mul_of_mem q.out a.property).trans (Quotient.out_eq q)
    · apply Subtype.ext
      change (Quotient.out (QuotientGroup.mk (q.out * a.val) : G ⧸ K))⁻¹ *
        (q.out * a.val) = a.val
      rw [QuotientGroup.mk_mul_of_mem q.out a.property, QuotientGroup.out_eq']
      simp

theorem finite_trace_transitivity
    {k : Type u} [Field k] {G : Type v} [Group G] [Finite G]
    {V : Type w} [AddCommGroup V] [Module k V]
    (ρ : G →* Module.End k V) (K : Subgroup G) (x : V) :
    letI : Fintype G := Fintype.ofFinite G
    letI : Fintype K := Fintype.ofFinite K
    letI : Fintype (G ⧸ K) := Fintype.ofFinite _
    (∑ g : G, ρ g x) =
      ∑ q : G ⧸ K, ρ q.out (∑ a : K, ρ a.val x) := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  letI : Fintype K := Fintype.ofFinite K
  letI : Fintype (G ⧸ K) := Fintype.ofFinite _
  let e : G ≃ (G ⧸ K) × K := traceCosetEquiv K
  calc
    (∑ g : G, ρ g x) = ∑ qa : (G ⧸ K) × K, ρ (e.symm qa) x :=
      (e.symm.sum_comp (fun g => ρ g x)).symm
    _ = ∑ q : G ⧸ K, ρ q.out (∑ a : K, ρ a.val x) := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro q _
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro a _
      have he : e.symm (q, a) = q.out * a.val := rfl
      rw [he]
      rw [map_mul]
      rfl

/-- The intermediate trace is the subgroup's cardinal scalar when its
action is trivial. No characteristic assumption is used here. -/
theorem finite_trace_trivial_action
    {k : Type u} [Field k] {G : Type v} [Group G] [Finite G]
    {V : Type w} [AddCommGroup V] [Module k V]
    (ρ : G →* Module.End k V) (K : Subgroup G) (hK : K ≤ ρ.ker) (x : V) :
    letI : Fintype K := Fintype.ofFinite K
    (∑ a : K, ρ a.val x) = (Nat.card K : k) • x := by
  classical
  letI : Fintype K := Fintype.ofFinite K
  have ha (a : K) : ρ a.val x = x := by rw [hK a.property]; rfl
  simp only [ha, Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card,
    Nat.cast_smul_eq_nsmul]

end Sharpness

namespace Sharpness.FusionSystem
open CategoryTheory
open scoped BigOperators

variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)

/-- The subgroup `L C_U(L)`, expressed as the join of the commuting factors. -/
def simpleCentralizerIntermediate (_F : FusionSystem S) (U L : Subgroup S) : Subgroup S :=
  L ⊔ (Subgroup.centralizer (L : Set S) ⊓ U)

theorem simpleCentralizerIntermediate_le {U L : Subgroup S} (hLU : L ≤ U) :
    F.simpleCentralizerIntermediate U L ≤ F.relativeNormalizer U L := by
  apply sup_le
  · exact le_inf L.le_normalizer hLU
  · exact le_inf (inf_le_left.trans (Subgroup.centralizer_le_normalizer _)) inf_le_right

def SimpleCentralizerQuotient (U L : Subgroup S) : Subgroup (F.NormalizerQuotient U L) :=
  ((F.simpleCentralizerIntermediate U L).subgroupOf (F.relativeNormalizer U L)).map
    (QuotientGroup.mk' (L.subgroupOf (F.relativeNormalizer U L)))

/-- Projection from the literal intermediate subgroup to the normalizer
quotient. Its kernel and range identify the intermediate trace's index. -/
def simpleIntermediateProjection {U L : Subgroup S} (hLU : L ≤ U) :
    F.simpleCentralizerIntermediate U L →* F.NormalizerQuotient U L :=
  (QuotientGroup.mk' (L.subgroupOf (F.relativeNormalizer U L))).comp
    (Subgroup.inclusion (F.simpleCentralizerIntermediate_le hLU))

theorem simpleIntermediateProjection_ker {U L : Subgroup S} (hLU : L ≤ U) :
    (F.simpleIntermediateProjection hLU).ker =
      L.subgroupOf (F.simpleCentralizerIntermediate U L) := by
  ext x
  change (QuotientGroup.mk
    (⟨x.val, F.simpleCentralizerIntermediate_le hLU x.property⟩ : F.relativeNormalizer U L) = 1) ↔
      x.val ∈ L
  exact QuotientGroup.eq_one_iff _

theorem simpleIntermediateProjection_range {U L : Subgroup S} (hLU : L ≤ U) :
    (F.simpleIntermediateProjection hLU).range = F.SimpleCentralizerQuotient U L := by
  ext a
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨⟨x.val, F.simpleCentralizerIntermediate_le hLU x.property⟩, x.property, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x.val, hx⟩, rfl⟩

theorem simpleCentralizerQuotient_card_index {U L : Subgroup S} (hLU : L ≤ U) :
    Nat.card (F.SimpleCentralizerQuotient U L) =
      (L.subgroupOf (F.simpleCentralizerIntermediate U L)).index := by
  have h := Subgroup.index_ker (F.simpleIntermediateProjection hLU)
  rw [F.simpleIntermediateProjection_ker hLU,
    F.simpleIntermediateProjection_range hLU] at h
  exact h.symm

theorem simpleCentralizerIntermediate_killed {U L : Subgroup S} (hLU : L ≤ U) :
    (F.simpleCentralizerIntermediate U L).subgroupOf (F.relativeNormalizer U L) ≤
      (F.relativeNormalizerToAut U L).ker := by
  have hker : F.simpleCentralizerIntermediate U L ≤
      ((F.relativeNormalizerToAut U L).ker.map (F.relativeNormalizer U L).subtype) := by
    apply sup_le
    · intro x hx
      refine ⟨⟨x, L.le_normalizer hx, hLU hx⟩, ?_, rfl⟩
      exact F.subgroup_killed_by_normalizerAut U L hx
    · intro x hx
      refine ⟨⟨x, Subgroup.centralizer_le_normalizer _ hx.1, hx.2⟩, ?_, rfl⟩
      exact F.centralizer_killed U L _ hx.1
  intro x hx
  obtain ⟨y, hy, he⟩ := hker hx
  have hyx : y = x := Subtype.ext he
  exact hyx ▸ hy

theorem simpleCentralizerQuotient_killed {U L : Subgroup S} (hLU : L ≤ U) :
    F.SimpleCentralizerQuotient U L ≤ (F.normalizerQuotientToAut U L).ker := by
  rintro a ⟨b, hb, rfl⟩
  exact F.simpleCentralizerIntermediate_killed hLU hb

theorem simpleCentralizerQuotient_nontrivial {U L : Subgroup S}
    (bad : ¬ Subgroup.centralizer (L : Set S) ⊓ U ≤ L) :
    Nontrivial (F.SimpleCentralizerQuotient U L) := by
  classical
  obtain ⟨c, hc, hcL⟩ : ∃ c : S, c ∈ Subgroup.centralizer (L : Set S) ⊓ U ∧ c ∉ L := by
    simpa only [SetLike.not_le_iff_exists] using bad
  let cN : F.relativeNormalizer U L :=
    ⟨c, Subgroup.centralizer_le_normalizer _ hc.1, hc.2⟩
  let a : F.NormalizerQuotient U L := QuotientGroup.mk cN
  have ha : a ∈ F.SimpleCentralizerQuotient U L :=
    ⟨cN, show c ∈ F.simpleCentralizerIntermediate U L from
      (show Subgroup.centralizer (L : Set S) ⊓ U ≤ F.simpleCentralizerIntermediate U L
        from le_sup_right) hc, rfl⟩
  refine ⟨⟨⟨a, ha⟩, 1, ?_⟩⟩
  intro h
  have he : a = 1 := congrArg Subtype.val h
  exact hcL ((QuotientGroup.eq_one_iff cN).mp he)

theorem simpleCentralizerQuotient_p_power (p : ℕ) [Fact p.Prime]
    (hS : IsPGroup p S) {U L : Subgroup S}
    (bad : ¬ Subgroup.centralizer (L : Set S) ⊓ U ≤ L) :
    ∃ r : ℕ, 0 < r ∧ Nat.card (F.SimpleCentralizerQuotient U L) = p ^ r := by
  letI := F.simpleCentralizerQuotient_nontrivial bad
  have hp := ((hS.to_subgroup (F.relativeNormalizer U L)).to_quotient
    (L.subgroupOf (F.relativeNormalizer U L))).to_subgroup (F.SimpleCentralizerQuotient U L)
  obtain ⟨r, hr⟩ := hp.exists_card_eq
  refine ⟨r, ?_, hr⟩
  by_contra hn
  have hz : r = 0 := Nat.eq_zero_of_not_pos hn
  rw [hz, pow_zero] at hr
  exact Finite.one_lt_card.ne' hr

variable {k : Type u} [Field k]
    (M : MackeyModule.{u,u,u} k F.Orbit F.mackeyShape)

/-- The relative trace factors through `L C_U(L)/L`; its intermediate
trace is a nontrivial p-power scalar and hence zero in characteristic p. -/
theorem normalizerTrace_zero_v29 (p : ℕ) [Fact p.Prime] [CharP k p]
    (hS : IsPGroup p S) {U L : Subgroup S} (hLU : L ≤ U)
    (bad : ¬ Subgroup.centralizer (L : Set S) ⊓ U ≤ L) :
    F.normalizerTrace M U L = 0 := by
  classical
  let G := F.NormalizerQuotient U L
  let K := F.SimpleCentralizerQuotient U L
  let ρ : G →* Module.End k (M.Value (F.toOrbit.obj ⟨L⟩)) :=
    (M.automorphismAction _).comp (F.normalizerQuotientToAut U L)
  letI : Fintype G := Fintype.ofFinite G
  letI : Fintype K := Fintype.ofFinite K
  letI : Fintype (G ⧸ K) := Fintype.ofFinite _
  have hker : K ≤ ρ.ker := by
    intro a ha
    change M.automorphismAction _ (F.normalizerQuotientToAut U L a) = 1
    rw [F.simpleCentralizerQuotient_killed hLU ha, map_one]
  obtain ⟨r, hr, hcard⟩ := F.simpleCentralizerQuotient_p_power p hS bad
  have hcast : (Nat.card K : k) = 0 := by
    apply (CharP.cast_eq_zero_iff k p _).mpr
    rw [hcard]
    exact dvd_pow_self p (Nat.ne_zero_of_lt hr)
  ext x
  have hintermediate : (∑ a : K, ρ a.val x) = 0 := by
    rw [finite_trace_trivial_action ρ K hker x, hcast, zero_smul]
  have htotal := finite_trace_transitivity ρ K x
  rw [hintermediate] at htotal
  simp only [map_zero, Finset.sum_const_zero] at htotal
  change (∑ a : F.NormalizerQuotient U L,
    M.push (F.normalizerQuotientToAut U L a).hom x) = 0 at htotal
  simpa only [normalizerTrace, LinearMap.sum_apply, LinearMap.zero_apply] using htotal

end Sharpness.FusionSystem
