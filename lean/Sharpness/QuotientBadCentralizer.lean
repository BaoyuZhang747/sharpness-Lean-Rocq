import Sharpness.QuotientCentric

/-! The nontrivial outer p-kernel produced by a bad quotient centralizer.
This is the group-theoretic obstruction used for centric-radical inclusion
in manuscript Lemma 3.1, Step 2. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem
open CategoryTheory
variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)
    {Z : Subgroup S} [Z.Normal]

include F

theorem quotient_conjugate_eq (P : Subgroup S) (s : S)
    (hs : (QuotientGroup.mk' Z) s ∈
      Subgroup.centralizer (P.map (QuotientGroup.mk' Z) : Set (S ⧸ Z))) (x : P) :
    (QuotientGroup.mk (s * x.val * s⁻¹) : S ⧸ Z) = QuotientGroup.mk x.val := by
  have h := (Subgroup.mem_centralizer_iff.mp hs) ((QuotientGroup.mk' Z) x.val)
    ⟨x.val, x.property, rfl⟩
  change (QuotientGroup.mk x.val : S ⧸ Z) * QuotientGroup.mk s =
    QuotientGroup.mk s * QuotientGroup.mk x.val at h
  simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  rw [← h, mul_assoc, mul_inv_cancel, mul_one]

theorem quotient_centralizer_normalizes (P : Subgroup S) (hZP : Z ≤ P) (s : S)
    (hs : (QuotientGroup.mk' Z) s ∈
      Subgroup.centralizer (P.map (QuotientGroup.mk' Z) : Set (S ⧸ Z))) :
    s ∈ Subgroup.normalizer (P : Set S) := by
  have stable (t : S) (ht : (QuotientGroup.mk' Z) t ∈
      Subgroup.centralizer (P.map (QuotientGroup.mk' Z) : Set (S ⧸ Z)))
      (x : S) (hx : x ∈ P) : t * x * t⁻¹ ∈ P := by
    have hz := QuotientGroup.eq.mp (F.quotient_conjugate_eq P t ht ⟨x, hx⟩).symm
    have h := P.mul_mem hx (hZP hz)
    simpa only [mul_inv_cancel_left] using h
  intro x
  constructor
  · exact stable s hs x
  · intro hx
    have hi : (QuotientGroup.mk' Z) s⁻¹ ∈
        Subgroup.centralizer (P.map (QuotientGroup.mk' Z) : Set (S ⧸ Z)) := by
      rw [map_inv]
      exact Subgroup.inv_mem _ hs
    have h := stable s⁻¹ hi (s * x * s⁻¹) hx
    change x ∈ P
    simpa only [inv_inv, inv_mul_cancel_left, mul_assoc, inv_mul_cancel, mul_one] using h

theorem orbitGamma_nontrivial_of_bad_quotient_centralizer
    (hZ : F.CentralSubgroup Z) (P : Subgroup S) (hZP : Z ≤ P)
    (centric : F.IsCentric P)
    (bad : ¬ Subgroup.centralizer (P.map (QuotientGroup.mk' Z) : Set (S ⧸ Z)) ≤
      P.map (QuotientGroup.mk' Z)) :
    letI := F.central_subgroupOf_normal hZ P
    F.orbitGamma hZ hZP ≠ ⊥ := by
  classical
  letI := F.central_subgroupOf_normal hZ P
  obtain ⟨q, hq, hnq⟩ := Set.not_subset.mp bad
  obtain ⟨s, hs⟩ := QuotientGroup.mk'_surjective Z q
  have hsc : (QuotientGroup.mk' Z) s ∈
      Subgroup.centralizer (P.map (QuotientGroup.mk' Z) : Set (S ⧸ Z)) := hs ▸ hq
  have hsn : s ∉ P := fun hm => hnq (hs ▸ Subgroup.mem_map_of_mem _ hm)
  let n : Subgroup.normalizer (P : Set S) :=
    ⟨s, F.quotient_centralizer_normalizes P hZP s hsc⟩
  let a : F.automorphismSubgroup P :=
    ⟨P.normalizerMonoidHom n, F.normalizerAut_allowed P n⟩
  have ha : a ∈ F.Gamma hZ hZP := by
    apply (quotient_kernel_iff (F.automorphismSubgroup P).subtype
      (Z.subgroupOf P) (F.central_aut_fixed hZ hZP) a).mpr
    intro x
    have hz : x.val⁻¹ * (s * x.val * s⁻¹) ∈ Z :=
      QuotientGroup.eq.mp (F.quotient_conjugate_eq P s hsc x).symm
    exact hz
  have hnot : F.automorphismToOrbitAut P a ≠ 1 := by
    intro he
    have heh := congrArg (fun b : Aut (F.toOrbit.obj ⟨P⟩) => b.hom) he
    have hraw : F.toOrbit.map (F.isoOfMulEquiv a.val a.property).hom =
        F.toOrbit.map (𝟙 (⟨P⟩ : F.Object)) := heh.trans (F.toOrbit.map_id _).symm
    obtain ⟨r, hr⟩ := (F.orbit_map_eq_iff _ _).mp hraw
    have hc : r.val⁻¹ * s ∈ Subgroup.centralizer (P : Set S) := by
      apply Subgroup.mem_centralizer_iff.mpr
      intro x hx
      have h := congrArg (fun y : P => y.val) (hr ⟨x, hx⟩)
      change x = r.val⁻¹ * (s * x * s⁻¹) * r.val at h
      have conj : (r.val⁻¹ * s) * x * (r.val⁻¹ * s)⁻¹ = x := by
        calc
          _ = r.val⁻¹ * (s * x * s⁻¹) * r.val := by group
          _ = x := h.symm
      calc
        x * (r.val⁻¹ * s) =
            ((r.val⁻¹ * s) * x * (r.val⁻¹ * s)⁻¹) * (r.val⁻¹ * s) := by rw [conj]
        _ = (r.val⁻¹ * s) * x := by group
    have hCP := centric P le_top (MulEquiv.refl P) (F.id_mem P)
    rw [inf_top_eq] at hCP
    have hmem := P.mul_mem r.property (hCP hc)
    exact hsn (by simpa only [mul_inv_cancel_left] using hmem)
  intro hbot
  have hm : F.automorphismToOrbitAut P a ∈ F.orbitGamma hZ hZP := ⟨a, ha, rfl⟩
  rw [hbot] at hm
  exact hnot hm

end Sharpness.FusionSystem
