import Sharpness.Unconditional.PuigNormalization
import Sharpness.Unconditional.PuigNormalizerAmalgamation

/-! The concrete growth diagram in Puig's induction. Normalize the two
left legs into one subgroup of P, join the two relative normalizers, and
apply the saturation extension axiom. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness.FusionSystem
open CategoryTheory
variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)

theorem puigInclusion_comp {A B C : Subgroup S}
    {hA : F.IsCentric A} {hB : F.IsCentric B} {hC : F.IsCentric C}
    (hAB : A ≤ B) (hBC : B ≤ C) :
    F.puigInclusion (hA := hA) (hB := hB) hAB ≫ F.puigInclusion (hB := hC) hBC =
      F.puigInclusion (hAB.trans hBC) := by
  apply InducedCategory.hom_ext
  change F.toOrbit.map (F.inclusion hAB) ≫ F.toOrbit.map (F.inclusion hBC) = _
  rw [← F.toOrbit.map_comp]
  rfl

theorem puig_order_iso {X Y : F.CentricOrbit} (e : X ≅ Y) :
    F.orbitOrder X.obj = F.orbitOrder Y.obj :=
  le_antisymm (F.orbitOrder_mono e.hom.hom) (F.orbitOrder_mono e.inv.hom)

theorem puig_isIso_of_order_eq {X Y : F.CentricOrbit} (f : X ⟶ Y)
    (h : F.orbitOrder X.obj = F.orbitOrder Y.obj) : IsIso f := by
  letI := F.orbit_isIso_of_equal_order f.hom h
  exact (ObjectProperty.isoMk _ (asIso f.hom)).isIso_hom

theorem puig_lt_relativeNormalizer (p : ℕ) [Fact p.Prime]
    (hS : IsPGroup p S) {R A : Subgroup S} (hRA : R < A) :
    R < Subgroup.normalizer (R : Set S) ⊓ A := by
  apply lt_of_le_of_ne (le_inf Subgroup.le_normalizer hRA.le)
  intro he
  have hsmall : R.subgroupOf A ≠ ⊤ := by
    intro ht
    exact hRA.not_ge (Subgroup.subgroupOf_eq_top.mp ht)
  have hlt := proper_subgroup_lt_normalizer p (hS.to_subgroup A) hsmall
  obtain ⟨x, hxN, hxR⟩ := SetLike.not_le_iff_exists.mp (not_le_of_gt hlt)
  have hx : x.val ∈ Subgroup.normalizer (R : Set S) := by
    rw [← Subgroup.subgroupOf_normalizer_eq hRA.le] at hxN
    exact hxN
  exact hxR (he ▸ show x.val ∈ Subgroup.normalizer (R : Set S) ⊓ A from ⟨hx, x.property⟩)

private theorem card_lt_of_lt {A B : Subgroup S} (h : A < B) : Nat.card A < Nat.card B := by
  apply lt_of_not_ge
  intro hc
  exact h.ne (Subgroup.eq_of_le_of_card_ge h.le hc)

/-- Saturation gives the growing common-extension diagram for any two
noninvertible factors of centric spans. -/
theorem centric_growth_amalgamation (p : ℕ) [Fact p.Prime]
    (hS : IsPGroup p S) (sat : F.Saturated p)
    {P Q : F.CentricOrbit} {X A B : PuigSpan P Q}
    (f : X.Factor A) (g : X.Factor B) (hf : ¬ IsIso f.hom) (hg : ¬ IsIso g.hom) :
    Nonempty (PuigSpan.GrowthAmalgamation (fun U : F.CentricOrbit => F.orbitOrder U.obj) f g) := by
  obtain ⟨R, hR, hRP, eX, heX⟩ := F.normalize_centric_arrow X.left
  have hfa : (eX.inv ≫ f.hom) ≫ A.left = F.puigInclusion hRP := by
    rw [Category.assoc, f.left_fac, ← heX, Iso.inv_hom_id_assoc]
  have hgb : (eX.inv ≫ g.hom) ≫ B.left = F.puigInclusion hRP := by
    rw [Category.assoc, g.left_fac, ← heX, Iso.inv_hom_id_assoc]
  obtain ⟨A', hA', hRA, hAP, eA, heA, hfeA⟩ :=
    F.normalize_centric_factor hR hRP A.left (eX.inv ≫ f.hom) hfa
  obtain ⟨B', hB', hRB, hBP, eB, heB, hgeB⟩ :=
    F.normalize_centric_factor hR hRP B.left (eX.inv ≫ g.hom) hgb
  have hfNorm : f.hom ≫ eA.hom = eX.hom ≫ F.puigInclusion hRA := by
    rw [← hfeA, ← Category.assoc, Iso.hom_inv_id_assoc]
  have hgNorm : g.hom ≫ eB.hom = eX.hom ≫ F.puigInclusion hRB := by
    rw [← hgeB, ← Category.assoc, Iso.hom_inv_id_assoc]
  have hproperA : R < A' := by
    apply lt_of_le_of_ne hRA
    intro hh
    apply hf
    apply F.puig_isIso_of_order_eq
    have hx := F.puig_order_iso eX
    have ha := F.puig_order_iso eA
    change F.orbitOrder X.apex.obj = Nat.card R at hx
    change F.orbitOrder A.apex.obj = Nat.card A' at ha
    rw [hx, ha, hh]
  have hproperB : R < B' := by
    apply lt_of_le_of_ne hRB
    intro hh
    apply hg
    apply F.puig_isIso_of_order_eq
    have hx := F.puig_order_iso eX
    have hb := F.puig_order_iso eB
    change F.orbitOrder X.apex.obj = Nat.card R at hx
    change F.orbitOrder B.apex.obj = Nat.card B' at hb
    rw [hx, hb, hh]
  let βA : F.puigObject A' hA' ⟶ Q := eA.inv ≫ A.right
  let βB : F.puigObject B' hB' ⟶ Q := eB.inv ≫ B.right
  have hβA : F.puigInclusion hRA ≫ βA = eX.inv ≫ X.right := by
    rw [← hfeA]
    simp only [βA, Category.assoc, Iso.hom_inv_id_assoc, f.right_fac]
  have hβB : F.puigInclusion hRB ≫ βB = eX.inv ≫ X.right := by
    rw [← hgeB]
    simp only [βB, Category.assoc, Iso.hom_inv_id_assoc, g.right_fac]
  let a₀ := F.orbitRepresentative βA.hom
  let b₀ := F.orbitRepresentative βB.hom
  have hraw : F.toOrbit.map (F.inclusion hRA ≫ a₀) =
      F.toOrbit.map (F.inclusion hRB ≫ b₀) := by
    have hh := congrArg (fun t : F.puigObject R hR ⟶ Q => t.hom) (hβA.trans hβB.symm)
    change F.toOrbit.map (F.inclusion hRA) ≫ βA.hom =
      F.toOrbit.map (F.inclusion hRB) ≫ βB.hom at hh
    simpa only [Functor.map_comp, a₀, b₀, F.orbitRepresentative_map] using hh
  obtain ⟨d₀, hdA, hdB⟩ := F.centric_normalizer_amalgamation p hS sat hRA hRB hR a₀ b₀ hraw
  let NA := Subgroup.normalizer (R : Set S) ⊓ A'
  let NB := Subgroup.normalizer (R : Set S) ⊓ B'
  let N := NA ⊔ NB
  have hRNA : R ≤ NA := le_inf Subgroup.le_normalizer hRA
  have hRNB : R ≤ NB := le_inf Subgroup.le_normalizer hRB
  have hNAA : NA ≤ A' := inf_le_right
  have hNBB : NB ≤ B' := inf_le_right
  have hNAP : NA ≤ P.obj.as.subgroup := hNAA.trans hAP
  have hNBP : NB ≤ P.obj.as.subgroup := hNBB.trans hBP
  have hNP : N ≤ P.obj.as.subgroup := sup_le hNAP hNBP
  have hNA : F.IsCentric NA := F.centric_overgroup hR hRNA
  have hNB : F.IsCentric NB := F.centric_overgroup hR hRNB
  have hN : F.IsCentric N := F.centric_overgroup hNA le_sup_left
  let Y : PuigSpan P Q :=
    { apex := F.puigObject NA hNA
      left := F.puigInclusion hNAP
      right := F.puigInclusion hNAA ≫ βA }
  let Z : PuigSpan P Q :=
    { apex := F.puigObject NB hNB
      left := F.puigInclusion hNBP
      right := F.puigInclusion hNBB ≫ βB }
  let D : PuigSpan P Q :=
    { apex := F.puigObject N hN
      left := F.puigInclusion hNP
      right := ObjectProperty.homMk (F.toOrbit.map d₀) }
  let a : X.Factor Y :=
    { hom := eX.hom ≫ F.puigInclusion hRNA
      left_fac := by
        change (eX.hom ≫ F.puigInclusion hRNA) ≫ F.puigInclusion hNAP = X.left
        rw [Category.assoc, F.puigInclusion_comp]
        exact heX
      right_fac := by
        change (eX.hom ≫ F.puigInclusion hRNA) ≫ (F.puigInclusion hNAA ≫ βA) = X.right
        rw [Category.assoc, ← Category.assoc (F.puigInclusion hRNA), F.puigInclusion_comp,
          hβA, Iso.hom_inv_id_assoc] }
  let b : X.Factor Z :=
    { hom := eX.hom ≫ F.puigInclusion hRNB
      left_fac := by
        change (eX.hom ≫ F.puigInclusion hRNB) ≫ F.puigInclusion hNBP = X.left
        rw [Category.assoc, F.puigInclusion_comp]
        exact heX
      right_fac := by
        change (eX.hom ≫ F.puigInclusion hRNB) ≫ (F.puigInclusion hNBB ≫ βB) = X.right
        rw [Category.assoc, ← Category.assoc (F.puigInclusion hRNB), F.puigInclusion_comp,
          hβB, Iso.hom_inv_id_assoc] }
  let c : Y.Factor A :=
    { hom := F.puigInclusion hNAA ≫ eA.inv
      left_fac := by
        change (F.puigInclusion hNAA ≫ eA.inv) ≫ A.left = F.puigInclusion hNAP
        rw [← heA, Category.assoc, Iso.inv_hom_id_assoc, F.puigInclusion_comp]
      right_fac := Category.assoc _ _ _ }
  let d : Z.Factor B :=
    { hom := F.puigInclusion hNBB ≫ eB.inv
      left_fac := by
        change (F.puigInclusion hNBB ≫ eB.inv) ≫ B.left = F.puigInclusion hNBP
        rw [← heB, Category.assoc, Iso.inv_hom_id_assoc, F.puigInclusion_comp]
      right_fac := Category.assoc _ _ _ }
  let e : Y.Factor D :=
    { hom := F.puigInclusion le_sup_left
      left_fac := F.puigInclusion_comp _ _
      right_fac := by
        apply InducedCategory.hom_ext
        change F.toOrbit.map (F.inclusion le_sup_left) ≫ F.toOrbit.map d₀ =
          F.toOrbit.map (F.inclusion hNAA) ≫ βA.hom
        simpa only [Functor.map_comp, a₀, F.orbitRepresentative_map] using hdA }
  let h : Z.Factor D :=
    { hom := F.puigInclusion le_sup_right
      left_fac := F.puigInclusion_comp _ _
      right_fac := by
        apply InducedCategory.hom_ext
        change F.toOrbit.map (F.inclusion le_sup_right) ≫ F.toOrbit.map d₀ =
          F.toOrbit.map (F.inclusion hNBB) ≫ βB.hom
        simpa only [Functor.map_comp, b₀, F.orbitRepresentative_map] using hdB }
  refine ⟨{
    Y := Y
    Z := Z
    D := D
    a := a
    b := b
    c := c
    d := d
    e := e
    h := h
    growY := ?_
    growZ := ?_
    facA := ?_
    facB := ?_
    agree := ?_ }⟩
  · have hx := F.puig_order_iso eX
    change F.orbitOrder X.apex.obj = Nat.card R at hx
    change F.orbitOrder X.apex.obj < Nat.card NA
    rw [hx]
    exact card_lt_of_lt (puig_lt_relativeNormalizer p hS hproperA)
  · have hx := F.puig_order_iso eX
    change F.orbitOrder X.apex.obj = Nat.card R at hx
    change F.orbitOrder X.apex.obj < Nat.card NB
    rw [hx]
    exact card_lt_of_lt (puig_lt_relativeNormalizer p hS hproperB)
  · change (eX.hom ≫ F.puigInclusion hRNA) ≫ (F.puigInclusion hNAA ≫ eA.inv) = f.hom
    rw [Category.assoc, ← Category.assoc (F.puigInclusion hRNA), F.puigInclusion_comp,
      ← Category.assoc, ← hfNorm, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  · change (eX.hom ≫ F.puigInclusion hRNB) ≫ (F.puigInclusion hNBB ≫ eB.inv) = g.hom
    rw [Category.assoc, ← Category.assoc (F.puigInclusion hRNB), F.puigInclusion_comp,
      ← Category.assoc, ← hgNorm, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  · change (eX.hom ≫ F.puigInclusion hRNA) ≫ F.puigInclusion le_sup_left =
      (eX.hom ≫ F.puigInclusion hRNB) ≫ F.puigInclusion le_sup_right
    rw [Category.assoc, Category.assoc, F.puigInclusion_comp, F.puigInclusion_comp]

end Sharpness.FusionSystem
