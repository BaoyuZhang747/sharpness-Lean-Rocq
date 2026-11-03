import Sharpness.CentralizerCentral

/-! The centric-subgroup comparison for a centralizer fusion system, derived
from the defining centralizer morphisms and the ambient saturation axiom. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

universe u
namespace Sharpness.FusionSystem
open CategoryTheory

variable {S : Type u} [Group S] (F : FusionSystem S)

private theorem centric_iff_centralizers (P : Subgroup S) :
    F.IsCentric P ↔ ∀ (Q : Subgroup S) (e : P ≃* Q),
      F.IsHom e.toMonoidHom → Subgroup.centralizer (Q : Set S) ≤ Q := by
  constructor
  · intro h Q e he
    simpa only [inf_top_eq] using h Q le_top e he
  · intro h Q _ e he
    simpa only [inf_top_eq] using h Q e he

private theorem restrict_hom {P Q A B : Subgroup S}
    (f : P →* Q) (hf : F.IsHom f) (hAP : A ≤ P) (hBQ : B ≤ Q)
    (g : A →* B)
    (hg : ∀ a : A, (g a).val = (f ⟨a.val, hAP a.property⟩).val) :
    F.IsHom g := by
  apply F.codomain_restrict_mem (f.comp (subgroupInclusion A P hAP))
    (F.comp_mem _ _ (F.inclusion_mem hAP) hf) hBQ g
  ext a
  exact hg a

private theorem ambient_centric_implies_subsystem_centric
    (T : Subgroup S) (H : FusionSystem T) (h : F.SubsystemEmbedding T H)
    (P : Subgroup T) (hP : F.IsCentric (ambientSubgroup T P)) : H.IsCentric P := by
  apply (centric_iff_centralizers H P).mpr
  intro Q e he x hx
  let e' := (subgroupAmbientEquiv T P).symm.trans
    (e.trans (subgroupAmbientEquiv T Q))
  have he' : F.IsHom e'.toMonoidHom := h.hom_mem e.toMonoidHom he
  have hx' : x.val ∈ Subgroup.centralizer (ambientSubgroup T Q : Set S) := by
    apply Subgroup.mem_centralizer_iff.mpr
    rintro y ⟨yT, hyT, rfl⟩
    exact congrArg Subtype.val ((Subgroup.mem_centralizer_iff.mp hx) yT hyT)
  obtain ⟨y, hy, hxy⟩ := (centric_iff_centralizers F _).mp hP _ e' he' hx'
  have : y = x := Subtype.ext hxy
  exact this ▸ hy

variable [Finite S]

omit [Finite S] in
/-- A fusion isomorphism with fully centralized target extends to a morphism
between the two centralizers, with the specified values wherever its source
lies in its own centralizer. -/
theorem centralizer_extension_of_fullyCentralized (p : ℕ) (sat : F.Saturated p)
    {A B : Subgroup S} (e : A ≃* B) (he : F.IsHom e.toMonoidHom)
    (hB : F.FullyCentralized B) :
    ∃ f : Subgroup.centralizer (A : Set S) →* Subgroup.centralizer (B : Set S),
      F.IsHom f ∧ ∀ (a : A) (ha : a.val ∈ Subgroup.centralizer (A : Set S)),
        (f ⟨a.val, ha⟩).val = (e a).val := by
  obtain ⟨N, hAN, hN, g, hg, hge⟩ := sat.extension e he hB
  have hCN : Subgroup.centralizer (A : Set S) ≤ N := by
    intro x hx
    rw [← SetLike.mem_coe, hN]
    refine ⟨⟨x, Subgroup.centralizer_le_normalizer (A : Set S) hx⟩, rfl, 1, ?_⟩
    intro a
    have hxcomm := (Subgroup.mem_centralizer_iff.mp hx) a.val a.property
    have hxfix : A.normalizerMonoidHom
        ⟨x, Subgroup.centralizer_le_normalizer (A : Set S) hx⟩ a = a := by
      apply Subtype.ext
      change x * a.val * x⁻¹ = a.val
      rw [← hxcomm, mul_assoc, mul_inv_cancel, mul_one]
    rw [hxfix]
    simp
  let gC : Subgroup.centralizer (A : Set S) →* (⊤ : Subgroup S) :=
    g.comp (subgroupInclusion _ N hCN)
  have hgC : F.IsHom gC := F.comp_mem _ _ (F.inclusion_mem hCN) hg
  have hmem : ∀ x : Subgroup.centralizer (A : Set S),
      (gC x).val ∈ Subgroup.centralizer (B : Set S) := by
    intro x
    apply Subgroup.mem_centralizer_iff.mpr
    intro b hb
    let a := e.symm ⟨b, hb⟩
    have hga : (g ⟨a.val, hAN a.property⟩).val = b := by
      rw [hge a]
      exact congrArg Subtype.val (e.apply_symm_apply ⟨b, hb⟩)
    have hcomm : (⟨a.val, hAN a.property⟩ : N) * ⟨x.val, hCN x.property⟩ =
        ⟨x.val, hCN x.property⟩ * ⟨a.val, hAN a.property⟩ := by
      apply Subtype.ext
      exact (Subgroup.mem_centralizer_iff.mp x.property) a.val a.property
    have hm := congrArg (fun z : N => (g z).val) hcomm
    change b * (g ⟨x.val, hCN x.property⟩).val =
      (g ⟨x.val, hCN x.property⟩).val * b
    simpa only [map_mul, Subgroup.coe_mul, hga] using hm
  let f : Subgroup.centralizer (A : Set S) →* Subgroup.centralizer (B : Set S) :=
    { toFun x := ⟨(gC x).val, hmem x⟩
      map_one' := by
        apply Subtype.ext
        change (gC 1).val = 1
        exact congrArg (fun z : (⊤ : Subgroup S) => z.val) gC.map_one
      map_mul' x y := by
        apply Subtype.ext
        change (gC (x * y)).val = (gC x).val * (gC y).val
        exact congrArg (fun z : (⊤ : Subgroup S) => z.val) (gC.map_mul x y) }
  refine ⟨f, F.codomain_restrict_mem gC hgC le_top f (by ext x; rfl), ?_⟩
  intro a ha
  exact hge a

variable (p : ℕ) [Fact p.Prime] (hS : IsPGroup p S) (sat : F.Saturated p)
    (E : F.ElementaryCategory p) (C : F.AKOCentralizerInput p hS sat E)

theorem elementaryInCentralizer_le_of_centric
    (P : Subgroup (F.centralizerGroup p E)) (hP : C.system.IsCentric P) :
    F.elementaryInCentralizer p E ≤ P := by
  have hself := (centric_iff_centralizers C.system P).mp hP P (MulEquiv.refl P)
    (C.system.id_mem P)
  intro z hz
  apply hself
  apply Subgroup.mem_centralizer_iff.mpr
  intro x _
  exact (Subgroup.mem_center_iff.mp
    (F.elementaryInCentralizer_in_center p E hz)) x

omit [Finite S] [Fact p.Prime] in
/-- Once the source contains `E`, an ambient fusion map which fixes `E`
belongs to the centralizer fusion system by its defining extension property. -/
theorem centralizer_hom_of_fixes_elementary
    {P Q : Subgroup (F.centralizerGroup p E)}
    (hEP : F.elementaryInCentralizer p E ≤ P) (f : P →* Q)
    (hf : F.IsHom (ambientHom (F.centralizerGroup p E) f))
    (hfix : ∀ z : F.elementaryInCentralizer p E,
      (f ⟨z.val, hEP z.property⟩).val = z.val) : C.system.IsHom f := by
  apply (C.hom_iff f).mpr
  refine ⟨hf, ?_⟩
  let pre : (P ⊔ F.elementaryInCentralizer p E :
      Subgroup (F.centralizerGroup p E)) →* P :=
    subgroupInclusion _ _ (sup_le le_rfl hEP)
  let post : Q →* (Q ⊔ F.elementaryInCentralizer p E :
      Subgroup (F.centralizerGroup p E)) := subgroupInclusion _ _ le_sup_left
  let g := post.comp (f.comp pre)
  refine ⟨g, ?_, (fun _ => rfl), ?_⟩
  · change F.IsHom (ambientHom (F.centralizerGroup p E) (post.comp (f.comp pre)))
    rw [ambientHom_comp, ambientHom_comp]
    exact F.comp_mem _ _
      (F.comp_mem _ _ (F.ambientHom_inclusion_allowed _ _) hf)
      (F.ambientHom_inclusion_allowed _ _)
  · exact hfix

/-- A subgroup centric in the centralizer fusion system is centric in the
ambient saturated fusion system. Only the defining centralizer morphisms,
not saturation of the centralizer system, are used. -/
theorem centralizer_centric_implies_ambient_centric
    (P : Subgroup (F.centralizerGroup p E)) (hP : C.system.IsCentric P) :
    F.IsCentric (ambientSubgroup (F.centralizerGroup p E) P) := by
  let T := F.centralizerGroup p E
  let A := ambientSubgroup T P
  have hEP := F.elementaryInCentralizer_le_of_centric p hS sat E C P hP
  have hEA : E.obj.subgroup ≤ A := by
    intro z hz
    exact ⟨⟨z, F.elementary_le_centralizer p E hz⟩, hEP hz, rfl⟩
  apply (centric_iff_centralizers F A).mpr
  intro R e he
  let eEhom : E.obj.subgroup →* R :=
    e.toMonoidHom.comp (subgroupInclusion _ _ hEA)
  have heEhom : F.IsHom eEhom := F.comp_mem _ _ (F.inclusion_mem hEA) he
  let eEraw : E.obj.subgroup →* S := R.subtype.comp eEhom
  let D : Subgroup S := eEraw.range
  have heEraw_inj : Function.Injective eEraw :=
    Subtype.val_injective.comp (F.injective eEhom heEhom)
  let eE : E.obj.subgroup ≃* D := MonoidHom.ofInjective heEraw_inj
  have hDR : D ≤ R := by
    rintro z ⟨x, rfl⟩
    exact (eEhom x).property
  have heE : F.IsHom eE.toMonoidHom := by
    apply F.codomain_restrict_mem eEhom heEhom hDR eE.toMonoidHom
    ext z
    rfl
  obtain ⟨b, hb, hbe⟩ := F.centralizer_extension_of_fullyCentralized p sat
    eE.symm (F.inverse_mem eE heE) E.property.2.2.2
  have hRC : R ≤ Subgroup.centralizer (D : Set S) := by
    intro r hr
    apply Subgroup.mem_centralizer_iff.mpr
    rintro d ⟨z, rfl⟩
    have hc : (⟨z.val, hEA z.property⟩ : A) * e.symm ⟨r, hr⟩ =
        e.symm ⟨r, hr⟩ * ⟨z.val, hEA z.property⟩ := by
      apply Subtype.ext
      exact (Subgroup.mem_centralizer_iff.mp
        (ambientSubgroup_le T P (e.symm ⟨r, hr⟩).property)) z.val z.property
    have hm := congrArg (fun a : A => (e a).val) hc
    change (e (⟨z.val, hEA z.property⟩ : A)).val * r =
      r * (e (⟨z.val, hEA z.property⟩ : A)).val
    simpa only [map_mul, Subgroup.coe_mul, MulEquiv.apply_symm_apply] using hm
  let f : A →* T := b.comp ((subgroupInclusion R _ hRC).comp e.toMonoidHom)
  have hf : F.IsHom f :=
    F.comp_mem _ _ (F.comp_mem _ _ he (F.inclusion_mem hRC)) hb
  let g : P →* T := f.comp (subgroupAmbientEquiv T P).toMonoidHom
  have hg_inj : Function.Injective g :=
    (F.injective f hf).comp (subgroupAmbientEquiv T P).injective
  let U : Subgroup T := g.range
  let v : P ≃* U := MonoidHom.ofInjective hg_inj
  have hvF : F.IsHom (ambientHom T v.toMonoidHom) := by
    apply F.codomain_restrict_mem f hf (ambientSubgroup_le T U)
      (ambientHom T v.toMonoidHom)
    apply MonoidHom.ext
    intro a
    obtain ⟨a, rfl⟩ := (subgroupAmbientEquiv T P).surjective a
    apply Subtype.ext
    change (ambientHom T v.toMonoidHom (subgroupAmbientEquiv T P a)).val = _
    rw [ambientHom_apply]
    rfl
  have hvfix : ∀ z : F.elementaryInCentralizer p E,
      (v ⟨z.val, hEP z.property⟩).val = z.val := by
    intro z
    apply Subtype.ext
    let zE : E.obj.subgroup := ⟨z.val.val, z.property⟩
    have hh := hbe (eE zE) (hRC (eEhom zE).property)
    rw [MulEquiv.symm_apply_apply] at hh
    change (b ⟨(e (subgroupAmbientEquiv T P ⟨z.val, hEP z.property⟩)).val, _⟩).val =
      z.val.val
    change (b ⟨(e (⟨z.val.val, hEA z.property⟩ : A)).val, _⟩).val = z.val.val at hh
    exact hh
  have hv : C.system.IsHom v.toMonoidHom :=
    F.centralizer_hom_of_fixes_elementary p hS sat E C hEP v.toMonoidHom hvF hvfix
  have hCU : Subgroup.centralizer (U : Set T) ≤ U :=
    (centric_iff_centralizers C.system P).mp hP U v hv
  intro x hx
  have hxD : x ∈ Subgroup.centralizer (D : Set S) := by
    apply Subgroup.mem_centralizer_iff.mpr
    intro z hz
    exact (Subgroup.mem_centralizer_iff.mp hx) z (hDR hz)
  have hbx : b ⟨x, hxD⟩ ∈ Subgroup.centralizer (U : Set T) := by
    apply Subgroup.mem_centralizer_iff.mpr
    rintro y ⟨a, rfl⟩
    have hc : (⟨(e (subgroupAmbientEquiv T P a)).val,
        hRC (e (subgroupAmbientEquiv T P a)).property⟩ :
        Subgroup.centralizer (D : Set S)) * ⟨x, hxD⟩ =
        ⟨x, hxD⟩ * ⟨(e (subgroupAmbientEquiv T P a)).val,
        hRC (e (subgroupAmbientEquiv T P a)).property⟩ := by
      apply Subtype.ext
      exact (Subgroup.mem_centralizer_iff.mp hx) _
        (e (subgroupAmbientEquiv T P a)).property
    exact (map_mul b _ _).symm.trans ((congrArg b hc).trans (map_mul b _ _))
  obtain ⟨a, ha⟩ := hCU hbx
  have hax : (⟨(e (subgroupAmbientEquiv T P a)).val,
      hRC (e (subgroupAmbientEquiv T P a)).property⟩ :
      Subgroup.centralizer (D : Set S)) = ⟨x, hxD⟩ :=
    F.injective b hb ha
  have heax : (e (subgroupAmbientEquiv T P a)).val = x := congrArg Subtype.val hax
  rw [← heax]
  exact (e (subgroupAmbientEquiv T P a)).property

/-- The full centralizer centricity comparison, proved from ambient saturation
and the actual defining centralizer morphisms. -/
def yalcinCentralizerCentricInput : F.YalcinCentralizerCentricInput E C where
  lemma_8_11 P := ⟨⟨F.centralizer_centric_implies_ambient_centric p hS sat E C P,
    ambient_centric_implies_subsystem_centric F _ C.system (C.embedding F) P⟩,
    F.elementaryInCentralizer_le_of_centric p hS sat E C P⟩

end Sharpness.FusionSystem
