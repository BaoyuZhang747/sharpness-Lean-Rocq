import Sharpness.Unconditional.CentralizerSaturationExtension
import Sharpness.Unconditional.CentralizerCentric

/-! Full centralization in a centralizer system and the ambient join. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem
variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)

theorem centralizer_card_le_ambient_join (p : ℕ) (E : F.ElementaryCategory p)
    (P : Subgroup (F.centralizerGroup p E)) :
    Nat.card (Subgroup.centralizer (P : Set (F.centralizerGroup p E))) ≤
      Nat.card (Subgroup.centralizer
        (ambientSubgroup (F.centralizerGroup p E) (P ⊔ F.elementaryInCentralizer p E) : Set S)) := by
  let T := F.centralizerGroup p E
  let Z := F.elementaryInCentralizer p E
  have hZ : Z ≤ Subgroup.center T := (F.centralizerSystem_central p E).in_center
  have hmem : ∀ x : Subgroup.centralizer (P : Set T),
      x.val.val ∈ Subgroup.centralizer (ambientSubgroup T (P ⊔ Z) : Set S) := by
    intro x
    have hle : P ⊔ Z ≤ Subgroup.centralizer ({x.val} : Set T) := by
      apply sup_le
      · intro y hy
        apply Subgroup.mem_centralizer_iff.mpr
        intro z hz
        have hz' : z = x.val := Set.mem_singleton_iff.mp hz
        subst z
        exact ((Subgroup.mem_centralizer_iff.mp x.property) y hy).symm
      · intro y hy
        exact Subgroup.center_le_centralizer _ (hZ hy)
    apply Subgroup.mem_centralizer_iff.mpr
    rintro y ⟨yT, hy, rfl⟩
    exact congrArg (fun t : T => t.val)
      (((Subgroup.mem_centralizer_iff.mp (hle hy)) x.val (Set.mem_singleton _)).symm)
  let f : Subgroup.centralizer (P : Set T) →
      Subgroup.centralizer (ambientSubgroup T (P ⊔ Z) : Set S) :=
    fun x => ⟨x.val.val, hmem x⟩
  apply Nat.card_le_card_of_injective f
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : Subgroup.centralizer
    (ambientSubgroup T (P ⊔ Z) : Set S) => z.val) h

/-- Full centralization of `P` in `C_F(E)` forces ambient full centralization
of `PE`. This uses only ambient saturation and the exact centralizer maps. -/
theorem centralizerSystem_join_fullyCentralized (p : ℕ) (sat : F.Saturated p)
    (E : F.ElementaryCategory p) (P : Subgroup (F.centralizerGroup p E))
    (hP : (F.centralizerSystem p E).FullyCentralized P) :
    F.FullyCentralized (ambientSubgroup (F.centralizerGroup p E)
      (P ⊔ F.elementaryInCentralizer p E)) := by
  let T := F.centralizerGroup p E
  let Z := F.elementaryInCentralizer p E
  let C := F.centralizerSystem p E
  let A := ambientSubgroup T (P ⊔ Z)
  have hEA : E.obj.subgroup ≤ A := by
    intro z hz
    exact ⟨⟨z, F.elementary_le_centralizer p E hz⟩, Subgroup.mem_sup_right hz, rfl⟩
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
        (ambientSubgroup_le T (P ⊔ Z) (e.symm ⟨r, hr⟩).property)) z.val z.property
    have hm := congrArg (fun a : A => (e a).val) hc
    change (e (⟨z.val, hEA z.property⟩ : A)).val * r =
      r * (e (⟨z.val, hEA z.property⟩ : A)).val
    simpa only [map_mul, Subgroup.coe_mul, MulEquiv.apply_symm_apply] using hm
  let f : A →* T := b.comp ((subgroupInclusion R _ hRC).comp e.toMonoidHom)
  have hf : F.IsHom f :=
    F.comp_mem _ _ (F.comp_mem _ _ he (F.inclusion_mem hRC)) hb
  let gJ : (P ⊔ Z : Subgroup T) →* T := f.comp (subgroupAmbientEquiv T (P ⊔ Z)).toMonoidHom
  let gP : P →* T := gJ.comp (subgroupInclusion P (P ⊔ Z) le_sup_left)
  have hgP_inj : Function.Injective gP := by
    intro x y h
    have hh := F.injective f hf h
    have hh' := (subgroupAmbientEquiv T (P ⊔ Z)).injective hh
    exact Subtype.ext (congrArg (fun z : (P ⊔ Z : Subgroup T) => z.val) hh')
  let U : Subgroup T := gP.range
  let v : P ≃* U := MonoidHom.ofInjective hgP_inj
  have hgJZ : ∀ z : Z, gJ ⟨z.val, Subgroup.mem_sup_right z.property⟩ = z.val := by
    intro z
    apply Subtype.ext
    let zE : E.obj.subgroup := ⟨z.val.val, z.property⟩
    have hh := hbe (eE zE) (hRC (eEhom zE).property)
    rw [MulEquiv.symm_apply_apply] at hh
    exact hh
  have hJmem : ∀ x, gJ x ∈ U ⊔ Z := by
    have hle : (⊤ : Subgroup (P ⊔ Z : Subgroup T)) ≤ (U ⊔ Z).comap gJ := by
      rw [← Subgroup.subgroupOf_self (P ⊔ Z),
        Subgroup.subgroupOf_sup (show P ≤ P ⊔ Z from le_sup_left)
          (show Z ≤ P ⊔ Z from le_sup_right)]
      apply sup_le
      · intro x hx
        exact Subgroup.mem_sup_left (show gJ x ∈ U from ⟨⟨x.val, hx⟩, rfl⟩)
      · intro x hx
        change gJ x ∈ U ⊔ Z
        rw [hgJZ ⟨x.val, hx⟩]
        exact Subgroup.mem_sup_right hx
    exact fun x => hle (Subgroup.mem_top x)
  let g : (P ⊔ Z : Subgroup T) →* (U ⊔ Z : Subgroup T) :=
    { toFun x := ⟨gJ x, hJmem x⟩
      map_one' := Subtype.ext gJ.map_one
      map_mul' x y := Subtype.ext (gJ.map_mul x y) }
  have hg : F.IsHom (ambientHom T g) := by
    apply F.codomain_restrict_mem f hf (ambientSubgroup_le T (U ⊔ Z)) (ambientHom T g)
    apply MonoidHom.ext
    intro x
    obtain ⟨x, rfl⟩ := (subgroupAmbientEquiv T (P ⊔ Z)).surjective x
    apply Subtype.ext
    change (ambientHom T g (subgroupAmbientEquiv T (P ⊔ Z) x)).val = _
    rw [ambientHom_apply]
    rfl
  have hvF : F.IsHom (ambientHom T v.toMonoidHom) := by
    have hV := (F.subgroupRestriction T).codomain_restrict_mem
      (g.comp (subgroupInclusion P (P ⊔ Z) le_sup_left))
      ((F.subgroupRestriction T).comp_mem _ _
        ((F.subgroupRestriction T).inclusion_mem _) hg)
      le_sup_left v.toMonoidHom (by ext; rfl)
    exact hV
  have hv : C.IsHom v.toMonoidHom := ⟨hvF, g, hg, (fun _ => rfl), hgJZ⟩
  have hlocal : Nat.card (Subgroup.centralizer (U : Set T)) ≤
      Nat.card (Subgroup.centralizer (P : Set T)) := hP U v hv
  have hRcentral : Nat.card (Subgroup.centralizer (R : Set S)) ≤
      Nat.card (Subgroup.centralizer (U : Set T)) := by
    have hCD : Subgroup.centralizer (R : Set S) ≤ Subgroup.centralizer (D : Set S) :=
      Subgroup.centralizer_le hDR
    have hmem : ∀ x : Subgroup.centralizer (R : Set S),
        b ⟨x.val, hCD x.property⟩ ∈ Subgroup.centralizer (U : Set T) := by
      intro x
      apply Subgroup.mem_centralizer_iff.mpr
      rintro y ⟨q, rfl⟩
      have hc : (⟨(e (subgroupAmbientEquiv T (P ⊔ Z)
          ⟨q.val, Subgroup.mem_sup_left q.property⟩)).val, hRC (e _).property⟩ :
            Subgroup.centralizer (D : Set S)) * ⟨x.val, hCD x.property⟩ =
          ⟨x.val, hCD x.property⟩ * ⟨(e (subgroupAmbientEquiv T (P ⊔ Z)
            ⟨q.val, Subgroup.mem_sup_left q.property⟩)).val, hRC (e _).property⟩ := by
        apply Subtype.ext
        exact (Subgroup.mem_centralizer_iff.mp x.property) _ (e _).property
      exact (map_mul b _ _).symm.trans ((congrArg b hc).trans (map_mul b _ _))
    let k : Subgroup.centralizer (R : Set S) → Subgroup.centralizer (U : Set T) :=
      fun x => ⟨b ⟨x.val, hCD x.property⟩, hmem x⟩
    apply Nat.card_le_card_of_injective k
    intro x y h
    apply Subtype.ext
    have h' := congrArg (fun z : Subgroup.centralizer (U : Set T) => z.val) h
    exact congrArg (fun z : Subgroup.centralizer (D : Set S) => z.val) (F.injective b hb h')
  exact hRcentral.trans (hlocal.trans (F.centralizer_card_le_ambient_join p E P))

theorem centralizerSystem_receptive_of_fullyCentralized (p : ℕ) (sat : F.Saturated p)
    (E : F.ElementaryCategory p) (P : Subgroup (F.centralizerGroup p E))
    (hP : (F.centralizerSystem p E).FullyCentralized P) :
    (F.centralizerSystem p E).Receptive P :=
  F.centralizerSystem_receptive_of_join_fullyCentralized p sat E P
    (F.centralizerSystem_join_fullyCentralized p sat E P hP)

end Sharpness.FusionSystem
