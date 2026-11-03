import Sharpness.CentralizerCentral

/-! Concrete centralizer morphisms and their closure axioms. No saturation
claim is included in the construction of the underlying fusion system. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem
variable {S : Type u} [Group S] (F : FusionSystem S)

/-- Restrict the ambient morphisms to subgroups of a fixed subgroup. -/
def subgroupRestriction (T : Subgroup S) : FusionSystem T where
  IsHom f := F.IsHom (ambientHom T f)
  injective f hf := by
    intro x y h
    apply (subgroupAmbientEquiv T _).injective
    apply F.injective _ hf
    simpa only [ambientHom_apply] using congrArg (subgroupAmbientEquiv T _) h
  id_mem P := by rw [ambientHom_id]; exact F.id_mem _
  comp_mem f g hf hg := by
    rw [ambientHom_comp]
    exact F.comp_mem _ _ hf hg
  inclusion_mem h := F.ambientHom_inclusion_allowed T h
  conjugation_mem P Q s h := by
    let h' : ∀ x ∈ ambientSubgroup T P, s.val⁻¹ * x * s.val ∈ ambientSubgroup T Q := by
      rintro x ⟨y, hy, rfl⟩
      exact ⟨s⁻¹ * y * s, h y hy, rfl⟩
    have heq : ambientHom T (subgroupConjugation P Q s h) =
        subgroupConjugation _ _ s.val h' := by
      ext x
      obtain ⟨y, rfl⟩ := (subgroupAmbientEquiv T P).surjective x
      exact congrArg Subtype.val (ambientHom_apply T _ y)
    rw [heq]
    exact F.conjugation_mem _ _ _ _
  inverse_mem e he := by
    let e' := (subgroupAmbientEquiv T _).symm.trans
      (e.trans (subgroupAmbientEquiv T _))
    exact F.inverse_mem e' he
  codomain_restrict_mem f hf hRQ g hgf := by
    apply F.codomain_restrict_mem (ambientHom T f) hf (Subgroup.map_mono hRQ)
    rw [← ambientHom_inclusion T hRQ, ← ambientHom_comp, hgf]

/-- A centralizer morphism has an extension fixing the central subgroup. -/
def CentralizingHom (Z : Subgroup S) {P Q : Subgroup S} (f : P →* Q) : Prop :=
  F.IsHom f ∧ ∃ g : (P ⊔ Z : Subgroup S) →* (Q ⊔ Z : Subgroup S),
    F.IsHom g ∧
    (∀ x : P, (g ⟨x.val, Subgroup.mem_sup_left x.property⟩).val = (f x).val) ∧
    (∀ z : Z, (g ⟨z.val, Subgroup.mem_sup_right z.property⟩).val = z.val)

theorem centralizingHom_id (Z P : Subgroup S) :
    F.CentralizingHom Z (MonoidHom.id P) :=
  ⟨F.id_mem P, MonoidHom.id _, F.id_mem _, (fun _ => rfl), (fun _ => rfl)⟩

theorem centralizingHom_comp (Z : Subgroup S) {P Q R : Subgroup S}
    (f : P →* Q) (g : Q →* R) (hf : F.CentralizingHom Z f)
    (hg : F.CentralizingHom Z g) : F.CentralizingHom Z (g.comp f) := by
  obtain ⟨hf, f', hf', hfP, hfZ⟩ := hf
  obtain ⟨hg, g', hg', hgQ, hgZ⟩ := hg
  refine ⟨F.comp_mem _ _ hf hg, g'.comp f', F.comp_mem _ _ hf' hg', ?_, ?_⟩
  · intro x
    change (g' (f' ⟨x.val, Subgroup.mem_sup_left x.property⟩)).val = _
    have h : f' ⟨x.val, Subgroup.mem_sup_left x.property⟩ =
        ⟨(f x).val, Subgroup.mem_sup_left (f x).property⟩ := Subtype.ext (hfP x)
    rw [h]
    exact hgQ (f x)
  · intro z
    change (g' (f' ⟨z.val, Subgroup.mem_sup_right z.property⟩)).val = _
    have h : f' ⟨z.val, Subgroup.mem_sup_right z.property⟩ =
        ⟨z.val, Subgroup.mem_sup_right z.property⟩ := Subtype.ext (hfZ z)
    rw [h]
    exact hgZ z

theorem centralizingHom_inclusion (Z : Subgroup S) {P Q : Subgroup S} (h : P ≤ Q) :
    F.CentralizingHom Z (subgroupInclusion P Q h) :=
  ⟨F.inclusion_mem h, subgroupInclusion _ _ (sup_le_sup_right h Z),
    F.inclusion_mem _, (fun _ => rfl), (fun _ => rfl)⟩

theorem join_image_mem {A B Q : Subgroup S} (g : (A ⊔ B : Subgroup S) →* Q)
    (R : Subgroup Q)
    (hA : ∀ x : A, g ⟨x.val, Subgroup.mem_sup_left x.property⟩ ∈ R)
    (hB : ∀ x : B, g ⟨x.val, Subgroup.mem_sup_right x.property⟩ ∈ R) :
    ∀ x, g x ∈ R := by
  have h : (⊤ : Subgroup (A ⊔ B : Subgroup S)) ≤ R.comap g := by
    rw [← Subgroup.subgroupOf_self (A ⊔ B),
      Subgroup.subgroupOf_sup (show A ≤ A ⊔ B from le_sup_left)
        (show B ≤ A ⊔ B from le_sup_right)]
    exact sup_le (fun x hx => hA ⟨x.val, hx⟩) (fun x hx => hB ⟨x.val, hx⟩)
  exact fun x => h (Subgroup.mem_top x)

/-- An extension of a surjection which fixes the extra subgroup is surjective. -/
theorem centralizing_extension_surjective {Z P Q : Subgroup S} (f : P →* Q)
    (hf : Function.Surjective f) (g : (P ⊔ Z : Subgroup S) →* (Q ⊔ Z : Subgroup S))
    (hgP : ∀ x : P, (g ⟨x.val, Subgroup.mem_sup_left x.property⟩).val = (f x).val)
    (hgZ : ∀ z : Z, (g ⟨z.val, Subgroup.mem_sup_right z.property⟩).val = z.val) :
    Function.Surjective g := by
  apply MonoidHom.range_eq_top.mp
  apply top_unique
  rw [← Subgroup.subgroupOf_self (Q ⊔ Z),
    Subgroup.subgroupOf_sup (show Q ≤ Q ⊔ Z from le_sup_left)
      (show Z ≤ Q ⊔ Z from le_sup_right)]
  apply sup_le
  · intro x hx
    obtain ⟨y, hy⟩ := hf ⟨x.val, hx⟩
    refine ⟨⟨y.val, Subgroup.mem_sup_left y.property⟩, ?_⟩
    apply Subtype.ext
    exact (hgP y).trans (congrArg Subtype.val hy)
  · intro x hx
    exact ⟨⟨x.val, Subgroup.mem_sup_right hx⟩, Subtype.ext (hgZ ⟨x.val, hx⟩)⟩

/-- Fusion isomorphisms in a centralizer extend to fusion isomorphisms of joins. -/
theorem centralizingHom_equiv_extension (Z : Subgroup S) {P Q : Subgroup S}
    (e : P ≃* Q) (he : F.CentralizingHom Z e.toMonoidHom) :
    ∃ g : (P ⊔ Z : Subgroup S) ≃* (Q ⊔ Z : Subgroup S),
      F.IsHom g.toMonoidHom ∧
      (∀ x : P, (g ⟨x.val, Subgroup.mem_sup_left x.property⟩).val = (e x).val) ∧
      (∀ z : Z, (g ⟨z.val, Subgroup.mem_sup_right z.property⟩).val = z.val) := by
  obtain ⟨_, g, hg, hgP, hgZ⟩ := he
  exact ⟨MulEquiv.ofBijective g ⟨F.injective g hg,
    centralizing_extension_surjective e.toMonoidHom e.surjective g hgP hgZ⟩,
    hg, hgP, hgZ⟩

theorem centralizingHom_inverse (Z : Subgroup S) {P Q : Subgroup S}
    (e : P ≃* Q) (he : F.CentralizingHom Z e.toMonoidHom) :
    F.CentralizingHom Z e.symm.toMonoidHom := by
  obtain ⟨he, g, hg, hgP, hgZ⟩ := he
  have hsurj : Function.Surjective g := by
    apply MonoidHom.range_eq_top.mp
    apply top_unique
    rw [← Subgroup.subgroupOf_self (Q ⊔ Z),
      Subgroup.subgroupOf_sup (show Q ≤ Q ⊔ Z from le_sup_left)
        (show Z ≤ Q ⊔ Z from le_sup_right)]
    apply sup_le
    · intro x hx
      refine ⟨⟨(e.symm ⟨x.val, hx⟩).val,
        Subgroup.mem_sup_left (e.symm ⟨x.val, hx⟩).property⟩, ?_⟩
      apply Subtype.ext
      exact (hgP (e.symm ⟨x.val, hx⟩)).trans
        (congrArg Subtype.val (e.apply_symm_apply ⟨x.val, hx⟩))
    · intro x hx
      exact ⟨⟨x.val, Subgroup.mem_sup_right hx⟩, Subtype.ext (hgZ ⟨x.val, hx⟩)⟩
  let e' := MulEquiv.ofBijective g ⟨F.injective g hg, hsurj⟩
  refine ⟨F.inverse_mem e he, e'.symm.toMonoidHom, F.inverse_mem e' hg, ?_, ?_⟩
  · intro x
    have h : e' ⟨(e.symm x).val, Subgroup.mem_sup_left (e.symm x).property⟩ =
        ⟨x.val, Subgroup.mem_sup_left x.property⟩ := by
      apply Subtype.ext
      exact (hgP (e.symm x)).trans (congrArg Subtype.val (e.apply_symm_apply x))
    exact congrArg Subtype.val ((e'.symm_apply_eq).mpr h.symm)
  · intro z
    have h : e' ⟨z.val, Subgroup.mem_sup_right z.property⟩ =
        ⟨z.val, Subgroup.mem_sup_right z.property⟩ := Subtype.ext (hgZ z)
    exact congrArg Subtype.val ((e'.symm_apply_eq).mpr h.symm)

theorem centralizingHom_codomain_restrict (Z : Subgroup S) {P Q R : Subgroup S}
    (f : P →* Q) (hf : F.CentralizingHom Z f) (hRQ : R ≤ Q)
    (f' : P →* R) (hff' : (subgroupInclusion R Q hRQ).comp f' = f) :
    F.CentralizingHom Z f' := by
  obtain ⟨hf, g, hg, hgP, hgZ⟩ := hf
  have hmem : ∀ x, (g x).val ∈ R ⊔ Z := by
    apply join_image_mem g ((R ⊔ Z).subgroupOf (Q ⊔ Z))
    · intro x
      change (g _).val ∈ R ⊔ Z
      rw [hgP x, ← hff']
      exact Subgroup.mem_sup_left (f' x).property
    · intro z
      change (g _).val ∈ R ⊔ Z
      rw [hgZ z]
      exact Subgroup.mem_sup_right z.property
  let g' : (P ⊔ Z : Subgroup S) →* (R ⊔ Z : Subgroup S) :=
    { toFun x := ⟨(g x).val, hmem x⟩
      map_one' := Subtype.ext (congrArg (fun x : (Q ⊔ Z : Subgroup S) => x.val) g.map_one)
      map_mul' x y := Subtype.ext
        (congrArg (fun x : (Q ⊔ Z : Subgroup S) => x.val) (g.map_mul x y)) }
  refine ⟨F.codomain_restrict_mem f hf hRQ f' hff', g',
    F.codomain_restrict_mem g hg (sup_le_sup_right hRQ Z) g' (by ext; rfl), ?_, ?_⟩
  · intro x
    exact (hgP x).trans (congrArg (fun h : P →* Q => (h x).val) hff'.symm)
  · exact hgZ

theorem centralizingHom_conjugation (Z : Subgroup S) (hZ : Z ≤ Subgroup.center S)
    (P Q : Subgroup S) (s : S) (h : ∀ x ∈ P, s⁻¹ * x * s ∈ Q) :
    F.CentralizingHom Z (subgroupConjugation P Q s h) := by
  have hfix : ∀ z ∈ Z, s⁻¹ * z * s = z := by
    intro z hz
    have hc := (Subgroup.mem_center_iff.mp (hZ hz)) s
    calc
      s⁻¹ * z * s = s⁻¹ * (z * s) := mul_assoc _ _ _
      _ = s⁻¹ * (s * z) := congrArg (s⁻¹ * ·) hc.symm
      _ = z := inv_mul_cancel_left s z
  have hsup : ∀ x ∈ P ⊔ Z, s⁻¹ * x * s ∈ Q ⊔ Z := by
    have hle : P ⊔ Z ≤ (Q ⊔ Z).comap (MulAut.conj s⁻¹).toMonoidHom := by
      apply sup_le
      · intro x hx
        change s⁻¹ * x * (s⁻¹)⁻¹ ∈ Q ⊔ Z
        simpa only [inv_inv] using Subgroup.mem_sup_left (h x hx)
      · intro z hz
        change s⁻¹ * z * (s⁻¹)⁻¹ ∈ Q ⊔ Z
        simpa only [inv_inv, hfix z hz] using Subgroup.mem_sup_right hz
    intro x hx
    have hx' := hle hx
    change s⁻¹ * x * (s⁻¹)⁻¹ ∈ Q ⊔ Z at hx'
    simpa only [inv_inv] using hx'
  exact ⟨F.conjugation_mem _ _ _ _, subgroupConjugation _ _ s hsup,
    F.conjugation_mem _ _ _ _, (fun _ => rfl), (fun z => hfix z.val z.property)⟩

/-- The fusion system of morphisms admitting extensions that fix `Z`. -/
def centralizingSystem (Z : Subgroup S) (hZ : Z ≤ Subgroup.center S) : FusionSystem S where
  IsHom := F.CentralizingHom Z
  injective f hf := F.injective f hf.1
  id_mem := F.centralizingHom_id Z
  comp_mem f g := F.centralizingHom_comp Z f g
  inclusion_mem := F.centralizingHom_inclusion Z
  conjugation_mem := F.centralizingHom_conjugation Z hZ
  inverse_mem := F.centralizingHom_inverse Z
  codomain_restrict_mem f hf hRQ g hgf :=
    F.centralizingHom_codomain_restrict Z f hf hRQ g hgf

theorem centralizingSystem_central (Z : Subgroup S) (hZ : Z ≤ Subgroup.center S) :
    (F.centralizingSystem Z hZ).CentralSubgroup Z := by
  refine ⟨hZ, ?_⟩
  intro P Q f hf
  obtain ⟨_, g, hg, hgP, hgZ⟩ := hf
  refine ⟨g, ⟨hg, ?_⟩, hgP, hgZ⟩
  let pre := subgroupInclusion ((P ⊔ Z) ⊔ Z) (P ⊔ Z)
    (sup_le le_rfl le_sup_right)
  let post := subgroupInclusion (Q ⊔ Z) ((Q ⊔ Z) ⊔ Z) le_sup_left
  exact ⟨post.comp (g.comp pre),
    F.comp_mem _ _ (F.comp_mem _ _ (F.inclusion_mem _) hg) (F.inclusion_mem _),
    (fun _ => rfl), hgZ⟩

variable [Finite S] (p : ℕ) (E : F.ElementaryCategory p)

/-- The actual centralizer fusion system, with no saturation assumption. -/
def centralizerSystem : FusionSystem (F.centralizerGroup p E) :=
  (F.subgroupRestriction (F.centralizerGroup p E)).centralizingSystem
    (F.elementaryInCentralizer p E) (by
      intro z hz
      apply Subgroup.mem_center_iff.mpr
      intro t
      apply Subtype.ext
      exact ((Subgroup.mem_centralizer_iff.mp t.property) z.val hz).symm)

theorem centralizerSystem_hom_iff {P Q : Subgroup (F.centralizerGroup p E)} (f : P →* Q) :
    (F.centralizerSystem p E).IsHom f ↔
      F.IsHom (ambientHom (F.centralizerGroup p E) f) ∧
      ∃ g : (P ⊔ F.elementaryInCentralizer p E : Subgroup (F.centralizerGroup p E)) →*
          (Q ⊔ F.elementaryInCentralizer p E : Subgroup (F.centralizerGroup p E)),
        F.IsHom (ambientHom (F.centralizerGroup p E) g) ∧
        (∀ x : P, (g ⟨x.val, Subgroup.mem_sup_left x.property⟩).val = (f x).val) ∧
        (∀ z : F.elementaryInCentralizer p E,
          (g ⟨z.val, Subgroup.mem_sup_right z.property⟩).val = z.val) := Iff.rfl

theorem centralizerSystem_central :
    (F.centralizerSystem p E).CentralSubgroup (F.elementaryInCentralizer p E) :=
  (F.subgroupRestriction (F.centralizerGroup p E)).centralizingSystem_central _ _

end Sharpness.FusionSystem

