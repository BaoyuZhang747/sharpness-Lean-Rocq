import Sharpness.QuotientImage

/-! The quotient fusion system by a central subgroup, constructed from
actual lifts. Its fusion-system axioms do not require saturation. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem
open CategoryTheory
variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)
    {Z : Subgroup S} [Z.Normal] (hZ : F.CentralSubgroup Z)

theorem quotientInducedHom_injective {A B : Subgroup (S ⧸ Z)}
    (f : (⟨F.quotientPreimage Z A⟩ : F.Object) ⟶ ⟨F.quotientPreimage Z B⟩) :
    Function.Injective (F.quotientInducedHom hZ f) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply le_antisymm _ bot_le
  intro a ha
  obtain ⟨x, rfl⟩ := F.subgroupProjection_surjective Z A a
  have he : F.subgroupProjection Z B (f.val x) = 1 := by
    simpa only [MonoidHom.mem_ker, F.quotientInducedHom_apply] using ha
  have hz : (f.val x).val ∈ Z :=
    (QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val he)
  let z : F.quotientPreimage Z A :=
    ⟨(f.val x).val, (QuotientGroup.le_comap_mk' Z A) hz⟩
  have hfx : f.val z = f.val x := by
    apply Subtype.ext
    exact F.central_fixed_element hZ f.val f.property z hz
  have hx : x = z := (F.injective f.val f.property hfx).symm
  change F.subgroupProjection Z A x = 1
  apply Subtype.ext
  change (QuotientGroup.mk x.val : S ⧸ Z) = 1
  rw [hx]
  exact (QuotientGroup.eq_one_iff _).mpr hz

theorem quotientInducedHom_surjective_iff {A B : Subgroup (S ⧸ Z)}
    (f : (⟨F.quotientPreimage Z A⟩ : F.Object) ⟶ ⟨F.quotientPreimage Z B⟩) :
    Function.Surjective (F.quotientInducedHom hZ f) ↔ Function.Surjective f.val := by
  constructor
  · intro hf y
    apply (F.quotient_image_iff hZ f y).mp
    exact hf (F.subgroupProjection Z B y)
  · intro hf y
    obtain ⟨y', rfl⟩ := F.subgroupProjection_surjective Z B y
    obtain ⟨x, rfl⟩ := hf y'
    exact ⟨F.subgroupProjection Z A x, F.quotientInducedHom_apply hZ f x⟩

@[simp] theorem quotientInducedHom_id (A : Subgroup (S ⧸ Z)) :
    F.quotientInducedHom hZ (𝟙 (⟨F.quotientPreimage Z A⟩ : F.Object)) =
      MonoidHom.id A := by
  ext a
  obtain ⟨x, rfl⟩ := F.subgroupProjection_surjective Z A a
  exact congrArg Subtype.val (F.quotientInducedHom_apply hZ (𝟙 _) x)

@[simp] theorem quotientInducedHom_comp {A B C : Subgroup (S ⧸ Z)}
    (f : (⟨F.quotientPreimage Z A⟩ : F.Object) ⟶ ⟨F.quotientPreimage Z B⟩)
    (g : (⟨F.quotientPreimage Z B⟩ : F.Object) ⟶ ⟨F.quotientPreimage Z C⟩) :
    F.quotientInducedHom hZ (f ≫ g) =
      (F.quotientInducedHom hZ g).comp (F.quotientInducedHom hZ f) := by
  apply MonoidHom.ext
  intro a
  obtain ⟨x, rfl⟩ := F.subgroupProjection_surjective Z A a
  change F.quotientInducedHom hZ (f ≫ g) (F.subgroupProjection Z A x) =
    F.quotientInducedHom hZ g (F.quotientInducedHom hZ f (F.subgroupProjection Z A x))
  rw [F.quotientInducedHom_apply, F.quotientInducedHom_apply,
    F.quotientInducedHom_apply]
  rfl

/-- Admissible quotient maps are precisely the maps induced by admissible
maps between their full preimages. -/
def centralQuotient : FusionSystem (S ⧸ Z) where
  IsHom := fun {A B} g =>
    ∃ f : (⟨F.quotientPreimage Z A⟩ : F.Object) ⟶ ⟨F.quotientPreimage Z B⟩,
      F.quotientInducedHom hZ f = g
  injective := by
    rintro A B g ⟨f, rfl⟩
    exact F.quotientInducedHom_injective hZ f
  id_mem := by
    intro A
    exact ⟨𝟙 _, F.quotientInducedHom_id hZ A⟩
  comp_mem := by
    rintro A B C g h ⟨f, rfl⟩ ⟨f', rfl⟩
    exact ⟨f ≫ f', F.quotientInducedHom_comp hZ f f'⟩
  inclusion_mem := by
    intro A B hAB
    refine ⟨F.inclusion (Subgroup.comap_mono hAB), ?_⟩
    apply MonoidHom.ext
    intro a
    obtain ⟨x, rfl⟩ := F.subgroupProjection_surjective Z A a
    rw [F.quotientInducedHom_apply]
    rfl
  conjugation_mem := by
    intro A B s h
    obtain ⟨t, rfl⟩ := QuotientGroup.mk'_surjective Z s
    have ht : ∀ x ∈ F.quotientPreimage Z A,
        t⁻¹ * x * t ∈ F.quotientPreimage Z B := by
      intro x hx
      change (QuotientGroup.mk' Z) (t⁻¹ * x * t) ∈ B
      simpa only [map_mul, map_inv] using h ((QuotientGroup.mk' Z) x) hx
    let f : (⟨F.quotientPreimage Z A⟩ : F.Object) ⟶ ⟨F.quotientPreimage Z B⟩ :=
      ⟨subgroupConjugation _ _ t ht, F.conjugation_mem _ _ t ht⟩
    refine ⟨f, ?_⟩
    apply MonoidHom.ext
    intro a
    obtain ⟨x, rfl⟩ := F.subgroupProjection_surjective Z A a
    rw [F.quotientInducedHom_apply]
    apply Subtype.ext
    change (QuotientGroup.mk' Z) (t⁻¹ * x.val * t) = _
    simp only [map_mul, map_inv]
    rfl
  inverse_mem := by
    rintro A B e ⟨f, hf⟩
    have hs : Function.Surjective f.val :=
      (F.quotientInducedHom_surjective_iff hZ f).mp (hf ▸ e.surjective)
    let e' := MulEquiv.ofBijective f.val ⟨F.injective f.val f.property, hs⟩
    let fi : (⟨F.quotientPreimage Z B⟩ : F.Object) ⟶ ⟨F.quotientPreimage Z A⟩ :=
      ⟨e'.symm.toMonoidHom, F.inverse_mem e' f.property⟩
    refine ⟨fi, ?_⟩
    apply MonoidHom.ext
    intro b
    obtain ⟨y, rfl⟩ := F.subgroupProjection_surjective Z B b
    rw [F.quotientInducedHom_apply]
    apply e.injective
    change e (F.subgroupProjection Z A (e'.symm y)) =
      e (e.symm (F.subgroupProjection Z B y))
    rw [e.apply_symm_apply]
    have hh := F.quotientInducedHom_apply hZ f (e'.symm y)
    rw [hf] at hh
    exact hh.trans (congrArg (F.subgroupProjection Z B) (e'.apply_symm_apply y))
  codomain_restrict_mem := by
    rintro A B C g ⟨f, hf⟩ hCB g' hgg'
    have himg (x : F.quotientPreimage Z A) : (f.val x).val ∈ F.quotientPreimage Z C := by
      have hh := F.quotientInducedHom_apply hZ f x
      rw [hf, ← hgg'] at hh
      have hv := congrArg Subtype.val hh
      change (g' (F.subgroupProjection Z A x)).val =
        (QuotientGroup.mk (f.val x).val : S ⧸ Z) at hv
      change (QuotientGroup.mk (f.val x).val : S ⧸ Z) ∈ C
      rw [← hv]
      exact (g' (F.subgroupProjection Z A x)).property
    let f' : F.quotientPreimage Z A →* F.quotientPreimage Z C :=
      { toFun x := ⟨(f.val x).val, himg x⟩
        map_one' := by
          apply Subtype.ext
          exact congrArg (fun y : F.quotientPreimage Z B => y.val) (map_one f.val)
        map_mul' x y := by
          apply Subtype.ext
          exact congrArg (fun y : F.quotientPreimage Z B => y.val) (map_mul f.val x y) }
    have hf' : F.IsHom f' := F.codomain_restrict_mem f.val f.property
      (Subgroup.comap_mono hCB) f' (by ext x; rfl)
    refine ⟨⟨f', hf'⟩, ?_⟩
    apply MonoidHom.ext
    intro a
    obtain ⟨x, rfl⟩ := F.subgroupProjection_surjective Z A a
    rw [F.quotientInducedHom_apply]
    apply Subtype.ext
    have hh := F.quotientInducedHom_apply hZ f x
    rw [hf, ← hgg'] at hh
    exact (congrArg Subtype.val hh).symm

@[simp] theorem centralQuotient_isHom_iff {A B : Subgroup (S ⧸ Z)} (g : A →* B) :
    (F.centralQuotient hZ).IsHom g ↔
      ∃ f : (⟨F.quotientPreimage Z A⟩ : F.Object) ⟶ ⟨F.quotientPreimage Z B⟩,
        F.quotientInducedHom hZ f = g := Iff.rfl

end Sharpness.FusionSystem
