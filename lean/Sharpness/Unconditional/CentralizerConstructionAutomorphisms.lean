import Sharpness.Unconditional.CentralizerConstruction

/-! The automorphism restriction in the centralizer saturation proof:
automorphisms of `PZ` preserving `P` and fixing `Z` restrict bijectively to
centralizer automorphisms of `P`. -/
set_option autoImplicit false
noncomputable section
universe u v
namespace Sharpness.FusionSystem
variable {S : Type u} [Group S] (F : FusionSystem S)

theorem join_hom_ext {P Z : Subgroup S} {G : Type v} [Group G]
    {f g : (P ⊔ Z : Subgroup S) →* G}
    (hP : ∀ x : P, f ⟨x.val, Subgroup.mem_sup_left x.property⟩ =
      g ⟨x.val, Subgroup.mem_sup_left x.property⟩)
    (hZ : ∀ z : Z, f ⟨z.val, Subgroup.mem_sup_right z.property⟩ =
      g ⟨z.val, Subgroup.mem_sup_right z.property⟩) : f = g := by
  have h : (⊤ : Subgroup (P ⊔ Z : Subgroup S)) ≤ f.eqLocus g := by
    rw [← Subgroup.subgroupOf_self (P ⊔ Z),
      Subgroup.subgroupOf_sup (show P ≤ P ⊔ Z from le_sup_left)
        (show Z ≤ P ⊔ Z from le_sup_right)]
    exact sup_le (fun x hx => hP ⟨x.val, hx⟩) (fun x hx => hZ ⟨x.val, hx⟩)
  exact MonoidHom.ext (fun x => h (Subgroup.mem_top x))

/-- The actual automorphisms of `PZ` preserving `P` and fixing `Z`. -/
def centralizingJoinAutomorphisms (Z P : Subgroup S) : Subgroup (MulAut (P ⊔ Z : Subgroup S)) where
  carrier a := F.IsHom a.toMonoidHom ∧
    (∀ x : (P ⊔ Z : Subgroup S), (a x).val ∈ P ↔ x.val ∈ P) ∧
    (∀ z : Z, (a ⟨z.val, Subgroup.mem_sup_right z.property⟩).val = z.val)
  one_mem' := ⟨F.id_mem _, (fun _ => Iff.rfl), (fun _ => rfl)⟩
  mul_mem' {a b} ha hb := by
    refine ⟨F.comp_mem _ _ hb.1 ha.1, ?_, ?_⟩
    · intro x
      exact (ha.2.1 (b x)).trans (hb.2.1 x)
    · intro z
      change (a (b ⟨z.val, Subgroup.mem_sup_right z.property⟩)).val = z.val
      have hbz : b ⟨z.val, Subgroup.mem_sup_right z.property⟩ =
          ⟨z.val, Subgroup.mem_sup_right z.property⟩ := Subtype.ext (hb.2.2 z)
      rw [hbz]
      exact ha.2.2 z
  inv_mem' {a} ha := by
    refine ⟨F.inverse_mem a ha.1, ?_, ?_⟩
    · intro x
      change (a.symm x).val ∈ P ↔ x.val ∈ P
      simpa only [MulEquiv.apply_symm_apply] using (ha.2.1 (a.symm x)).symm
    · intro z
      have haz : a ⟨z.val, Subgroup.mem_sup_right z.property⟩ =
          ⟨z.val, Subgroup.mem_sup_right z.property⟩ := Subtype.ext (ha.2.2 z)
      exact congrArg Subtype.val ((a.symm_apply_eq).mpr haz.symm)

def centralizingJoinRestriction (Z P : Subgroup S)
    (a : F.centralizingJoinAutomorphisms Z P) : MulAut P where
  toFun x := ⟨(a.val ⟨x.val, Subgroup.mem_sup_left x.property⟩).val,
    (a.property.2.1 _).mpr x.property⟩
  invFun x := ⟨(a.val.symm ⟨x.val, Subgroup.mem_sup_left x.property⟩).val, by
    have h := (a.property.2.1 (a.val.symm ⟨x.val, Subgroup.mem_sup_left x.property⟩)).mp
    exact h (by simpa only [MulEquiv.apply_symm_apply] using x.property)⟩
  left_inv x := by
    apply Subtype.ext
    exact congrArg (fun y : (P ⊔ Z : Subgroup S) => y.val)
      (a.val.symm_apply_apply ⟨x.val, Subgroup.mem_sup_left x.property⟩)
  right_inv x := by
    apply Subtype.ext
    exact congrArg (fun y : (P ⊔ Z : Subgroup S) => y.val)
      (a.val.apply_symm_apply ⟨x.val, Subgroup.mem_sup_left x.property⟩)
  map_mul' x y := by
    apply Subtype.ext
    exact congrArg (fun y : (P ⊔ Z : Subgroup S) => y.val) (a.val.map_mul
      ⟨x.val, Subgroup.mem_sup_left x.property⟩ ⟨y.val, Subgroup.mem_sup_left y.property⟩)

theorem centralizingJoinRestriction_allowed (Z P : Subgroup S)
    (a : F.centralizingJoinAutomorphisms Z P) :
    F.CentralizingHom Z (F.centralizingJoinRestriction Z P a).toMonoidHom := by
  have h : F.IsHom (F.centralizingJoinRestriction Z P a).toMonoidHom := by
    apply F.codomain_restrict_mem
      (a.val.toMonoidHom.comp (subgroupInclusion P (P ⊔ Z) le_sup_left))
      (F.comp_mem _ _ (F.inclusion_mem _) a.property.1) le_sup_left
    ext x
    rfl
  exact ⟨h, a.val.toMonoidHom, a.property.1, (fun _ => rfl), a.property.2.2⟩

theorem centralizingJoinRestriction_injective (Z P : Subgroup S) :
    Function.Injective (F.centralizingJoinRestriction Z P) := by
  intro a b hab
  apply Subtype.ext
  apply MulEquiv.toMonoidHom_injective
  apply join_hom_ext
  · intro x
    apply Subtype.ext
    exact congrArg (fun e : MulAut P => (e x).val) hab
  · intro z
    apply Subtype.ext
    exact (a.property.2.2 z).trans (b.property.2.2 z).symm

theorem centralizingJoinRestriction_surjective (Z P : Subgroup S)
    (e : MulAut P) (he : F.CentralizingHom Z e.toMonoidHom) :
    ∃ a : F.centralizingJoinAutomorphisms Z P,
      F.centralizingJoinRestriction Z P a = e := by
  obtain ⟨g, hg, hgP, hgZ⟩ := F.centralizingHom_equiv_extension Z e he
  have hpres : ∀ x : (P ⊔ Z : Subgroup S), (g x).val ∈ P ↔ x.val ∈ P := by
    intro x
    constructor
    · intro hx
      let y := e.symm ⟨(g x).val, hx⟩
      have hy : g ⟨y.val, Subgroup.mem_sup_left y.property⟩ = g x := by
        apply Subtype.ext
        exact (hgP y).trans (congrArg Subtype.val (e.apply_symm_apply ⟨(g x).val, hx⟩))
      have hxy := congrArg Subtype.val (g.injective hy)
      exact hxy ▸ y.property
    · intro hx
      rw [hgP ⟨x.val, hx⟩]
      exact (e ⟨x.val, hx⟩).property
  refine ⟨⟨g, hg, hpres, hgZ⟩, ?_⟩
  ext x
  exact hgP x

variable [Finite S]

/-- Restriction identifies the two actual automorphism groups used in
the fully automized part of centralizer saturation. -/
def centralizingAutomorphismEquiv (Z P : Subgroup S) (hZ : Z ≤ Subgroup.center S) :
    F.centralizingJoinAutomorphisms Z P ≃*
      (F.centralizingSystem Z hZ).automorphismSubgroup P :=
  MulEquiv.ofBijective
    ({ toFun a := ⟨F.centralizingJoinRestriction Z P a,
        F.centralizingJoinRestriction_allowed Z P a⟩
       map_one' := by apply Subtype.ext; ext; rfl
       map_mul' a b := by apply Subtype.ext; ext; rfl } :
      F.centralizingJoinAutomorphisms Z P →*
        (F.centralizingSystem Z hZ).automorphismSubgroup P)
    ⟨fun a b h => F.centralizingJoinRestriction_injective Z P (congrArg Subtype.val h),
      fun e => by
        obtain ⟨a, ha⟩ := F.centralizingJoinRestriction_surjective Z P e.val e.property
        exact ⟨a, Subtype.ext ha⟩⟩

end Sharpness.FusionSystem
