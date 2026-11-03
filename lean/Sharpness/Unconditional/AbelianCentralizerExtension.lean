import Sharpness.Unconditional.AbelianCentralizerConstruction
import Sharpness.Unconditional.CentralizerSaturationExtension

set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem
variable {S : Type u} [Group S] [Finite S]

/-- The receptivity part of centralizer saturation holds whenever the
target join with `E` is fully centralized in the ambient fusion system. -/
theorem abelianCentralizerSystem_receptive_of_join_fullyCentralized
    (F : FusionSystem S) (p : ℕ) (sat : F.Saturated p) (E : F.AbelianCentralizerData)
    (Q : Subgroup (F.abelianCentralizerGroup E))
    (hQ : F.FullyCentralized (ambientSubgroup (F.abelianCentralizerGroup E)
      (Q ⊔ F.abelianInCentralizer E))) :
    (F.abelianCentralizerSystem E).Receptive Q := by
  let T := F.abelianCentralizerGroup E
  let Z := F.abelianInCentralizer E
  let C := F.abelianCentralizerSystem E
  have hZ : Z ≤ Subgroup.center T := (F.abelianCentralizerSystem_central E).in_center
  intro P e he
  obtain ⟨g, hg, hgP, hgZ⟩ :=
    (F.subgroupRestriction T).centralizingHom_equiv_extension Z e he
  let a := (subgroupAmbientEquiv T (P ⊔ Z)).symm.trans
    (g.trans (subgroupAmbientEquiv T (Q ⊔ Z)))
  have ha : F.IsHom a.toMonoidHom := hg
  obtain ⟨M, hAM, hM, f, hf, hfa⟩ := sat.extension a ha hQ
  let N := C.extensionDomainSubgroup e
  have hPN : P ≤ N := C.le_extensionDomainSubgroup e
  have hZN : Z ≤ N := (hZ.trans (Subgroup.center_le_centralizer _)).trans
    (C.centralizer_le_extensionDomainSubgroup e)
  have hNM : ambientSubgroup T N ≤ M := by
    intro x hx
    rw [← SetLike.mem_coe, hM]
    exact centralizing_extensionDomain_ambient_le F T C hZ e g hgP hgZ hx
  have hfixZ : ∀ z : Z,
      (f ⟨z.val.val, hNM ⟨z.val, hZN z.property, rfl⟩⟩).val = z.val.val := by
    intro z
    let zJ : (P ⊔ Z : Subgroup T) := ⟨z.val, Subgroup.mem_sup_right z.property⟩
    have hh := hfa (subgroupAmbientEquiv T (P ⊔ Z) zJ)
    change (f ⟨z.val.val, _⟩).val =
      (ambientHom T g.toMonoidHom (subgroupAmbientEquiv T (P ⊔ Z) zJ)).val at hh
    rw [ambientHom_apply] at hh
    exact hh.trans (congrArg (fun t : T => t.val) (hgZ z))
  have hmem : ∀ n : N,
      (f ⟨n.val.val, hNM ⟨n.val, n.property, rfl⟩⟩).val ∈ T := by
    intro n
    apply Subgroup.mem_centralizer_iff.mpr
    intro z hz
    let zT : T := ⟨z, F.abelian_le_centralizer E hz⟩
    let zZ : Z := ⟨zT, hz⟩
    let zn : M := ⟨z, hNM ⟨zT, hZN hz, rfl⟩⟩
    let nn : M := ⟨n.val.val, hNM ⟨n.val, n.property, rfl⟩⟩
    have hcomm : zn * nn = nn * zn := by
      apply Subtype.ext
      exact (Subgroup.mem_centralizer_iff.mp n.val.property) z hz
    have hh := congrArg (fun m : M => (f m).val) hcomm
    have hzz : (f zn).val = z := hfixZ zZ
    simpa only [map_mul, Subgroup.coe_mul, hzz] using hh
  let fN : N →* (⊤ : Subgroup T) :=
    { toFun n := ⟨⟨(f ⟨n.val.val, hNM ⟨n.val, n.property, rfl⟩⟩).val, hmem n⟩, trivial⟩
      map_one' := by
        apply Subtype.ext
        apply Subtype.ext
        exact congrArg (fun x : (⊤ : Subgroup S) => x.val) f.map_one
      map_mul' n m := by
        apply Subtype.ext
        apply Subtype.ext
        exact congrArg (fun x : (⊤ : Subgroup S) => x.val)
          (f.map_mul ⟨n.val.val, hNM ⟨n.val, n.property, rfl⟩⟩
            ⟨m.val.val, hNM ⟨m.val, m.property, rfl⟩⟩) }
  have hfN : F.IsHom (ambientHom T fN) := by
    apply F.codomain_restrict_mem (f.comp (subgroupInclusion _ _ hNM))
      (F.comp_mem _ _ (F.inclusion_mem hNM) hf) le_top (ambientHom T fN)
    apply MonoidHom.ext
    intro x
    obtain ⟨n, rfl⟩ := (subgroupAmbientEquiv T N).surjective x
    apply Subtype.ext
    change (ambientHom T fN (subgroupAmbientEquiv T N n)).val = _
    rw [ambientHom_apply]
    rfl
  have hfixN : ∀ z : Z, (fN ⟨z.val, hZN z.property⟩).val = z.val := by
    intro z
    apply Subtype.ext
    exact hfixZ z
  refine ⟨fN, centralizingHom_of_fixes (F.subgroupRestriction T) hZN fN hfN hfixN, ?_⟩
  intro x
  apply Subtype.ext
  let xJ : (P ⊔ Z : Subgroup T) := ⟨x.val, Subgroup.mem_sup_left x.property⟩
  have hh := hfa (subgroupAmbientEquiv T (P ⊔ Z) xJ)
  change (f ⟨x.val.val, _⟩).val =
    (ambientHom T g.toMonoidHom (subgroupAmbientEquiv T (P ⊔ Z) xJ)).val at hh
  rw [ambientHom_apply] at hh
  exact hh.trans (congrArg (fun t : T => t.val) (hgP x))

end Sharpness.FusionSystem
