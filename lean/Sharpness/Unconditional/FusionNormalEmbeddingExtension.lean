import Sharpness.Unconditional.FusionSystemGroupTransportFinite

/-! A conjugation map on an embedded subgroup extends over its join with
an actual normal subgroup lying in the embedding image. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness
variable {T G : Type u} [Group T] [Group G]

/-- A completely explicit extension domain; no saturation premise is needed. -/
theorem embedding_conjugation_extends_over_normal
    (i : T →* G) (hi : Function.Injective i)
    (O : Subgroup G) [O.Normal] (hOi : O ≤ i.range)
    (P : Subgroup T) (f : P →* T) (g : G)
    (hf : ∀ x : P, i (f x) = g * i x.val * g⁻¹) :
    ∃ Q : Subgroup T, ∃ hPQ : P ≤ Q,
      O ≤ Q.map i ∧ ∃ t : Q →* T,
        (∀ x : Q, i (t x) = g * i x.val * g⁻¹) ∧
        (∀ x : P, t ⟨x.val, hPQ x.property⟩ = f x) := by
  let Q := P ⊔ O.comap i
  let D := i.range.comap ((MulAut.conj g).toMonoidHom.comp i)
  have hPD : P ≤ D := by
    intro x hx
    exact ⟨f ⟨x, hx⟩, hf ⟨x, hx⟩⟩
  have hOD : O.comap i ≤ D := by
    intro x hx
    exact hOi (Subgroup.Normal.conj_mem inferInstance (i x) hx g)
  have hQD : Q ≤ D := sup_le hPD hOD
  let m : Q →* i.range :=
    (((MulAut.conj g).toMonoidHom.comp i).comp Q.subtype).codRestrict i.range
      (fun x => hQD x.property)
  let e := MonoidHom.ofInjective hi
  let t : Q →* T := e.symm.toMonoidHom.comp m
  have ht (x : Q) : i (t x) = g * i x.val * g⁻¹ :=
    congrArg (fun z : i.range => z.val) (e.apply_symm_apply (m x))
  refine ⟨Q, le_sup_left, ?_, t, ht, fun x => ?_⟩
  · intro y hy
    obtain ⟨z, hz⟩ := hOi hy
    have hzo : z ∈ O.comap i := by change i z ∈ O; rw [hz]; exact hy
    exact ⟨z, Subgroup.mem_sup_right hzo, hz⟩
  · apply hi
    exact (ht ⟨x.val, Subgroup.mem_sup_left x.property⟩).trans (hf x).symm

end Sharpness
