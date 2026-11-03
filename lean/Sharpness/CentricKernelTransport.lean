import Sharpness.CentricKernel

/-! Transport of the inner-kernel result from a fully normalized conjugate.
The hypothesis is the literal centralizer condition at every F-conjugate;
it is supplied from quotient centricity in QuotientCentric. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem
open CategoryTheory
variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)
    (p : ℕ) [Fact p.Prime] (hS : IsPGroup p S) (sat : F.Saturated p)
    {Z : Subgroup S} [Z.Normal] (hZ : F.CentralSubgroup Z)
    (P : Subgroup S) (hZP : Z ≤ P)

include p hS sat

theorem gamma_inner_of_conjugate_centralizers
    (centric : ∀ (Q : Subgroup S) (e : P ≃* Q), F.IsHom e.toMonoidHom →
      Subgroup.centralizer (Q.map (QuotientGroup.mk' Z) : Set (S ⧸ Z)) ≤
        Q.map (QuotientGroup.mk' Z)) :
    letI := F.central_subgroupOf_normal hZ P
    ∀ a : F.Gamma hZ hZP, ∃ r : P, ∀ x : P, a.val.val x = r⁻¹ * x * r := by
  letI := F.central_subgroupOf_normal hZ P
  intro a
  obtain ⟨Q, e, he, hn⟩ := F.exists_fullyNormalized P
  have hZQ := (F.central_containment_iff hZ e he).mp hZP
  letI := F.central_subgroupOf_normal hZ Q
  let f : (⟨Q⟩ : F.Object) ⟶ ⟨P⟩ := (F.isoOfMulEquiv e he).inv
  let g : (⟨Q⟩ : F.Object) ⟶ ⟨P⟩ :=
    f ≫ (F.isoOfMulEquiv a.val.val a.val.property).hom
  have same : ∀ x : Q, (f.val x).val⁻¹ * (g.val x).val ∈ Z := by
    intro x
    exact F.gamma_modZ hZ hZP a (f.val x)
  obtain ⟨b, hb⟩ := F.exists_gamma_of_same_modZ hZ hZQ f g same
  obtain ⟨r, hr⟩ := F.gamma_inner_fullyNormalized p hS sat hZ Q hZQ hn
    (centric Q e he) b
  refine ⟨e.symm r, ?_⟩
  intro x
  have hv := congrArg (fun t : (⟨Q⟩ : F.Object) ⟶ ⟨P⟩ => t.val (e x)) hb
  change e.symm (b.val.val (e x)) = a.val.val (e.symm (e x)) at hv
  rw [hr, e.symm_apply_apply] at hv
  simpa only [map_mul, map_inv, e.symm_apply_apply] using hv.symm

end Sharpness.FusionSystem
