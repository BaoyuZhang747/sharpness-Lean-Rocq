import Sharpness.Unconditional.AlperinNormalizer
import Sharpness.CentralAutomorphisms

/-! The normal-subgroup case of centric extension rigidity. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness

def autPointwiseFixer {G : Type u} [Group G] (A : Subgroup (MulAut G))
    (N : Subgroup G) : Subgroup A where
  carrier := {a | ∀ n : N, a.val n.val = n.val}
  one_mem' _ := rfl
  mul_mem' {a b} ha hb n := by
    change a.val (b.val n.val) = n.val
    rw [hb n, ha n]
  inv_mem' {a} ha n := by
    change a.val.symm n.val = n.val
    calc
      a.val.symm n.val = a.val.symm (a.val n.val) := congrArg a.val.symm (ha n).symm
      _ = n.val := a.val.symm_apply_apply n.val

theorem autPointwiseFixer_mod_normal {G : Type u} [Group G]
    (A : Subgroup (MulAut G)) (N : Subgroup G) [N.Normal]
    (hN : Subgroup.centralizer (N : Set G) ≤ N)
    (a : autPointwiseFixer A N) (x : G) : x⁻¹ * a.val.val x ∈ N := by
  apply hN
  apply Subgroup.mem_centralizer_iff.mpr
  intro n hn
  have hc := a.property ⟨x * n * x⁻¹, (inferInstance : N.Normal).conj_mem n hn x⟩
  change a.val.val (x * n * x⁻¹) = x * n * x⁻¹ at hc
  rw [map_mul, map_mul, map_inv, a.property ⟨n, hn⟩] at hc
  have hh := congrArg (fun y : G => x⁻¹ * y * a.val.val x) hc
  simpa [mul_assoc] using hh.symm

theorem autPointwiseFixer_isPGroup {G : Type u} [Group G] [Finite G]
    (p : ℕ) [Fact p.Prime] (hG : IsPGroup p G)
    (A : Subgroup (MulAut G)) (N : Subgroup G) [N.Normal]
    (hN : Subgroup.centralizer (N : Set G) ≤ N) :
    IsPGroup p (autPointwiseFixer A N) :=
  subgroup_isPGroup_of_delta A.subtype (autPointwiseFixer A N) N
    (fun a n => a.property n) (autPointwiseFixer_mod_normal A N hN)
    p (hG.to_subgroup N) Subtype.val_injective

namespace FusionSystem
open CategoryTheory
open scoped Pointwise
variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)

theorem pSubgroup_transport_to_inner (p : ℕ) [Fact p.Prime]
    (hS : IsPGroup p S) (sat : F.Saturated p)
    (P : Subgroup S) (K : Subgroup (F.automorphismSubgroup P)) (hK : IsPGroup p K) :
    ∃ (R : Subgroup S) (e : P ≃* R) (he : F.IsHom e.toMonoidHom),
      K.map (F.alperinAutTransport e he).toMonoidHom ≤
        (F.innerSylowSubgroup R).subgroupOf (F.automorphismSubgroup R) := by
  obtain ⟨R, e₀, he₀, hR⟩ := F.exists_fullyNormalized P
  let τ := F.alperinAutTransport e₀ he₀
  let H := K.map τ.toMonoidHom
  have hpH : IsPGroup p H := hK.map τ.toMonoidHom
  obtain ⟨T, hHT⟩ := hpH.exists_le_sylow
  let HR := (F.innerSylowSubgroup R).subgroupOf (F.automorphismSubgroup R)
  have hpR : IsPGroup p HR := (F.conjugation_isPGroup p hS R).of_equiv
    (Subgroup.subgroupOfEquivOfLe (F.innerSylowSubgroup_le R)).symm
  let U := hpR.toSylow (sat.fully_normalized R hR).2
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq (F.automorphismSubgroup R) T U
  let e := e₀.trans a.val
  have he : F.IsHom e.toMonoidHom := F.comp_mem _ _ he₀ a.property
  refine ⟨R, e, he, ?_⟩
  rintro b ⟨c, hc, rfl⟩
  have hcT : τ c ∈ (T : Subgroup (F.automorphismSubgroup R)) := hHT ⟨c, hc, rfl⟩
  have hsmul := Subgroup.smul_mem_pointwise_smul (τ c) (MulAut.conj a)
    (T : Subgroup (F.automorphismSubgroup R)) hcT
  have hconj : a * τ c * a⁻¹ ∈ (U : Subgroup (F.automorphismSubgroup R)) := by
    rw [← ha, Sylow.coe_subgroup_smul]
    simpa only [MulAut.smul_def, MulAut.conj_apply] using hsmul
  change F.alperinAutTransport (e₀.trans a.val) he c ∈ HR
  rw [F.alperinAutTransport_trans]
  exact hconj

theorem centric_normal_aut_inner (p : ℕ) [Fact p.Prime]
    (hS : IsPGroup p S) (sat : F.Saturated p)
    {Q R : Subgroup S} (hQR : Q ≤ R) [(Q.subgroupOf R).Normal]
    (hQ : F.IsCentric Q) (a : MulAut R) (ha : F.IsHom a.toMonoidHom)
    (hfix : ∀ q : Q, (a ⟨q.val, hQR q.property⟩).val = q.val) :
    ∃ z : Q, ∀ x : R, (a x).val = z.val⁻¹ * x.val * z.val := by
  let N := Q.subgroupOf R
  let K := autPointwiseFixer (F.automorphismSubgroup R) N
  have hself : Subgroup.centralizer (N : Set R) ≤ N := by
    intro x hx
    have hxc : x.val ∈ Subgroup.centralizer (Q : Set S) := by
      apply Subgroup.mem_centralizer_iff.mpr
      intro q hq
      exact congrArg Subtype.val ((Subgroup.mem_centralizer_iff.mp hx)
        ⟨q, hQR hq⟩ hq)
    exact (hQ Q le_top (MulEquiv.refl Q) (F.id_mem Q)) ⟨hxc, Subgroup.mem_top _⟩
  have hpK : IsPGroup p K := autPointwiseFixer_isPGroup p (hS.to_subgroup R)
    (F.automorphismSubgroup R) N hself
  let aa : F.automorphismSubgroup R := ⟨a, ha⟩
  have haa : aa ∈ K := by
    intro q
    apply Subtype.ext
    exact hfix ⟨q.val.val, q.property⟩
  obtain ⟨T, e, he, hKT⟩ := F.pSubgroup_transport_to_inner p hS sat R K hpK
  have hta := hKT ⟨aa, haa, rfl⟩
  obtain ⟨t, ht⟩ := hta
  let f : (⟨Q⟩ : F.Object) ⟶ ⟨T⟩ :=
    F.inclusion hQR ≫ (F.isoOfMulEquiv e he).hom
  let Q' := F.imageSubgroup f
  let j : Q ≃* Q' := MonoidHom.ofInjective
    (Subtype.val_injective.comp (F.injective f.val f.property))
  have hj : F.IsHom j.toMonoidHom := (F.toImage f).property
  have htc : t.val ∈ Subgroup.centralizer (Q' : Set S) := by
    apply Subgroup.mem_centralizer_iff.mpr
    intro y hy
    obtain ⟨q, rfl⟩ := hy
    have h := congrArg (fun b : MulAut T => (b (e ⟨q.val, hQR q.property⟩)).val) ht
    change t.val * (e ⟨q.val, hQR q.property⟩).val * t.val⁻¹ =
      (e (a (e.symm (e ⟨q.val, hQR q.property⟩)))).val at h
    rw [e.symm_apply_apply] at h
    have hq : a ⟨q.val, hQR q.property⟩ = ⟨q.val, hQR q.property⟩ := Subtype.ext (hfix q)
    rw [hq] at h
    have hh := congrArg (fun v : S => v * t.val) h
    change (e ⟨q.val, hQR q.property⟩).val * t.val =
      t.val * (e ⟨q.val, hQR q.property⟩).val
    simpa [mul_assoc] using hh.symm
  have htQ' : t.val ∈ Q' := (hQ Q' le_top j hj) ⟨htc, Subgroup.mem_top _⟩
  have htT : t.val ∈ T := (F.image_le f) htQ'
  obtain ⟨z, hz⟩ := htQ'
  refine ⟨z⁻¹, ?_⟩
  intro x
  have h := congrArg (fun b : MulAut T => b (e x)) ht
  change T.normalizerMonoidHom t (e x) = e (a (e.symm (e x))) at h
  rw [e.symm_apply_apply] at h
  have hz' : e ⟨z.val, hQR z.property⟩ =
      ⟨t.val, htT⟩ := Subtype.ext hz
  have heval : e (⟨z.val, hQR z.property⟩ * x * (⟨z.val, hQR z.property⟩ : R)⁻¹) =
      e (a x) := by
    rw [map_mul, map_mul, map_inv, hz']
    exact h
  have hx := congrArg Subtype.val (e.injective heval)
  simpa only [Subgroup.coe_inv, Subgroup.coe_mul, inv_inv] using hx.symm

omit [Finite S] in
theorem centric_normal_image_le_of_agree
    {Q R T : Subgroup S} (hQR : Q ≤ R) [(Q.subgroupOf R).Normal]
    (hQ : F.IsCentric Q)
    (f g : (⟨R⟩ : F.Object) ⟶ ⟨T⟩)
    (hfg : ∀ q : Q, (f.val ⟨q.val, hQR q.property⟩).val =
      (g.val ⟨q.val, hQR q.property⟩).val) :
    F.imageSubgroup g ≤ F.imageSubgroup f := by
  let fQ : (⟨Q⟩ : F.Object) ⟶ ⟨T⟩ := F.inclusion hQR ≫ f
  let L := F.imageSubgroup fQ
  let j : Q ≃* L := MonoidHom.ofInjective
    (Subtype.val_injective.comp (F.injective fQ.val fQ.property))
  have hj : F.IsHom j.toMonoidHom := (F.toImage fQ).property
  rintro y ⟨x, rfl⟩
  have hdelta : (f.val x).val⁻¹ * (g.val x).val ∈ L := by
    apply (hQ L le_top j hj)
    refine ⟨?_, Subgroup.mem_top _⟩
    apply Subgroup.mem_centralizer_iff.mpr
    intro z hz
    obtain ⟨q, rfl⟩ := hz
    let qR : R := ⟨q.val, hQR q.property⟩
    have hqN : x * qR * x⁻¹ ∈ Q.subgroupOf R :=
      (inferInstance : (Q.subgroupOf R).Normal).conj_mem qR q.property x
    have h := hfg ⟨(x * qR * x⁻¹).val, hqN⟩
    change (f.val (x * qR * x⁻¹)).val = (g.val (x * qR * x⁻¹)).val at h
    simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv] at h
    have hq : (g.val qR).val = (f.val qR).val := (hfg q).symm
    rw [hq] at h
    have hh := congrArg (fun v : S => (f.val x).val⁻¹ * v * (g.val x).val) h
    change (f.val qR).val * ((f.val x).val⁻¹ * (g.val x).val) =
      ((f.val x).val⁻¹ * (g.val x).val) * (f.val qR).val
    simpa [mul_assoc] using hh
  obtain ⟨q, hq⟩ := hdelta
  refine ⟨x * ⟨q.val, hQR q.property⟩, ?_⟩
  change (f.val (x * ⟨q.val, hQR q.property⟩)).val = (g.val x).val
  rw [map_mul]
  change (f.val x).val * (f.val ⟨q.val, hQR q.property⟩).val = (g.val x).val
  change (f.val ⟨q.val, hQR q.property⟩).val =
    (f.val x).val⁻¹ * (g.val x).val at hq
  rw [hq, mul_inv_cancel_left]

theorem centric_normal_orbit_eq_of_agree (p : ℕ) [Fact p.Prime]
    (hS : IsPGroup p S) (sat : F.Saturated p)
    {Q R T : Subgroup S} (hQR : Q ≤ R) [(Q.subgroupOf R).Normal]
    (hQ : F.IsCentric Q)
    (f g : (⟨R⟩ : F.Object) ⟶ ⟨T⟩)
    (hfg : ∀ q : Q, (f.val ⟨q.val, hQR q.property⟩).val =
      (g.val ⟨q.val, hQR q.property⟩).val) :
    F.toOrbit.map f = F.toOrbit.map g := by
  have hgf := F.centric_normal_image_le_of_agree hQR hQ f g hfg
  have hfg' := F.centric_normal_image_le_of_agree hQR hQ g f (fun q => (hfg q).symm)
  have himage : F.imageSubgroup g = F.imageSubgroup f := le_antisymm hgf hfg'
  let L := F.imageSubgroup f
  let eF : R ≃* L := MonoidHom.ofInjective
    (Subtype.val_injective.comp (F.injective f.val f.property))
  have heF : F.IsHom eF.toMonoidHom := (F.toImage f).property
  let g' : R →* L :=
    { toFun x := ⟨(g.val x).val, hgf ⟨x, rfl⟩⟩
      map_one' := by
        apply Subtype.ext
        exact congrArg (fun t : T => t.val) (map_one g.val)
      map_mul' x y := by
        apply Subtype.ext
        exact congrArg (fun t : T => t.val) (map_mul g.val x y) }
  have hg' : F.IsHom g' :=
    F.codomain_restrict_mem g.val g.property (F.image_le f) g' (by ext x; rfl)
  have hsurj : Function.Surjective g' := by
    intro y
    have hy : y.val ∈ F.imageSubgroup g := himage.symm ▸ y.property
    obtain ⟨x, hx⟩ := hy
    exact ⟨x, Subtype.ext hx⟩
  let eG := MulEquiv.ofBijective g' ⟨F.injective g' hg', hsurj⟩
  let a := eG.trans eF.symm
  have ha : F.IsHom a.toMonoidHom := F.comp_mem _ _ hg' (F.inverse_mem eF heF)
  have hfix : ∀ q : Q, (a ⟨q.val, hQR q.property⟩).val = q.val := by
    intro q
    have hEq : a ⟨q.val, hQR q.property⟩ = ⟨q.val, hQR q.property⟩ := by
      apply eF.injective
      change eF (eF.symm (eG ⟨q.val, hQR q.property⟩)) = _
      rw [eF.apply_symm_apply]
      apply Subtype.ext
      exact (hfg q).symm
    exact congrArg Subtype.val hEq
  obtain ⟨z, hz⟩ := F.centric_normal_aut_inner p hS sat hQR hQ a ha hfix
  apply (F.orbit_map_eq_iff f g).mpr
  refine ⟨f.val ⟨z.val, hQR z.property⟩, ?_⟩
  intro x
  have hax : a x = (⟨z.val, hQR z.property⟩ : R)⁻¹ * x *
      ⟨z.val, hQR z.property⟩ := Subtype.ext (hz x)
  have heq : f.val (a x) = g.val x := by
    apply Subtype.ext
    exact congrArg (fun y : L => y.val) (eF.apply_symm_apply (eG x))
  rw [← heq, hax, map_mul, map_mul, map_inv]

theorem centric_normal_orbit_restriction_injective (p : ℕ) [Fact p.Prime]
    (hS : IsPGroup p S) (sat : F.Saturated p)
    {Q R T : Subgroup S} (hQR : Q ≤ R) [(Q.subgroupOf R).Normal]
    (hQ : F.IsCentric Q)
    (f g : (⟨R⟩ : F.Object) ⟶ ⟨T⟩)
    (hfg : F.toOrbit.map (F.inclusion hQR ≫ f) =
      F.toOrbit.map (F.inclusion hQR ≫ g)) :
    F.toOrbit.map f = F.toOrbit.map g := by
  obtain ⟨t, ht⟩ := (F.orbit_map_eq_iff _ _).mp hfg
  let f' := f ≫ F.inner ⟨T⟩ t
  have heq : F.toOrbit.map f' = F.toOrbit.map g := by
    apply F.centric_normal_orbit_eq_of_agree p hS sat hQR hQ f' g
    intro q
    exact congrArg Subtype.val (ht q).symm
  simpa only [f', F.toOrbit.map_comp, F.inner_orbit_eq_id, Category.comp_id] using heq

end FusionSystem
end Sharpness
