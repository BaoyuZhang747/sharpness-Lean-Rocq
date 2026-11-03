import Mathlib.LinearAlgebra.Isomorphisms

/-! The canonical quotient of im(v) by im(vu), with an explicit
surjective map from the middle module. Its kernel is tested directly
on representatives, and the resulting descent criterion is proved. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
variable {R A B H E Q : Type u} [CommRing R]
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup H] [Module R H] [AddCommGroup E] [Module R E]
    [AddCommGroup Q] [Module R Q]
    (u : B →ₗ[R] A) (v : A →ₗ[R] H)

abbrev ImageQuotient := v.range ⧸ (v.comp u).range.comap v.range.subtype

def imageQuotientProjection : A →ₗ[R] ImageQuotient u v :=
  ((v.comp u).range.comap v.range.subtype).mkQ.comp v.rangeRestrict

theorem imageQuotientProjection_eq_zero (a : A) :
    imageQuotientProjection u v a = 0 ↔ ∃ b : B, v (u b) = v a := by
  change (Submodule.Quotient.mk (⟨v a, ⟨a, rfl⟩⟩ : v.range) : ImageQuotient u v) = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero]
  rfl

theorem imageQuotientProjection_surjective : Function.Surjective (imageQuotientProjection u v) := by
  intro z
  obtain ⟨y, rfl⟩ := ((v.comp u).range.comap v.range.subtype).mkQ_surjective z
  obtain ⟨a, ha⟩ := y.property
  refine ⟨a, ?_⟩
  exact congrArg (fun y : v.range => Submodule.Quotient.mk y)
    (show (⟨v a, ⟨a, rfl⟩⟩ : v.range) = y from Subtype.ext ha)

theorem imageQuotientProjection_comp : (imageQuotientProjection u v).comp u = 0 := by
  apply LinearMap.ext
  intro b
  exact (imageQuotientProjection_eq_zero u v (u b)).mpr ⟨b, rfl⟩

theorem imageQuotientProjection_of_mem_ker {a : A} (h : v a = 0) :
    imageQuotientProjection u v a = 0 :=
  (imageQuotientProjection_eq_zero u v a).mpr ⟨0, by simp [h]⟩

theorem imageQuotientProjection_ker_le {D : Type u} [AddCommGroup D] [Module R D]
    (d : D →ₗ[R] A) (g : A →ₗ[R] E)
    (hu : g.comp u = 0) (hd : g.comp d = 0) (exact : d.range = v.ker) :
    (imageQuotientProjection u v).ker ≤ g.ker := by
  intro a ha
  obtain ⟨b, hb⟩ := (imageQuotientProjection_eq_zero u v a).mp ha
  have hk : a-u b ∈ v.ker := by
    change v (a-u b) = 0
    rw [map_sub, hb, sub_self]
  obtain ⟨c, hc⟩ := (show a-u b ∈ d.range from exact.symm ▸ hk)
  have hgb : g (u b) = 0 := congrArg (fun f : B →ₗ[R] E => f b) hu
  have hgc : g (a-u b) = 0 := by
    rw [← hc]
    exact congrArg (fun f : D →ₗ[R] E => f c) hd
  change g a = 0
  have hs : u b + (a-u b) = a := by rw [add_comm, sub_add_cancel]
  rw [← hs, map_add, hgb, hgc, add_zero]

theorem surjective_linear_descent_bijective (g : A →ₗ[R] E) (q : A →ₗ[R] Q)
    (d : E →ₗ[R] Q) (hg : Function.Surjective g) (hq : Function.Surjective q)
    (fac : d.comp g = q) (hker : q.ker ≤ g.ker) : Function.Bijective d := by
  constructor
  · intro x y hxy
    obtain ⟨a, rfl⟩ := hg x
    obtain ⟨b, rfl⟩ := hg y
    have hk : a-b ∈ q.ker := by
      change q (a-b) = 0
      rw [← fac]
      change d (g (a-b)) = 0
      rw [map_sub, map_sub, hxy, sub_self]
    have he : g (a-b) = 0 := hker hk
    exact sub_eq_zero.mp ((g.map_sub a b).symm.trans he)
  · intro z
    obtain ⟨a, rfl⟩ := hq z
    exact ⟨g a, congrArg (fun f : A →ₗ[R] Q => f a) fac⟩

end Sharpness
