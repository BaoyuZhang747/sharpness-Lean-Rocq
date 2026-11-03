import Sharpness.BarExactness

/-! The two short exact sequences in cor:local are used at the level
of actual bar cocycles. Lifting cycles modulo boundaries proves the
surjectivity that the long exact sequences express. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FiniteBarModel
open CategoryTheory
variable {R C : Type u} [CommRing R] [Category.{u} C]
    (B : FiniteBarModel R C)

/-- If the kernel coefficients are acyclic, every positive cocycle in
the quotient has a closed lift. This is the surjectivity part of the
cohomology long exact sequence, proved by a concrete correction. -/
theorem closed_lift_of_kernel_exact
    {K D E : CoefficientCategory R C} (f : K ⟶ D) (g : D ⟶ E)
    (hf : ∀ P, Function.Injective (f.app P))
    (hg : ∀ P, Function.Surjective (g.app P))
    (hex : ∀ P, Function.Exact (f.app P) (g.app P))
    (hK : B.ExactPositive K) (n : ℕ)
    (z : B.Cochains E (n+1)) (hz : B.d E (n+1) z = 0) :
    ∃ y : B.Cochains D (n+1), B.d D (n+1) y = 0 ∧ B.map g (n+1) y = z := by
  obtain ⟨v, hv⟩ := B.map_surjective g hg (n+1) z
  have hgv : B.map g (n+2) (B.d D (n+1) v) = 0 := by
    rw [B.map_d, hv, hz]
  obtain ⟨t, ht⟩ := (B.map_exact f g hex (n+2) _).mp hgv
  have closed : B.d K (n+2) t = 0 := by
    apply B.map_injective f hf (n+3)
    rw [map_zero, B.map_d, ht]
    exact LinearMap.congr_fun (B.dd D (n+1)) v
  obtain ⟨b, hb⟩ := hK (n+1) t closed
  refine ⟨v - B.map f (n+1) b, ?_, ?_⟩
  · rw [map_sub, ← B.map_d, hb, ht, sub_self]
  · rw [map_sub, hv]
    have zero : B.map g (n+1) (B.map f (n+1) b) = 0 :=
      (B.map_exact f g hex (n+1)).apply_apply_eq_zero b
    rw [zero, sub_zero]

/-- Acyclic quotient coefficients make every positive cocycle homologous
to one in the subobject. This is the other surjectivity used in Step 1. -/
theorem representative_in_subobject_of_quotient_exact
    {D E Q : CoefficientCategory R C} (f : D ⟶ E) (g : E ⟶ Q)
    (hf : ∀ P, Function.Injective (f.app P))
    (hg : ∀ P, Function.Surjective (g.app P))
    (hex : ∀ P, Function.Exact (f.app P) (g.app P))
    (hQ : B.ExactPositive Q) (n : ℕ)
    (z : B.Cochains E (n+1)) (hz : B.d E (n+1) z = 0) :
    ∃ y : B.Cochains D (n+1), B.d D (n+1) y = 0 ∧
      ∃ b : B.Cochains E n, B.map f (n+1) y = z - B.d E n b := by
  have closed : B.d Q (n+1) (B.map g (n+1) z) = 0 := by
    rw [← B.map_d, hz, map_zero]
  obtain ⟨c, hc⟩ := hQ n _ closed
  obtain ⟨b, hb⟩ := B.map_surjective g hg n c
  have hzero : B.map g (n+1) (z - B.d E n b) = 0 := by
    rw [map_sub, B.map_d, hb, hc, sub_self]
  obtain ⟨y, hy⟩ := (B.map_exact f g hex (n+1) _).mp hzero
  refine ⟨y, ?_, b, hy⟩
  apply B.map_injective f hf (n+2)
  rw [map_zero, B.map_d, hy, map_sub, hz]
  have dd : B.d E (n+1) (B.d E n b) = 0 := LinearMap.congr_fun (B.dd E n) b
  rw [dd, sub_self]

/-- The manuscript's p-divisibility deduction, before finite generation.
No vanishing or surjectivity on cohomology is supplied as an input. -/
theorem scalar_surjective_on_cohomology
    {K D I Q : CoefficientCategory R C}
    (j : K ⟶ D) (a : D ⟶ I) (b : I ⟶ D) (q : D ⟶ Q)
    (hj : ∀ P, Function.Injective (j.app P))
    (ha : ∀ P, Function.Surjective (a.app P))
    (hja : ∀ P, Function.Exact (j.app P) (a.app P))
    (hb : ∀ P, Function.Injective (b.app P))
    (hq : ∀ P, Function.Surjective (q.app P))
    (hbq : ∀ P, Function.Exact (b.app P) (q.app P))
    (hK : B.ExactPositive K) (hQ : B.ExactPositive Q)
    (r : R) (factor : ∀ P x, b.app P (a.app P x) = r • x) (n : ℕ) :
    Function.Surjective (fun x : B.Cohomology D n => r • x) := by
  intro x
  refine Quotient.inductionOn' x fun z => ?_
  obtain ⟨y, hy, c, hc⟩ :=
    B.representative_in_subobject_of_quotient_exact b q hb hq hbq hQ n z.val z.property
  obtain ⟨v, hv, hvy⟩ := B.closed_lift_of_kernel_exact j a hj ha hja hK n y hy
  refine ⟨(LinearMap.range (B.boundary D n)).mkQ ⟨v, hv⟩, ?_⟩
  change (LinearMap.range (B.boundary D n)).mkQ (r • (⟨v, hv⟩ : B.cycles D n)) =
    (LinearMap.range (B.boundary D n)).mkQ z
  apply (Submodule.Quotient.eq _).mpr
  refine ⟨-c, ?_⟩
  apply Subtype.ext
  change B.d D n (-c) = r • v - z.val
  have hfactor : r • v = z.val - B.d D n c := by
    calc
      r • v = B.map b (n+1) (B.map a (n+1) v) := by
        funext i
        exact (factor _ _).symm
      _ = B.map b (n+1) y := by rw [hvy]
      _ = z.val - B.d D n c := hc
  rw [hfactor, map_neg]
  abel

end Sharpness.FiniteBarModel
