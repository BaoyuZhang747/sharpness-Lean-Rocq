import Sharpness.Unconditional.ElementaryCochainEdgeLeading

/-! One elementary correction removes the leading column of a total cocycle,
using exactness only after vertical cohomology. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
universe u
namespace Sharpness.ElementaryCochainEdge
open CategoryTheory CategoryTheory.Limits HomologicalComplex
variable {R : Type u} [CommRing R]
    (K : HomologicalComplex₂ (ModuleCat.{u} R) (ComplexShape.up ℕ) (ComplexShape.up ℕ))

theorem leading_correction (hK : PositiveHorizontalExact K) (p q n : ℕ) (hpq : p+q=n)
    (x : (K.total (ComplexShape.up ℕ)).X (n+1))
    (hx : Cycle (K.total (ComplexShape.up ℕ)) (n+1) x) (hs : SupportedFrom K x (p+1)) :
    ∃ y : (K.total (ComplexShape.up ℕ)).X n,
      SupportedFrom K y p ∧
      SupportedFrom K ((K.total (ComplexShape.up ℕ)).d n (n+1) y) (p+1) ∧
      totalSummandProjectionAt K (p+1) q (n+1) (by omega)
        ((K.total (ComplexShape.up ℕ)).d n (n+1) y) =
      totalSummandProjectionAt K (p+1) q (n+1) (by omega) x := by
  obtain ⟨a, ha, b, hb⟩ := horizontal_cycle_lift K hK p q
    (totalSummandProjectionAt K (p+1) q (n+1) (by omega) x)
    (leading_cycle K (p+1) q (n+1) (by omega) x hx hs)
    (leading_horizontal_cycle K (p+1) q (n+1) (by omega) x hx hs)
  cases q with
  | zero =>
    simp only [Nat.add_zero] at hpq
    subst n
    have hb' : totalSummandProjectionAt K (p+1) 0 (p+1) (by omega) x =
        (K.d p (p+1)).f 0 a := by
      have hb0 : (0 : (K.X (p+1)).X 0) =
          totalSummandProjectionAt K (p+1) 0 (p+1) (by omega) x - (K.d p (p+1)).f 0 a := by
        rw [(K.X (p+1)).shape 0 0 (by decide)] at hb
        exact hb
      exact sub_eq_zero.mp hb0.symm
    refine ⟨K.ιTotal (ComplexShape.up ℕ) p 0 p (by simp) a,
      inclusion_supportedFrom K p 0 p (by simp) a,
      inclusion_differential_cycle_supportedFrom K p 0 p (by simp) a (ha 1), ?_⟩
    rw [inclusion_differential_of_cycle K p 0 p (by simp) a (ha 1), inclusion_projection, hb']
  | succ q =>
    change (K.X (p+1)).d q (q+1) b =
      totalSummandProjectionAt K (p+1) (q+1) (n+1) (by omega) x -
        (K.d p (p+1)).f (q+1) a at hb
    let y₁ := K.ιTotal (ComplexShape.up ℕ) p (q+1) n hpq a
    let y₂ := ((-1 : ℤˣ)^(p+1))⁻¹ •
      K.ιTotal (ComplexShape.up ℕ) (p+1) q n (by change p+1+q=n; omega) b
    have hy₁ : SupportedFrom K y₁ p := inclusion_supportedFrom K p (q+1) n hpq a
    have hy₂ : SupportedFrom K y₂ (p+1) :=
      supportedFrom_smul K _ (inclusion_supportedFrom K (p+1) q n (by omega) b)
    have hd₁ : SupportedFrom K ((K.total (ComplexShape.up ℕ)).d n (n+1) y₁) (p+1) :=
      inclusion_differential_cycle_supportedFrom K p (q+1) n hpq a (ha (q+2))
    have hd₂ : SupportedFrom K ((K.total (ComplexShape.up ℕ)).d n (n+1) y₂) (p+1) := by
      dsimp only [y₂]
      rw [moduleHom_units_smul]
      exact supportedFrom_smul K _ (inclusion_differential_supportedFrom K (p+1) q n (by omega) b)
    refine ⟨y₁+y₂, supportedFrom_add K hy₁ (supportedFrom_mono K hy₂ (by omega)), ?_, ?_⟩
    · rw [map_add]
      exact supportedFrom_add K hd₁ hd₂
    · rw [map_add, map_add]
      have ht₁ : totalSummandProjectionAt K (p+1) (q+1) (n+1) (by omega)
          ((K.total (ComplexShape.up ℕ)).d n (n+1) y₁) = (K.d p (p+1)).f (q+1) a := by
        dsimp only [y₁]
        rw [inclusion_differential_of_cycle K p (q+1) n hpq a (ha (q+2)), inclusion_projection]
      have ht₂ : totalSummandProjectionAt K (p+1) (q+1) (n+1) (by omega)
          ((K.total (ComplexShape.up ℕ)).d n (n+1) y₂) = (K.X (p+1)).d q (q+1) b := by
        dsimp only [y₂]
        rw [moduleHom_units_smul, moduleHom_units_smul, inclusion_differential,
          map_add, moduleHom_units_smul,
          inclusion_projection_other K (p+1+1) q (n+1) (by omega) _
            (p+1) (q+1) (by omega) (by omega), inclusion_projection,
          zero_add, inv_smul_smul]
      rw [ht₁, ht₂, hb]
      abel

end Sharpness.ElementaryCochainEdge
