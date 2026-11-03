import Sharpness.Unconditional.ChainTotalIncomingProjections
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! Finite-diagonal elimination for acyclic columns of the native first-quadrant total complex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
universe u
namespace Sharpness.TotalComparison
open CategoryTheory CategoryTheory.Preadditive
open scoped BigOperators
variable {R : Type u} [CommRing R]

theorem chain_boundary_of_exactAt (L : ChainComplex (ModuleCat.{u} R) ℕ)
    (n : ℕ) (hL : L.ExactAt n) (x : L.X n)
    (hx : ∀ m, L.d n m x = 0) : ∃ y : L.X (n+1), L.d (n+1) n y = x := by
  have hp : (ComplexShape.down ℕ).prev n = n+1 :=
    (ComplexShape.down ℕ).prev_eq' (show (ComplexShape.down ℕ).Rel (n+1) n from rfl)
  have he := (L.exactAt_iff' (n+1) n ((ComplexShape.down ℕ).next n) hp rfl).mp hL
  exact (ShortComplex.moduleCat_exact_iff _).mp he x (hx _)

variable (K : HomologicalComplex₂ (ModuleCat.{u} R) (ComplexShape.down ℕ) (ComplexShape.down ℕ))

theorem total_element_decomposition {n : ℕ} (x : (K.total (ComplexShape.down ℕ)).X n) :
    (∑ i : Fin (n+1), K.ιTotal (ComplexShape.down ℕ) i.val (n-i.val) n
      (by change i.val+(n-i.val)=n; omega)
      (chainTotalProjection K i.val (n-i.val) n (by omega) x)) = x := by
  have h := congrArg (fun f : (K.total (ComplexShape.down ℕ)).X n ⟶
      (K.total (ComplexShape.down ℕ)).X n => f.hom x) (chainTotal_projection_sum K n)
  simpa only [ModuleCat.hom_sum, LinearMap.sum_apply, ModuleCat.hom_comp,
    LinearMap.comp_apply, ModuleCat.hom_id, LinearMap.id_apply] using h

theorem total_element_ext {n : ℕ} {x y : (K.total (ComplexShape.down ℕ)).X n}
    (h : ∀ p q (hpq : p+q=n), chainTotalProjection K p q n hpq x =
      chainTotalProjection K p q n hpq y) : x = y := by
  rw [← total_element_decomposition K x, ← total_element_decomposition K y]
  apply Finset.sum_congr rfl
  intro i _
  rw [h i.val (n-i.val)]

/-- A bound on the horizontal support of one total-chain element. -/
def TotalSupportBelow {n : ℕ} (x : (K.total (ComplexShape.down ℕ)).X n) (m : ℕ) : Prop :=
  ∀ p q (hpq : p+q=n), m ≤ p → chainTotalProjection K p q n hpq x = 0

theorem totalSupportBelow_degree {n : ℕ} (x : (K.total (ComplexShape.down ℕ)).X n) :
    TotalSupportBelow K x (n+1) := by
  intro p q hpq hmp
  omega

theorem totalSupportBelow_zero {n : ℕ} {x : (K.total (ComplexShape.down ℕ)).X n}
    (h : TotalSupportBelow K x 0) : x = 0 := by
  apply total_element_ext K
  intro p q hpq
  rw [h p q hpq (Nat.zero_le p), map_zero]

theorem total_differential_component (p q n : ℕ) (hpq : p+q=n)
    (x : (K.total (ComplexShape.down ℕ)).X (n+1)) :
    chainTotalProjection K p q n hpq ((K.total (ComplexShape.down ℕ)).d (n+1) n x) =
      (K.d (p+1) p).f q (chainTotalProjection K (p+1) q (n+1) (by omega) x) +
        (-1 : ℤˣ)^p • ((K.X p).d (q+1) q
          (chainTotalProjection K p (q+1) (n+1) (by omega) x)) := by
  have hd : (K.total (ComplexShape.down ℕ)).d (n+1) n ≫ chainTotalProjection K p q n hpq =
      chainTotalProjection K (p+1) q (n+1) (by omega) ≫ (K.d (p+1) p).f q +
        (-1 : ℤˣ)^p •
          (chainTotalProjection K p (q+1) (n+1) (by omega) ≫ (K.X p).d (q+1) q) := by
    change (K.D₁ _ (n+1) n + K.D₂ _ (n+1) n) ≫ _ = _
    rw [add_comp, chainTotal_horizontal_incoming, chainTotal_vertical_incoming]
  have hx := congrArg (fun f => f.hom x) hd
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_add,
    LinearMap.add_apply, Units.smul_def, ModuleCat.hom_zsmul, LinearMap.smul_apply] using hx

/-- In a total cycle, the highest supported component is a vertical cycle. -/
theorem total_top_component_cycle (p q : ℕ)
    (x : (K.total (ComplexShape.down ℕ)).X (p+(q+1)))
    (hs : TotalSupportBelow K x (p+1))
    (hc : (K.total (ComplexShape.down ℕ)).d (p+(q+1)) (p+q) x = 0) :
    (K.X p).d (q+1) q (chainTotalProjection K p (q+1) (p+(q+1)) rfl x) = 0 := by
  have h := total_differential_component K p q (p+q) rfl x
  have hc' : (K.total (ComplexShape.down ℕ)).d (p+q+1) (p+q) x = 0 := hc
  have hs' : chainTotalProjection K (p+1) q (p+q+1) (by omega) x = 0 :=
    hs (p+1) q (by omega) le_rfl
  rw [hc', map_zero, hs', map_zero, zero_add] at h
  have hz := congrArg (fun z => ((-1 : ℤˣ)^p)⁻¹ • z) h
  have hz' : (K.X p).d (q+1) q
      (chainTotalProjection K p (q+1) (p+q+1) (by omega) x) = 0 := by
    simpa only [smul_zero, inv_smul_smul] using hz.symm
  exact hz'

theorem moduleHom_units_smul {M N : ModuleCat.{u} R} (f : M ⟶ N) (s : ℤˣ) (x : M) :
    f (s • x) = s • f x := by simp only [Units.smul_def, map_zsmul]

/-- A signed lift of a single column element to the preceding total degree. -/
def totalBoundaryLift (p q n : ℕ) (hpq : p+q=n) (b : (K.X p).X (q+1)) :
    (K.total (ComplexShape.down ℕ)).X (n+1) :=
  ((-1 : ℤˣ)^p)⁻¹ •
    K.ιTotal (ComplexShape.down ℕ) p (q+1) (n+1) (by change p+(q+1)=n+1; omega) b

theorem totalBoundaryLift_projection (p q n : ℕ) (hpq : p+q=n)
    (b : (K.X p).X (q+1)) :
    chainTotalProjection K p (q+1) (n+1) (by omega) (totalBoundaryLift K p q n hpq b) =
      ((-1 : ℤˣ)^p)⁻¹ • b := by
  rw [totalBoundaryLift, moduleHom_units_smul]
  have h := congrArg (fun f => f.hom b)
    (chainTotalProjection_inclusion K p (q+1) (n+1) (by omega))
  exact congrArg (fun x => ((-1 : ℤˣ)^p)⁻¹ • x) h

theorem totalBoundaryLift_projection_other (p q n : ℕ) (hpq : p+q=n)
    (b : (K.X p).X (q+1)) (r s : ℕ) (hrs : r+s=n+1) (hpr : p ≠ r) :
    chainTotalProjection K r s (n+1) hrs (totalBoundaryLift K p q n hpq b) = 0 := by
  rw [totalBoundaryLift, moduleHom_units_smul]
  have h := congrArg (fun f => f.hom b)
    (chainTotalProjection_other K r s (n+1) p (q+1) hrs (by omega) hpr)
  change chainTotalProjection K r s (n+1) hrs
    (K.ιTotal (ComplexShape.down ℕ) p (q+1) (n+1) (by change p+(q+1)=n+1; omega) b) = 0 at h
  rw [h, smul_zero]

theorem totalBoundaryLift_boundary_top (p q n : ℕ) (hpq : p+q=n)
    (b : (K.X p).X (q+1)) :
    chainTotalProjection K p q n hpq
      ((K.total (ComplexShape.down ℕ)).d (n+1) n (totalBoundaryLift K p q n hpq b)) =
        (K.X p).d (q+1) q b := by
  rw [total_differential_component,
    totalBoundaryLift_projection_other K p q n hpq b (p+1) q (by omega) (by omega),
    map_zero, zero_add, totalBoundaryLift_projection, moduleHom_units_smul, smul_inv_smul]

theorem totalBoundaryLift_boundary_above (p q n : ℕ) (hpq : p+q=n)
    (b : (K.X p).X (q+1)) (r s : ℕ) (hrs : r+s=n) (hpr : p < r) :
    chainTotalProjection K r s n hrs
      ((K.total (ComplexShape.down ℕ)).d (n+1) n (totalBoundaryLift K p q n hpq b)) = 0 := by
  rw [total_differential_component,
    totalBoundaryLift_projection_other K p q n hpq b (r+1) s (by omega) (by omega),
    totalBoundaryLift_projection_other K p q n hpq b r (s+1) (by omega) (by omega),
    map_zero, map_zero, smul_zero, add_zero]

theorem total_leading_column_cycle (p q n : ℕ) (hpq : p+q=n)
    (x : (K.total (ComplexShape.down ℕ)).X n)
    (hs : TotalSupportBelow K x (p+1))
    (hc : ∀ j, (K.total (ComplexShape.down ℕ)).d n j x = 0) :
    ∀ j, (K.X p).d q j (chainTotalProjection K p q n hpq x) = 0 := by
  intro j
  by_cases h : (ComplexShape.down ℕ).Rel q j
  · obtain rfl : j+1=q := h
    obtain rfl : n=p+(j+1) := hpq.symm
    exact total_top_component_cycle K p j x hs (hc (p+j))
  · rw [(K.X p).shape q j h]
    rfl

/-- Descending support elimination expresses a total cycle as a boundary. -/
theorem total_cycle_boundary_of_support
    (hK : ∀ p, (K.X p).Acyclic) (n m : ℕ)
    (x : (K.total (ComplexShape.down ℕ)).X n)
    (hc : ∀ j, (K.total (ComplexShape.down ℕ)).d n j x = 0)
    (hs : TotalSupportBelow K x m) :
    ∃ y : (K.total (ComplexShape.down ℕ)).X (n+1),
      (K.total (ComplexShape.down ℕ)).d (n+1) n y = x := by
  induction m generalizing x with
  | zero =>
      refine ⟨0, ?_⟩
      rw [map_zero, totalSupportBelow_zero K hs]
  | succ p ih =>
      by_cases hp : p ≤ n
      · let q := n-p
        have hpq : p+q=n := by omega
        obtain ⟨b, hb⟩ := chain_boundary_of_exactAt (K.X p) q (hK p q)
          (chainTotalProjection K p q n hpq x) (total_leading_column_cycle K p q n hpq x hs hc)
        let y₀ := totalBoundaryLift K p q n hpq b
        let z := x - (K.total (ComplexShape.down ℕ)).d (n+1) n y₀
        have hzc : ∀ j, (K.total (ComplexShape.down ℕ)).d n j z = 0 := by
          intro j
          dsimp only [z]
          rw [map_sub, hc j]
          have hz := congrArg (fun f => f.hom y₀)
            ((K.total (ComplexShape.down ℕ)).d_comp_d (n+1) n j)
          change (K.total (ComplexShape.down ℕ)).d n j
            ((K.total (ComplexShape.down ℕ)).d (n+1) n y₀) = 0 at hz
          rw [hz, sub_zero]
        have hzs : TotalSupportBelow K z p := by
          intro r s hrs hpr
          change chainTotalProjection K r s n hrs
            (x - (K.total (ComplexShape.down ℕ)).d (n+1) n y₀) = 0
          rw [map_sub]
          by_cases he : r=p
          · subst r
            have heq : s=q := by omega
            subst s
            rw [totalBoundaryLift_boundary_top, hb, sub_self]
          · rw [hs r s hrs (by omega), totalBoundaryLift_boundary_above K p q n hpq b r s hrs
              (by omega), sub_zero]
        obtain ⟨y, hy⟩ := ih z hzc hzs
        refine ⟨y+y₀, ?_⟩
        rw [map_add, hy]
        exact sub_add_cancel x _
      · apply ih x hc
        intro r s hrs hpr
        omega

/-- A first-quadrant native total complex with acyclic columns is acyclic. -/
theorem total_acyclic_of_columns (hK : ∀ p, (K.X p).Acyclic) :
    (K.total (ComplexShape.down ℕ)).Acyclic := by
  intro n
  let T := K.total (ComplexShape.down ℕ)
  have hp : (ComplexShape.down ℕ).prev n = n+1 :=
    (ComplexShape.down ℕ).prev_eq' (show (ComplexShape.down ℕ).Rel (n+1) n from rfl)
  apply (T.exactAt_iff' (n+1) n ((ComplexShape.down ℕ).next n) hp rfl).mpr
  apply (ShortComplex.moduleCat_exact_iff _).mpr
  intro x hx
  apply total_cycle_boundary_of_support K hK n (n+1) x _ (totalSupportBelow_degree K x)
  intro j
  by_cases hj : (ComplexShape.down ℕ).Rel n j
  · have he := (ComplexShape.down ℕ).next_eq' hj
    rw [← he]
    exact hx
  · rw [T.shape n j hj]
    rfl

end Sharpness.TotalComparison
