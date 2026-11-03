import Sharpness.Unconditional.ElementaryCochainEdgeComponents
import Sharpness.Unconditional.ElementaryCochainEdgeCycles

/-! Horizontal support and native total coboundaries on finite diagonals. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
universe u
namespace Sharpness.ElementaryCochainEdge
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
variable {R : Type u} [CommRing R]
    (K : HomologicalComplex₂ (ModuleCat.{u} R) (ComplexShape.up ℕ) (ComplexShape.up ℕ))

def SupportedFrom {n : ℕ} (x : (K.total (ComplexShape.up ℕ)).X n) (m : ℕ) : Prop :=
  ∀ p q (hpq : p+q=n), p < m → totalSummandProjectionAt K p q n hpq x = 0

theorem supportedFrom_zero (n m : ℕ) :
    SupportedFrom K (0 : (K.total (ComplexShape.up ℕ)).X n) m := by
  intro p q hpq hp
  exact map_zero _

theorem supportedFrom_mono {n p q : ℕ} {x : (K.total (ComplexShape.up ℕ)).X n}
    (h : SupportedFrom K x q) (hpq : p ≤ q) : SupportedFrom K x p := by
  intro i j hij hi
  exact h i j hij (lt_of_lt_of_le hi hpq)

theorem supportedFrom_add {n p : ℕ} {x y : (K.total (ComplexShape.up ℕ)).X n}
    (hx : SupportedFrom K x p) (hy : SupportedFrom K y p) : SupportedFrom K (x+y) p := by
  intro i j hij hi
  rw [map_add, hx i j hij hi, hy i j hij hi, add_zero]

theorem supportedFrom_sub {n p : ℕ} {x y : (K.total (ComplexShape.up ℕ)).X n}
    (hx : SupportedFrom K x p) (hy : SupportedFrom K y p) : SupportedFrom K (x-y) p := by
  intro i j hij hi
  rw [map_sub, hx i j hij hi, hy i j hij hi, sub_self]

theorem supportedFrom_eq_zero {n : ℕ} {x : (K.total (ComplexShape.up ℕ)).X n}
    (h : SupportedFrom K x (n+1)) : x=0 := by
  apply element_ext K
  intro p q hpq
  rw [h p q hpq (by omega), map_zero]

theorem inclusion_projection (p q n : ℕ) (hpq : p+q=n) (x : (K.X p).X q) :
    totalSummandProjectionAt K p q n hpq (K.ιTotal (ComplexShape.up ℕ) p q n hpq x) = x :=
  congrArg (fun f => f.hom x) (totalSummandProjectionAt_inclusion K p q n hpq)

theorem inclusion_projection_other (p q n : ℕ) (hpq : p+q=n) (x : (K.X p).X q)
    (i j : ℕ) (hij : i+j=n) (hpi : p≠i) :
    totalSummandProjectionAt K i j n hij (K.ιTotal (ComplexShape.up ℕ) p q n hpq x) = 0 :=
  congrArg (fun f => f.hom x) (totalSummandProjectionAt_other K i j n p q hij hpq hpi)

theorem inclusion_supportedFrom (p q n : ℕ) (hpq : p+q=n) (x : (K.X p).X q) :
    SupportedFrom K (K.ιTotal (ComplexShape.up ℕ) p q n hpq x) p := by
  intro i j hij hi
  exact inclusion_projection_other K p q n hpq x i j hij (by omega)

theorem moduleHom_units_smul {M N : ModuleCat.{u} R} (f : M ⟶ N) (s : ℤˣ) (x : M) :
    f (s • x) = s • f x := by simp only [Units.smul_def, map_zsmul]

theorem supportedFrom_smul {n p : ℕ} (s : ℤˣ) {x : (K.total (ComplexShape.up ℕ)).X n}
    (hx : SupportedFrom K x p) : SupportedFrom K (s • x) p := by
  intro i j hij hi
  rw [moduleHom_units_smul, hx i j hij hi, smul_zero]

theorem inclusion_differential (p q n : ℕ) (hpq : p+q=n) (x : (K.X p).X q) :
    (K.total (ComplexShape.up ℕ)).d n (n+1) (K.ιTotal (ComplexShape.up ℕ) p q n hpq x) =
      K.ιTotal (ComplexShape.up ℕ) (p+1) q (n+1) (by change p+1+q=n+1; omega)
        ((K.d p (p+1)).f q x) +
      (-1 : ℤˣ)^p • K.ιTotal (ComplexShape.up ℕ) p (q+1) (n+1)
        (by change p+(q+1)=n+1; omega) ((K.X p).d q (q+1) x) := by
  have hd : K.ιTotal (ComplexShape.up ℕ) p q n hpq ≫
      (K.total (ComplexShape.up ℕ)).d n (n+1) =
      (K.d p (p+1)).f q ≫ K.ιTotal (ComplexShape.up ℕ) (p+1) q (n+1)
        (by change p+1+q=n+1; omega) +
      (-1 : ℤˣ)^p • ((K.X p).d q (q+1) ≫
        K.ιTotal (ComplexShape.up ℕ) p (q+1) (n+1)
          (by change p+(q+1)=n+1; omega)) := by
    change _ ≫ (K.D₁ _ n (n+1) + K.D₂ _ n (n+1)) = _
    rw [comp_add, horizontal_outgoing, vertical_outgoing]
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_add,
    LinearMap.add_apply, Units.smul_def, ModuleCat.hom_zsmul, LinearMap.smul_apply]
      using congrArg (fun f => f.hom x) hd

theorem inclusion_differential_of_cycle (p q n : ℕ) (hpq : p+q=n) (x : (K.X p).X q)
    (hx : (K.X p).d q (q+1) x=0) :
    (K.total (ComplexShape.up ℕ)).d n (n+1) (K.ιTotal (ComplexShape.up ℕ) p q n hpq x) =
      K.ιTotal (ComplexShape.up ℕ) (p+1) q (n+1) (by change p+1+q=n+1; omega)
        ((K.d p (p+1)).f q x) := by
  rw [inclusion_differential, hx, map_zero, smul_zero, add_zero]

theorem inclusion_differential_supportedFrom (p q n : ℕ) (hpq : p+q=n)
    (x : (K.X p).X q) :
    SupportedFrom K ((K.total (ComplexShape.up ℕ)).d n (n+1)
      (K.ιTotal (ComplexShape.up ℕ) p q n hpq x)) p := by
  rw [inclusion_differential]
  apply supportedFrom_add K
  · exact supportedFrom_mono K (inclusion_supportedFrom K (p+1) q (n+1) (by omega) _) (by omega)
  · exact supportedFrom_smul K _ (inclusion_supportedFrom K p (q+1) (n+1) (by omega) _)

theorem inclusion_differential_cycle_supportedFrom (p q n : ℕ) (hpq : p+q=n)
    (x : (K.X p).X q) (hx : (K.X p).d q (q+1) x=0) :
    SupportedFrom K ((K.total (ComplexShape.up ℕ)).d n (n+1)
      (K.ιTotal (ComplexShape.up ℕ) p q n hpq x)) (p+1) := by
  rw [inclusion_differential_of_cycle K p q n hpq x hx]
  exact inclusion_supportedFrom K (p+1) q (n+1) (by omega) _

theorem supportedFrom_step {n p q : ℕ} (hpq : p+q=n)
    {x : (K.total (ComplexShape.up ℕ)).X n} (hx : SupportedFrom K x p)
    (hlead : totalSummandProjectionAt K p q n hpq x=0) : SupportedFrom K x (p+1) := by
  intro i j hij hi
  by_cases hip : i=p
  · subst i
    have hj : j=q := by omega
    subst j
    exact hlead
  · exact hx i j hij (by omega)

end Sharpness.ElementaryCochainEdge
