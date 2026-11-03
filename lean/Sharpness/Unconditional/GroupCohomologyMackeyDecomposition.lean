import Mathlib.RepresentationTheory.Coinduced
import Mathlib.GroupTheory.DoubleCoset
import Mathlib.Tactic.Group

/-! The concrete double-coset coordinates of coinduction with trivial
coefficients. The coinducing subgroup is H, the restricting subgroup is K,
and representatives index H\G/K. Thus the component at x sends f to
(k ↦ f (x*k)), and its subgroup is K ∩ x⁻¹Hx, viewed as a subgroup of K.
All actions are Mathlib's right-translation coinduction actions. -/

set_option autoImplicit false
noncomputable section
universe u v w

namespace Sharpness.OrdinaryCohomology.MackeyDecomposition
open CategoryTheory

variable {R : Type u} {G : Type v} {A : Type w} [CommRing R] [Group G]
    [AddCommGroup A] [Module R A] (H K : Subgroup G)

/-- The actual intersection K ∩ x⁻¹Hx, expressed inside K. -/
def intersection (x : G) : Subgroup K :=
  H.comap ((MulAut.conj x).toMonoidHom.comp K.subtype)

@[simp] theorem mem_intersection (x : G) (k : K) :
    k ∈ intersection H K x ↔ x * (k : G) * x⁻¹ ∈ H := Iff.rfl

abbrev Source := Representation.coindV H.subtype (Representation.trivial R H A)

abbrev Component (x : G) := Representation.coindV (intersection H K x).subtype
  (Representation.trivial R (intersection H K x) A)

abbrev Components := ∀ d : DoubleCoset.Quotient (H : Set G) K,
  Component (R := R) (A := A) H K d.out

/-- Restrict an equivariant function to the coset represented by x. -/
def component (x : G) : Source (R := R) (A := A) H →ₗ[R]
    Component (R := R) (A := A) H K x where
  toFun f := ⟨fun k => f.1 (x * k), by
    intro l k
    have hl : x * (l.1 : G) * x⁻¹ ∈ H := l.2
    have hf := f.2 ⟨x * (l.1 : G) * x⁻¹, hl⟩ (x * k)
    simpa [Representation.trivial, mul_assoc] using hf⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem component_apply (x : G) (f : Source (R := R) (A := A) H) (k : K) :
    (component H K x f).1 k = f.1 (x * k) := rfl

/-- Simultaneous restriction to the actual double-coset representatives. -/
def decompose : Source (R := R) (A := A) H →ₗ[R] Components (R := R) (A := A) H K :=
  LinearMap.pi fun d => component H K d.out

@[simp] theorem decompose_apply (f : Source (R := R) (A := A) H)
    (d : DoubleCoset.Quotient (H : Set G) K) (k : K) :
    (decompose H K f d).1 k = f.1 (d.out * k) := rfl

/-- Every group element lies in its represented double coset. -/
theorem exists_coordinates (g : G) :
    ∃ h : H, ∃ k : K, g = (h : G) * (DoubleCoset.mk H K g).out * k := by
  obtain ⟨h, hh, k, hk, hg⟩ := (DoubleCoset.eq H K (DoubleCoset.mk H K g).out g).mp
    (DoubleCoset.out_eq' H K (DoubleCoset.mk H K g))
  exact ⟨⟨h, hh⟩, ⟨k, hk⟩, hg⟩

/-- The component restrictions retain every value of the original function. -/
theorem decompose_injective : Function.Injective (decompose (R := R) (A := A) H K) := by
  intro f f' same
  apply Subtype.ext
  funext g
  obtain ⟨h, k, hg⟩ := exists_coordinates H K g
  let d := DoubleCoset.mk H K g
  have hf : f.1 g = f.1 (d.out * k) := by
    rw [hg]
    simpa [Representation.trivial, mul_assoc] using f.2 h (d.out * k)
  have hf' : f'.1 g = f'.1 (d.out * k) := by
    rw [hg]
    simpa [Representation.trivial, mul_assoc] using f'.2 h (d.out * k)
  exact hf.trans ((congrArg (fun z => (z d).1 k) same).trans hf'.symm)

/-- Two coordinates in the same represented coset differ by the actual
intersection subgroup, not an assumed stabilizer. -/
theorem coordinates_related (x : G) (h h' : H) (k k' : K)
    (same : (h : G) * x * k = (h' : G) * x * k') :
    k * k'⁻¹ ∈ intersection H K x := by
  change x * ((k : G) * (k' : G)⁻¹) * x⁻¹ ∈ H
  have heq : x * ((k : G) * (k' : G)⁻¹) * x⁻¹ = (h : G)⁻¹ * h' := by
    calc
      x * ((k : G) * (k' : G)⁻¹) * x⁻¹ =
          (h : G)⁻¹ * ((h : G) * x * k) * (k' : G)⁻¹ * x⁻¹ := by group
      _ = (h : G)⁻¹ * ((h' : G) * x * k') * (k' : G)⁻¹ * x⁻¹ := by rw [same]
      _ = (h : G)⁻¹ * h' := by group
  rw [heq]
  exact H.mul_mem (H.inv_mem h.2) h'.2

/-- A component function has the same value on any two such coordinates. -/
theorem component_coordinates_eq (x : G) (f : Component (R := R) (A := A) H K x)
    (h h' : H) (k k' : K)
    (same : (h : G) * x * k = (h' : G) * x * k') : f.1 k = f.1 k' := by
  have hf := f.2 ⟨k * k'⁻¹, coordinates_related H K x h h' k k' same⟩ k'
  simpa [Representation.trivial] using hf

end Sharpness.OrdinaryCohomology.MackeyDecomposition
