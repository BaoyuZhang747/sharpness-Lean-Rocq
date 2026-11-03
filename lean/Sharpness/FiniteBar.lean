import Sharpness.HigherLimits

/-!
The finite-product bar description of AKO III.5.3 is packaged here as an
interface and constructed from a projective resolution in `Unconditional.BarCalculation`.
All uses of that description below are proved: zero cohomology is equivalent
to solving the cocycle equation, and maps act coordinatewise. In particular
this interface contains no Mackey, simple-functor, or sharpness assertion.
-/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory CategoryTheory.Limits Opposite

variable {R : Type u} [CommRing R] {C : Type u} [Category.{u} C]

abbrev finiteCochains (I : ℕ → Type u) (source : ∀ n, I n → Cᵒᵖ)
    (D : CoefficientCategory R C) (n : ℕ) := ∀ i : I n, D.obj (source n i)

instance (I : ℕ → Type u) (source : ∀ n, I n → Cᵒᵖ)
    (D : CoefficientCategory R C) (n : ℕ) :
    AddCommGroup (finiteCochains I source D n) := Pi.addCommGroup

instance (I : ℕ → Type u) (source : ∀ n, I n → Cᵒᵖ)
    (D : CoefficientCategory R C) (n : ℕ) :
    Module R (finiteCochains I source D n) := Pi.module _ _ _

def finiteCochainMap (I : ℕ → Type u) (source : ∀ n, I n → Cᵒᵖ)
    {D E : CoefficientCategory R C} (f : D ⟶ E) (n : ℕ) :
    finiteCochains I source D n →ₗ[R] finiteCochains I source E n where
  toFun x i := f.app (source n i) (x i)
  map_add' x y := by ext i; exact map_add _ _ _
  map_smul' a x := by ext i; exact map_smul _ _ _

/-- Bar cochains are finite products, their differential is natural, and
squares to zero. These are the general bar construction facts in AKO III.5.3.
No cohomology-vanishing conclusion is part of the data. -/
structure FiniteBarModel (R : Type u) [CommRing R] (C : Type u) [Category.{u} C] where
  Index : ℕ → Type u
  finiteIndex : ∀ n, Fintype (Index n)
  source : ∀ n, Index n → Cᵒᵖ
  d : ∀ (D : CoefficientCategory R C) (n : ℕ),
    finiteCochains Index source D n →ₗ[R] finiteCochains Index source D (n+1)
  dd : ∀ D n, (d D (n+1)).comp (d D n) = 0
  naturality : ∀ {D E : CoefficientCategory R C} (f : D ⟶ E) n,
    (d E n).comp (finiteCochainMap Index source f n) =
      (finiteCochainMap Index source f (n+1)).comp (d D n)

namespace FiniteBarModel
variable (B : FiniteBarModel R C)
attribute [instance] FiniteBarModel.finiteIndex

abbrev Cochains (D : CoefficientCategory R C) (n : ℕ) :=
  finiteCochains B.Index B.source D n

abbrev map {D E : CoefficientCategory R C} (f : D ⟶ E) (n : ℕ) :=
  finiteCochainMap B.Index B.source f n

theorem map_d {D E : CoefficientCategory R C} (f : D ⟶ E) (n : ℕ)
    (x : B.Cochains D n) : B.map f (n+1) (B.d D n x) = B.d E n (B.map f n x) :=
  (LinearMap.congr_fun (B.naturality f n) x).symm

def cycles (D : CoefficientCategory R C) (n : ℕ) : Submodule R (B.Cochains D (n+1)) :=
  LinearMap.ker (B.d D (n+1))

def boundary (D : CoefficientCategory R C) (n : ℕ) : B.Cochains D n →ₗ[R] B.cycles D n :=
  (B.d D n).codRestrict _ (fun x => LinearMap.congr_fun (B.dd D n) x)

abbrev Cohomology (D : CoefficientCategory R C) (n : ℕ) :=
  B.cycles D n ⧸ LinearMap.range (B.boundary D n)

instance (D : CoefficientCategory R C) (n : ℕ) : AddCommGroup (B.Cohomology D n) :=
  inferInstanceAs (AddCommGroup (B.cycles D n ⧸ LinearMap.range (B.boundary D n)))
instance (D : CoefficientCategory R C) (n : ℕ) : Module R (B.Cohomology D n) :=
  inferInstanceAs (Module R (B.cycles D n ⧸ LinearMap.range (B.boundary D n)))

def ExactPositive (D : CoefficientCategory R C) : Prop :=
  ∀ n, ∀ z : B.Cochains D (n+1), B.d D (n+1) z = 0 → ∃ b, B.d D n b = z

theorem exactPositive_iff (D : CoefficientCategory R C) :
    B.ExactPositive D ↔ ∀ n, Subsingleton (B.Cohomology D n) := by
  constructor
  · intro h n
    apply subsingleton_of_forall_eq 0
    intro x
    refine Quotient.inductionOn' x fun z => ?_
    obtain ⟨b, hb⟩ := h n z.val z.property
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    exact ⟨b, Subtype.ext hb⟩
  · intro h n z hz
    letI := h n
    have he : (LinearMap.range (B.boundary D n)).mkQ ⟨z, hz⟩ = 0 :=
      Subsingleton.elim _ _
    obtain ⟨b, hb⟩ := (Submodule.Quotient.mk_eq_zero _).mp he
    exact ⟨b, congrArg Subtype.val hb⟩

variable [EnoughProjectives (CoefficientCategory R C)]

/-- The actual identification with derived inverse limits. Only this
comparison is imported from AKO; the manuscript's reductions are proved. -/
structure Comparison where
  AKO_III_5_3 : ∀ D n, higherLimit D (n+1) ≅ ModuleCat.of R (B.Cohomology D n)

theorem acyclic_iff (cmp : B.Comparison) (D : CoefficientCategory R C) :
    Acyclic D ↔ B.ExactPositive D := by
  rw [B.exactPositive_iff]
  constructor
  · intro h n
    exact ModuleCat.isZero_iff_subsingleton.mp
      (IsZero.of_iso (h (n+1) (by omega)) (cmp.AKO_III_5_3 D n).symm)
  · intro h i hi
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hi)
    exact IsZero.of_iso (ModuleCat.isZero_iff_subsingleton.mpr (h n))
      (cmp.AKO_III_5_3 D n)

end FiniteBarModel
end Sharpness
