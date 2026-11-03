import Mathlib.Algebra.Homology.HomotopyCofiber
import Mathlib.Algebra.Homology.ConcreteCategory
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.QuasiIso

/-! The native homotopy cofiber detects quasi-isomorphisms of nonnegative chain
complexes of modules. The proof identifies native homology classes with cycle
classes, then constructs the required cone boundaries explicitly. Degree zero
uses the native one-summand cone component and is included in both directions. -/

/-! The native homotopy cofiber criterion for nonnegative chain complexes of modules. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
universe u v

namespace Sharpness.ChainCofiber
open CategoryTheory CategoryTheory.Limits HomologicalComplex

variable {R : Type u} [Ring R]

def Cycle (K : ChainComplex (ModuleCat.{v} R) ℕ) (n : ℕ) (x : K.X n) : Prop :=
  ∀ j, K.d n j x = 0

def cycleClass (K : ChainComplex (ModuleCat.{v} R) ℕ) (n : ℕ)
    (x : K.X n) (hx : Cycle K n x) : K.homology n :=
  K.homologyπ n (K.cyclesMk x _ rfl (hx _))

theorem cycle_iCycles (K : ChainComplex (ModuleCat.{v} R) ℕ) (n : ℕ)
    (z : K.cycles n) : Cycle K n (K.iCycles n z) := by
  intro j
  exact congrArg (fun f => f.hom z) (K.iCycles_d n j)

theorem cycleClass_surjective (K : ChainComplex (ModuleCat.{v} R) ℕ) (n : ℕ)
    (z : K.homology n) : ∃ (x : K.X n) (hx : Cycle K n x), cycleClass K n x hx = z := by
  obtain ⟨y, rfl⟩ := (ModuleCat.epi_iff_surjective (K.homologyπ n)).mp inferInstance z
  refine ⟨K.iCycles n y, cycle_iCycles K n y, ?_⟩
  unfold cycleClass
  congr 1
  apply (ModuleCat.mono_iff_injective (K.iCycles n)).mp inferInstance
  exact K.i_cyclesMk _ _ rfl _

theorem cycleClass_eq_zero_iff (K : ChainComplex (ModuleCat.{v} R) ℕ) (n : ℕ)
    (x : K.X n) (hx : Cycle K n x) :
    cycleClass K n x hx = 0 ↔ ∃ y : K.X (n+1), K.d (n+1) n y = x := by
  have hp : (ComplexShape.down ℕ).prev n = n+1 :=
    (ComplexShape.down ℕ).prev_eq' (show (ComplexShape.down ℕ).Rel (n+1) n from rfl)
  have he : K.homologyι n (cycleClass K n x hx) = K.pOpcycles n x := by
    have h := congrArg (fun f => f.hom (K.cyclesMk x _ rfl (hx _))) (K.homology_π_ι n)
    change K.homologyι n (cycleClass K n x hx) =
      K.pOpcycles n (K.iCycles n (K.cyclesMk x _ rfl (hx _))) at h
    exact h.trans (congrArg (K.pOpcycles n) (K.i_cyclesMk x _ rfl (hx _)))
  have hz : cycleClass K n x hx = 0 ↔ K.pOpcycles n x = 0 := by
    rw [← he]
    exact ⟨fun h => by rw [h, map_zero], fun h =>
      (ModuleCat.mono_iff_injective (K.homologyι n)).mp inferInstance (h.trans (map_zero _).symm)⟩
  rw [hz]
  have h := (K.sc n).moduleCat_pOpcycles_eq_zero_iff x
  change K.pOpcycles n x = 0 ↔ ∃ y : K.X ((ComplexShape.down ℕ).prev n),
    K.d ((ComplexShape.down ℕ).prev n) n y = x at h
  rw [hp] at h
  exact h

theorem cycle_map {K L : ChainComplex (ModuleCat.{v} R) ℕ} (f : K ⟶ L)
    (n : ℕ) (x : K.X n) (hx : Cycle K n x) : Cycle L n (f.f n x) := by
  intro j
  have h := congrArg (fun g => g.hom x) (f.comm n j)
  change L.d n j (f.f n x) = f.f j (K.d n j x) at h
  rw [h, hx j, map_zero]

theorem cycleClass_map {K L : ChainComplex (ModuleCat.{v} R) ℕ} (f : K ⟶ L)
    (n : ℕ) (x : K.X n) (hx : Cycle K n x) :
    homologyMap f n (cycleClass K n x hx) =
      cycleClass L n (f.f n x) (cycle_map f n x hx) := by
  unfold cycleClass
  have h := congrArg (fun g => g.hom (K.cyclesMk x _ rfl (hx _)))
    (homologyπ_naturality f n)
  change homologyMap f n (K.homologyπ n (K.cyclesMk x _ rfl (hx _))) =
    L.homologyπ n (cyclesMap f n (K.cyclesMk x _ rfl (hx _))) at h
  rw [h]
  congr 1
  apply (ModuleCat.mono_iff_injective (L.iCycles n)).mp inferInstance
  have hm := congrArg (fun g => g.hom (K.cyclesMk x _ rfl (hx _))) (cyclesMap_i f n)
  change L.iCycles n (cyclesMap f n (K.cyclesMk x _ rfl (hx _))) =
    f.f n (K.iCycles n (K.cyclesMk x _ rfl (hx _))) at hm
  exact (hm.trans (congrArg (f.f n) (K.i_cyclesMk x _ rfl (hx _)))).trans
    (L.i_cyclesMk _ _ rfl _).symm

theorem cycleClass_eq_iff (K : ChainComplex (ModuleCat.{v} R) ℕ) (n : ℕ)
    (x y : K.X n) (hx : Cycle K n x) (hy : Cycle K n y) :
    cycleClass K n x hx = cycleClass K n y hy ↔
      ∃ z : K.X (n+1), K.d (n+1) n z = x-y := by
  have he (x : K.X n) (hx : Cycle K n x) :
      K.homologyι n (cycleClass K n x hx) = K.pOpcycles n x := by
    have h := congrArg (fun f => f.hom (K.cyclesMk x _ rfl (hx _))) (K.homology_π_ι n)
    change K.homologyι n (cycleClass K n x hx) =
      K.pOpcycles n (K.iCycles n (K.cyclesMk x _ rfl (hx _))) at h
    exact h.trans (congrArg (K.pOpcycles n) (K.i_cyclesMk x _ rfl (hx _)))
  have hi := (ModuleCat.mono_iff_injective (K.homologyι n)).mp inferInstance
  rw [← hi.eq_iff, he x hx, he y hy]
  have hp : (ComplexShape.down ℕ).prev n = n+1 :=
    (ComplexShape.down ℕ).prev_eq' (show (ComplexShape.down ℕ).Rel (n+1) n from rfl)
  have h := (K.sc n).moduleCat_pOpcycles_eq_iff x y
  change K.pOpcycles n x = K.pOpcycles n y ↔
    ∃ z : K.X ((ComplexShape.down ℕ).prev n),
      K.d ((ComplexShape.down ℕ).prev n) n z = x-y at h
  rw [hp] at h
  exact h

def CycleSurjective {K L : ChainComplex (ModuleCat.{v} R) ℕ} (f : K ⟶ L) (n : ℕ) : Prop :=
  ∀ (y : L.X n), Cycle L n y → ∃ (x : K.X n), Cycle K n x ∧
    ∃ z : L.X (n+1), f.f n x + L.d (n+1) n z = y

def CycleInjective {K L : ChainComplex (ModuleCat.{v} R) ℕ} (f : K ⟶ L) (n : ℕ) : Prop :=
  ∀ (x : K.X n), Cycle K n x → (∃ y : L.X (n+1), L.d (n+1) n y = f.f n x) →
    ∃ z : K.X (n+1), K.d (n+1) n z = x

theorem homologyMap_surjective_iff {K L : ChainComplex (ModuleCat.{v} R) ℕ}
    (f : K ⟶ L) (n : ℕ) : Function.Surjective (homologyMap f n) ↔ CycleSurjective f n := by
  constructor
  · intro h y hy
    obtain ⟨a, ha⟩ := h (cycleClass L n y hy)
    obtain ⟨x, hx, rfl⟩ := cycleClass_surjective K n a
    rw [cycleClass_map] at ha
    obtain ⟨z, hz⟩ := (cycleClass_eq_iff L n _ _ _ _).mp ha
    refine ⟨x, hx, -z, ?_⟩
    rw [map_neg, hz]
    abel
  · intro h y
    obtain ⟨z, hz, rfl⟩ := cycleClass_surjective L n y
    obtain ⟨x, hx, a, ha⟩ := h z hz
    refine ⟨cycleClass K n x hx, ?_⟩
    rw [cycleClass_map, cycleClass_eq_iff]
    refine ⟨-a, ?_⟩
    rw [map_neg]
    exact eq_sub_iff_add_eq.mpr (by rw [← ha]; abel)

theorem homologyMap_injective_iff {K L : ChainComplex (ModuleCat.{v} R) ℕ}
    (f : K ⟶ L) (n : ℕ) : Function.Injective (homologyMap f n) ↔ CycleInjective f n := by
  rw [injective_iff_map_eq_zero (homologyMap f n).hom]
  constructor
  · intro h x hx hb
    apply (cycleClass_eq_zero_iff K n x hx).mp
    apply h
    rw [cycleClass_map]
    exact (cycleClass_eq_zero_iff L n _ _).mpr hb
  · intro h y hy
    obtain ⟨x, hx, rfl⟩ := cycleClass_surjective K n y
    rw [cycleClass_map] at hy
    apply (cycleClass_eq_zero_iff K n x hx).mpr
    exact h x hx ((cycleClass_eq_zero_iff L n _ _).mp hy)

theorem quasiIso_iff_cycle_conditions {K L : ChainComplex (ModuleCat.{v} R) ℕ}
    (f : K ⟶ L) : QuasiIso f ↔ ∀ n, CycleInjective f n ∧ CycleSurjective f n := by
  rw [quasiIso_iff]
  simp only [quasiIsoAt_iff_isIso_homologyMap, ConcreteCategory.isIso_iff_bijective,
    Function.Bijective, homologyMap_injective_iff, homologyMap_surjective_iff]

theorem exactAt_iff_cycles_boundaries (K : ChainComplex (ModuleCat.{v} R) ℕ) (n : ℕ) :
    K.ExactAt n ↔ ∀ x : K.X n, Cycle K n x →
      ∃ y : K.X (n+1), K.d (n+1) n y = x := by
  have hp : (ComplexShape.down ℕ).prev n = n+1 :=
    (ComplexShape.down ℕ).prev_eq' (show (ComplexShape.down ℕ).Rel (n+1) n from rfl)
  rw [K.exactAt_iff' (n+1) n ((ComplexShape.down ℕ).next n) hp rfl,
    ShortComplex.moduleCat_exact_iff]
  constructor
  · intro h x hx
    exact h x (hx _)
  · intro h x hx
    apply h x
    intro j
    by_cases hj : (ComplexShape.down ℕ).Rel n j
    · rw [← (ComplexShape.down ℕ).next_eq' hj]
      exact hx
    · rw [K.shape n j hj]
      rfl

theorem cycle_zero (K : ChainComplex (ModuleCat.{v} R) ℕ) (x : K.X 0) :
    Cycle K 0 x := by
  intro j
  rw [K.shape 0 j (by change ¬j+1=0; omega)]
  rfl

theorem cycle_succ_iff (K : ChainComplex (ModuleCat.{v} R) ℕ) (n : ℕ)
    (x : K.X (n+1)) : Cycle K (n+1) x ↔ K.d (n+1) n x = 0 := by
  constructor
  · exact fun h => h n
  · intro h j
    by_cases hj : (ComplexShape.down ℕ).Rel (n+1) j
    · have he : j=n := by change j+1=n+1 at hj; omega
      subst j
      exact h
    · rw [K.shape _ _ hj]
      rfl

section Cone
variable {K L : ChainComplex (ModuleCat.{v} R) ℕ} (f : K ⟶ L)
open homotopyCofiber
open CategoryTheory.Preadditive

abbrev coneFst (n : ℕ) := fstX f (n+1) n (by rfl)
abbrev coneSnd (n : ℕ) := sndX f n
abbrev coneInl (n : ℕ) := inlX f n (n+1) (by rfl)
abbrev coneInr (n : ℕ) := inrX f n

@[simp] theorem cone_fst_inl (n : ℕ) (x : K.X n) :
    coneFst f n (coneInl f n x) = x := by
  exact congrArg (fun g => g.hom x) (inlX_fstX f n (n+1) rfl)

@[simp] theorem cone_snd_inl (n : ℕ) (x : K.X n) :
    coneSnd f (n+1) (coneInl f n x) = 0 := by
  exact congrArg (fun g => g.hom x) (inlX_sndX f n (n+1) rfl)

@[simp] theorem cone_fst_inr (n : ℕ) (y : L.X (n+1)) :
    coneFst f n (coneInr f (n+1) y) = 0 := by
  exact congrArg (fun g => g.hom y) (inrX_fstX f (n+1) n rfl)

@[simp] theorem cone_snd_inr (n : ℕ) (y : L.X n) :
    coneSnd f n (coneInr f n y) = y := by
  exact congrArg (fun g => g.hom y) (inrX_sndX f n)

theorem cone_decomposition (n : ℕ) (x : (homotopyCofiber f).X (n+1)) :
    coneInl f n (coneFst f n x) + coneInr f (n+1) (coneSnd f (n+1) x) = x := by
  have h : coneFst f n ≫ coneInl f n + coneSnd f (n+1) ≫ coneInr f (n+1) = 𝟙 _ := by
    apply ext_from_X f n (n+1) rfl <;> simp [coneFst, coneSnd, coneInl, coneInr]
  exact congrArg (fun g => g.hom x) h

theorem cone_zero_decomposition (x : (homotopyCofiber f).X 0) :
    coneInr f 0 (coneSnd f 0 x) = x := by
  exact congrArg (fun g => g.hom x) (sndX_inrX f 0 (by change ¬ _+1=0; omega))

theorem cone_element_ext (n : ℕ) {x y : (homotopyCofiber f).X (n+1)}
    (h₁ : coneFst f n x = coneFst f n y)
    (h₂ : coneSnd f (n+1) x = coneSnd f (n+1) y) : x=y := by
  rw [← cone_decomposition f n x, ← cone_decomposition f n y, h₁, h₂]

theorem cone_zero_ext {x y : (homotopyCofiber f).X 0}
    (h : coneSnd f 0 x = coneSnd f 0 y) : x=y := by
  rw [← cone_zero_decomposition f x, ← cone_zero_decomposition f y, h]

theorem cone_d_fst (n : ℕ) (x : (homotopyCofiber f).X (n+1+1)) :
    coneFst f n ((homotopyCofiber f).d (n+1+1) (n+1) x) =
      -(K.d (n+1) n (coneFst f (n+1) x)) := by
  change (fstX f (n+1) n rfl).hom ((homotopyCofiber.d f (n+1+1) (n+1)).hom x) =
    -((K.d (n+1) n).hom ((fstX f (n+1+1) (n+1) rfl).hom x))
  have h₀ := d_fstX f (n+1+1) (n+1) n rfl rfl
  have h := congrArg (fun g => g.hom x) h₀
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_neg,
    LinearMap.neg_apply] using h

theorem cone_d_snd (n : ℕ) (x : (homotopyCofiber f).X (n+1)) :
    coneSnd f n ((homotopyCofiber f).d (n+1) n x) =
      f.f n (coneFst f n x) + L.d (n+1) n (coneSnd f (n+1) x) := by
  exact congrArg (fun g => g.hom x) (d_sndX f (n+1) n rfl)

theorem cone_inr_cycle (n : ℕ) (y : L.X n) (hy : Cycle L n y) :
    Cycle (homotopyCofiber f) n (coneInr f n y) := by
  exact cycle_map (homotopyCofiber.inr f) n y hy

theorem cone_fst_cycle (n : ℕ) (x : (homotopyCofiber f).X (n+1))
    (hx : Cycle (homotopyCofiber f) (n+1) x) : Cycle K n (coneFst f n x) := by
  cases n with
  | zero => exact cycle_zero _ _
  | succ n =>
    apply (cycle_succ_iff K n _).mpr
    have h := cone_d_fst f n x
    rw [hx (n+1), map_zero] at h
    exact neg_eq_zero.mp h.symm

theorem cone_cycle_iff (n : ℕ) (x : (homotopyCofiber f).X (n+1)) :
    Cycle (homotopyCofiber f) (n+1) x ↔
      Cycle K n (coneFst f n x) ∧
        f.f n (coneFst f n x) + L.d (n+1) n (coneSnd f (n+1) x) = 0 := by
  constructor
  · intro hx
    refine ⟨cone_fst_cycle f n x hx, ?_⟩
    rw [← cone_d_snd, hx n, map_zero]
  · rintro ⟨hx, hy⟩
    apply (cycle_succ_iff (homotopyCofiber f) n x).mpr
    cases n with
    | zero =>
      apply cone_zero_ext f
      rw [cone_d_snd, map_zero]
      exact hy
    | succ n =>
      apply cone_element_ext f n
      · rw [cone_d_fst, map_zero, hx n, neg_zero]
      · rw [cone_d_snd, map_zero]
        exact hy

theorem cycle_surjective_of_cofiber_acyclic (h : (homotopyCofiber f).Acyclic)
    (n : ℕ) : CycleSurjective f n := by
  intro y hy
  obtain ⟨w, hw⟩ := (exactAt_iff_cycles_boundaries _ n).mp (h n)
    (coneInr f n y) (cone_inr_cycle f n y hy)
  refine ⟨coneFst f n w, ?_, coneSnd f (n+1) w, ?_⟩
  · cases n with
    | zero => exact cycle_zero _ _
    | succ n =>
      apply (cycle_succ_iff K n _).mpr
      have hh := cone_d_fst f n w
      rw [hw, cone_fst_inr] at hh
      exact neg_eq_zero.mp hh.symm
  · rw [← cone_d_snd, hw, cone_snd_inr]

theorem cycle_injective_of_cofiber_acyclic (h : (homotopyCofiber f).Acyclic)
    (n : ℕ) : CycleInjective f n := by
  intro x hx hb
  obtain ⟨y, hy⟩ := hb
  let w : (homotopyCofiber f).X (n+1) := coneInl f n x - coneInr f (n+1) y
  have hw : Cycle (homotopyCofiber f) (n+1) w := by
    apply (cone_cycle_iff f n w).mpr
    simp only [w, map_sub, cone_fst_inl, cone_fst_inr, sub_zero,
      cone_snd_inl, cone_snd_inr, zero_sub, map_neg, hy, add_neg_cancel]
    exact ⟨hx, True.intro⟩
  obtain ⟨a, ha⟩ := (exactAt_iff_cycles_boundaries _ (n+1)).mp (h (n+1)) w hw
  refine ⟨-coneFst f (n+1) a, ?_⟩
  rw [map_neg]
  have hh := cone_d_fst f n a
  rw [ha] at hh
  simpa only [w, map_sub, cone_fst_inl, cone_fst_inr, sub_zero] using hh.symm

theorem quasiIso_of_cofiber_acyclic (h : (homotopyCofiber f).Acyclic) : QuasiIso f := by
  apply (quasiIso_iff_cycle_conditions f).mpr
  intro n
  exact ⟨cycle_injective_of_cofiber_acyclic f h n, cycle_surjective_of_cofiber_acyclic f h n⟩

theorem cofiber_acyclic_of_quasiIso [QuasiIso f] : (homotopyCofiber f).Acyclic := by
  have hf := (quasiIso_iff_cycle_conditions f).mp (inferInstance : QuasiIso f)
  intro n
  apply (exactAt_iff_cycles_boundaries _ n).mpr
  intro w hw
  cases n with
  | zero =>
    obtain ⟨x, hx, y, hy⟩ := (hf 0).2 (coneSnd f 0 w) (cycle_zero _ _)
    refine ⟨coneInl f 0 x + coneInr f 1 y, ?_⟩
    apply cone_zero_ext f
    rw [cone_d_snd]
    simpa only [map_add, cone_fst_inl, cone_fst_inr, add_zero,
      cone_snd_inl, cone_snd_inr, zero_add] using hy
  | succ n =>
    obtain ⟨hx, hy⟩ := (cone_cycle_iff f n w).mp hw
    have hboundary : ∃ y : L.X (n+1), L.d (n+1) n y = f.f n (coneFst f n w) := by
      refine ⟨-coneSnd f (n+1) w, ?_⟩
      rw [map_neg]
      exact (eq_neg_of_add_eq_zero_left hy).symm
    obtain ⟨a, ha⟩ := (hf n).1 (coneFst f n w) hx hboundary
    have hr : Cycle L (n+1) (coneSnd f (n+1) w + f.f (n+1) a) := by
      apply (cycle_succ_iff L n _).mpr
      have hcomm := congrArg (fun g => g.hom a) (f.comm (n+1) n)
      change L.d (n+1) n (f.f (n+1) a) = f.f n (K.d (n+1) n a) at hcomm
      rw [map_add, hcomm, ha]
      simpa only [add_comm] using hy
    obtain ⟨b, hb, c, hc⟩ := (hf (n+1)).2 _ hr
    refine ⟨coneInl f (n+1) (b-a) + coneInr f (n+1+1) c, ?_⟩
    apply cone_element_ext f n
    · rw [cone_d_fst]
      simp only [map_add, cone_fst_inl, cone_fst_inr, add_zero, map_sub,
        hb n, ha, zero_sub, neg_neg]
    · rw [cone_d_snd]
      simp only [map_add, cone_fst_inl, cone_fst_inr, add_zero,
        cone_snd_inl, cone_snd_inr, zero_add, map_sub, sub_self]
      rw [sub_add_eq_add_sub, hc]
      exact add_sub_cancel_right _ _

/-- The actual native mapping cone is acyclic exactly when the actual native map is a
quasi-isomorphism. All degrees, including zero, and arbitrary modules are covered. -/
theorem cofiber_acyclic_iff_quasiIso : (homotopyCofiber f).Acyclic ↔ QuasiIso f := by
  constructor
  · exact quasiIso_of_cofiber_acyclic f
  · intro h
    letI := h
    exact cofiber_acyclic_of_quasiIso f

end Cone
end Sharpness.ChainCofiber
