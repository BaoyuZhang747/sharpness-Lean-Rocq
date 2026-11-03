import Sharpness.Unconditional.ChainHomotopyCofiberQuasiIso
import Sharpness.Unconditional.SmallChainComparisonFiniteSupport

/-! The algebraic small-chain comparison criterion. A chain inclusion is a
quasi-isomorphism if compatible operators are homotopic to the identities and
every ambient chain eventually enters its image. These are explicit geometric
obligations, not assumed conclusions about the induced homology map. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
universe u v
namespace Sharpness.SmallChainComparison
open CategoryTheory CategoryTheory.Limits HomologicalComplex ChainCofiber
variable {R : Type u} [Ring R]
variable {S K : ChainComplex (ModuleCat.{v} R) ℕ}

theorem end_pow_commutes (i : S ⟶ K) (t : End S) (s : End K)
    (w : t ≫ i = i ≫ s) (k : ℕ) : (t^k) ≫ i = i ≫ (s^k) := by
  induction k with
  | zero => simp
  | succ k ih =>
      simp only [pow_succ', End.mul_def, Category.assoc, w]
      rw [← Category.assoc, ih, Category.assoc]

theorem homologyMap_pow_eq_id (s : End K) (h : Homotopy s (𝟙 K)) (k n : ℕ) :
    homologyMap (s^k) n = 𝟙 _ := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ', End.mul_def, homologyMap_comp, ih,
        h.homologyMap_eq, homologyMap_id, Category.id_comp]

theorem chainMap_apply_d (i : S ⟶ K) (n m : ℕ) (x : S.X n) :
    i.f m (S.d n m x) = K.d n m (i.f n x) := by
  exact (congrArg (fun g => g.hom x) (i.comm n m)).symm

theorem cycle_of_injective_map (i : S ⟶ K)
    (hi : ∀ n, Function.Injective (i.f n)) (n : ℕ) (x : S.X n)
    (hx : Cycle K n (i.f n x)) : Cycle S n x := by
  intro m
  apply hi m
  rw [chainMap_apply_d, hx m, map_zero]

/-- Native quasi-isomorphism from actual subdivision-type data and eventual image membership. -/
theorem quasiIso_of_eventual_image
    (i : S ⟶ K) (hi : ∀ n, Function.Injective (i.f n))
    (t : End S) (s : End K) (w : t ≫ i = i ≫ s)
    (ht : Homotopy t (𝟙 S)) (hs : Homotopy s (𝟙 K))
    (hevent : ∀ n (x : K.X n), ∃ k : ℕ, ∃ y : S.X n, i.f n y = (s^k).f n x) :
    QuasiIso i := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap, ConcreteCategory.isIso_iff_bijective]
  constructor
  · apply (homologyMap_injective_iff i n).mpr
    intro x hx hb
    obtain ⟨y, hy⟩ := hb
    obtain ⟨k, z, hz⟩ := hevent (n+1) y
    have hb' : S.d (n+1) n z = (t^k).f n x := by
      apply hi n
      calc
        i.f n (S.d (n+1) n z) = K.d (n+1) n (i.f (n+1) z) :=
          chainMap_apply_d i (n+1) n z
        _ = K.d (n+1) n ((s^k).f (n+1) y) := congrArg (K.d (n+1) n) hz
        _ = (s^k).f n (K.d (n+1) n y) := (chainMap_apply_d (s^k) (n+1) n y).symm
        _ = (s^k).f n (i.f n x) := congrArg ((s^k).f n) hy
        _ = i.f n ((t^k).f n x) :=
          (congrArg (fun f : S ⟶ K => (f.f n).hom x) (end_pow_commutes i t s w k)).symm
    have hc : cycleClass S n ((t^k).f n x) (cycle_map (t^k) n x hx) = 0 :=
      (cycleClass_eq_zero_iff S n _ _).mpr ⟨z, hb'⟩
    apply (cycleClass_eq_zero_iff S n x hx).mp
    have hpow := congrArg (fun f => f.hom (cycleClass S n x hx))
      (homologyMap_pow_eq_id t ht k n)
    change homologyMap (t^k) n (cycleClass S n x hx) = cycleClass S n x hx at hpow
    rw [cycleClass_map] at hpow
    exact hpow.symm.trans hc
  · intro a
    obtain ⟨x, hx, rfl⟩ := cycleClass_surjective K n a
    obtain ⟨k, y, hy⟩ := hevent n x
    have hyc : Cycle S n y := cycle_of_injective_map i hi n y (by
      rw [hy]
      exact cycle_map (s^k) n x hx)
    refine ⟨cycleClass S n y hyc, ?_⟩
    rw [cycleClass_map]
    have hpow := congrArg (fun f => f.hom (cycleClass K n x hx))
      (homologyMap_pow_eq_id s hs k n)
    change homologyMap (s^k) n (cycleClass K n x hx) = cycleClass K n x hx at hpow
    rw [cycleClass_map] at hpow
    simpa only [hy] using hpow

end Sharpness.SmallChainComparison
