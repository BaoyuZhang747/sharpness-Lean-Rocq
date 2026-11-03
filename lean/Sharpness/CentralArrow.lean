import Sharpness.CentralKernelAll

/-! The choice-independence step of Lemma 3.3, with actual fusion
homomorphisms agreeing modulo the central subgroup Z. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem
open CategoryTheory
variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)
    {Z : Subgroup S} (hZ : F.CentralSubgroup Z)
    {P Q : F.Object} (hZP : Z ≤ P.subgroup) (f g : P ⟶ Q)
    (same : ∀ x : P.subgroup, (f.val x).val⁻¹ * (g.val x).val ∈ Z)

include hZ hZP same

theorem image_mem_of_same_modZ (x : P.subgroup) : (g.val x).val ∈ F.imageSubgroup f := by
  let z := (f.val x).val⁻¹ * (g.val x).val
  have hz : z ∈ Z := same x
  let zP : P.subgroup := ⟨z, hZP hz⟩
  refine ⟨x * zP, ?_⟩
  change (f.val (x * zP)).val = (g.val x).val
  rw [map_mul]
  change (f.val x).val * (f.val zP).val = (g.val x).val
  have hfz := F.central_fixed hZ f.val f.property hZP ⟨z, hz⟩
  change (f.val zP).val = z at hfz
  rw [hfz]
  exact mul_inv_cancel_left _ _

def otherToImage : P ⟶ (⟨F.imageSubgroup f⟩ : F.Object) := by
  let r : P.subgroup →* F.imageSubgroup f :=
    { toFun x := ⟨(g.val x).val, F.image_mem_of_same_modZ hZ hZP f g same x⟩
      map_one' := by
        apply Subtype.ext
        exact congrArg (fun y : Q.subgroup => y.val) (map_one g.val)
      map_mul' x y := by
        apply Subtype.ext
        exact congrArg (fun z : Q.subgroup => z.val) (map_mul g.val x y) }
  refine ⟨r, F.codomain_restrict_mem g.val g.property (F.image_le f) r ?_⟩
  ext x
  rfl

def kernelFactorMap : P ⟶ P :=
  F.otherToImage hZ hZP f g same ≫ (F.imageIso f).inv

theorem kernelFactorMap_comp : F.kernelFactorMap hZ hZP f g same ≫ f = g := by
  have hf : f = (F.imageIso f).hom ≫ F.inclusion (F.image_le f) :=
    (F.image_factorization f).symm
  change (F.otherToImage hZ hZP f g same ≫ (F.imageIso f).inv) ≫ f = g
  conv_lhs =>
    rhs
    rw [hf]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  apply Subtype.ext
  ext x
  rfl

def kernelFactorAut : F.automorphismSubgroup P.subgroup := by
  let a := F.kernelFactorMap hZ hZP f g same
  let e : MulAut P.subgroup := MulEquiv.ofBijective a.val
    ((Nat.bijective_iff_injective_and_card a.val).mpr ⟨F.injective _ a.property, rfl⟩)
  exact ⟨e, a.property⟩

theorem kernelFactorAut_comp :
    (F.isoOfMulEquiv (F.kernelFactorAut hZ hZP f g same).val
      (F.kernelFactorAut hZ hZP f g same).property).hom ≫ f = g :=
  F.kernelFactorMap_comp hZ hZP f g same

theorem kernelFactorAut_modZ (x : P.subgroup) :
    x⁻¹ * (F.kernelFactorAut hZ hZP f g same).val x ∈ Z.subgroupOf P.subgroup := by
  let a := F.kernelFactorAut hZ hZP f g same
  let z := (f.val x).val⁻¹ * (g.val x).val
  have hz : z ∈ Z := same x
  let zP : P.subgroup := ⟨z, hZP hz⟩
  have hcomp := congrArg (fun h : P ⟶ Q => h.val x) (F.kernelFactorAut_comp hZ hZP f g same)
  change f.val (a.val x) = g.val x at hcomp
  have he : f.val (x⁻¹ * a.val x) = f.val zP := by
    rw [map_mul, map_inv, hcomp]
    apply Subtype.ext
    change (f.val x).val⁻¹ * (g.val x).val = (f.val zP).val
    exact (F.central_fixed hZ f.val f.property hZP ⟨z, hz⟩).symm
  have hpre := F.injective f.val f.property he
  change (x⁻¹ * a.val x).val ∈ Z
  rw [hpre]
  exact hz

theorem exists_gamma_of_same_modZ :
    letI := F.central_subgroupOf_normal hZ P.subgroup
    ∃ a : F.Gamma hZ hZP,
      (F.isoOfMulEquiv a.val.val a.val.property).hom ≫ f = g := by
  letI := F.central_subgroupOf_normal hZ P.subgroup
  let a := F.kernelFactorAut hZ hZP f g same
  have ha : a ∈ F.Gamma hZ hZP := by
    apply (quotient_kernel_iff (F.automorphismSubgroup P.subgroup).subtype
      (Z.subgroupOf P.subgroup) (F.central_aut_fixed hZ hZP) a).mpr
    exact F.kernelFactorAut_modZ hZ hZP f g same
  exact ⟨⟨a, ha⟩, F.kernelFactorAut_comp hZ hZP f g same⟩

theorem simple_maps_eq_of_same_modZ (p : ℕ) [Fact p.Prime]
    {k : Type u} [Field k] [CharP k p] (hS : IsPGroup p S)
    (M : MackeyModule.{u,u,u} k F.Orbit F.mackeyShape) (label : F.SimpleLabel M)
    (hZQ : Z ≤ label.Q.as.subgroup) :
    M.pull (F.toOrbit.map f) = M.pull (F.toOrbit.map g) ∧
      M.push (F.toOrbit.map f) = M.push (F.toOrbit.map g) := by
  letI := F.central_subgroupOf_normal hZ P.subgroup
  obtain ⟨a, ha⟩ := F.exists_gamma_of_same_modZ hZ hZP f g same
  constructor
  · rw [← ha, F.toOrbit.map_comp, M.pull_comp]
    change M.pull (F.toOrbit.map f) =
      (M.pull (F.automorphismToOrbitAut P.subgroup a.val).hom).comp (M.pull (F.toOrbit.map f))
    rw [F.central_kernel_pull_trivial p hS M label hZ hZQ P.subgroup hZP a, LinearMap.id_comp]
  · rw [← ha, F.toOrbit.map_comp, M.push_comp]
    change M.push (F.toOrbit.map f) =
      (M.push (F.toOrbit.map f)).comp (M.push (F.automorphismToOrbitAut P.subgroup a.val).hom)
    rw [F.central_kernel_push_trivial p hS M label hZ hZQ P.subgroup hZP a, LinearMap.comp_id]

end Sharpness.FusionSystem
