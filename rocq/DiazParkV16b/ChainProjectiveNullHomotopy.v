(** Maps from degreewise-projective nonnegative complexes to acyclic complexes
    have an explicitly constructed null homotopy. *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra boolp.
From DiazPark Require Import ModuleInfrastructure MackeyModuleCarriers MackeyModuleMaps.
From DiazParkV16b Require Import ChainComplex ChainHomology LinearProjective.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPChainComplex DPChainHomology DPLinearProjective.
Local Open Scope ring_scope.

Module DPChainProjectiveNullHomotopy.
Section Restrict.
Variable R : pzRingType.
Variables V W : lmodType R.
Variable f : {linear V -> W}.
Variable N : module_subspace W.
Variable hf : forall x, N (f x).
Definition cod_restrict (x : V) : submodule_carrier N :=
  @submodule_in R W N (f x) (hf x).
Lemma cod_restrict_linear : linear cod_restrict.
Proof. move=> r x y; apply submodule_val_injective; change (f (r *: x + y) = r *: f x + f y); exact: linearP. Qed.
HB.instance Definition _ := GRing.isLinear.Build R _ _ _ cod_restrict cod_restrict_linear.
End Restrict.
Section NullHomotopy.
Variable R : pzRingType.
Variables C D : chain_complex R.
Variable hP : forall n, linear_projective (chain_term C n).
Variable hD : acyclic D.
Variable f : chain_map C D.

Definition differential_to_cycles n :
    {linear chain_term D n.+1 -> cycle_module D n} :=
  @cod_restrict R (chain_term D n.+1) (chain_term D n)
    (chain_d D n) (cycle_subspace D n)
    (fun x => proj2 (@cycle_subspaceE R D n _)
      (@boundary_cycle R D n _ (ex_intro _ x erefl))).

Lemma differential_to_cycles_surjective n :
  forall y, exists x, differential_to_cycles n x = y.
Proof.
move=> y.
have [x hx] := @hD n (val y) (proj1 (@cycle_subspaceE R D n _) (submodule_val_mem y)).
exists x; apply submodule_val_injective; exact hx.
Qed.

Definition lift_cycle_map n (a : {linear chain_term C n -> chain_term D n})
    (ha : forall x, @cycle R D n (a x)) :
    {linear chain_term C n -> chain_term D n.+1}.
Proof.
pose aZ := @cod_restrict R (chain_term C n) (chain_term D n)
  a (cycle_subspace D n) (fun x => proj2 (@cycle_subspaceE R D n _) (ha x)).
exact (proj1_sig (constructive_indefinite_description
  (@hP n _ _ (differential_to_cycles n) (@differential_to_cycles_surjective n) aZ))).
Defined.

Lemma lift_cycle_map_d n (a : {linear chain_term C n -> chain_term D n})
    (ha : forall x, @cycle R D n (a x)) x :
  chain_d D n (lift_cycle_map ha x) = a x.
Proof.
rewrite /lift_cycle_map.
pose aZ : {linear chain_term C n -> cycle_module D n} :=
  @cod_restrict R (chain_term C n) (chain_term D n) a (cycle_subspace D n)
    (fun x => proj2 (@cycle_subspaceE R D n _) (ha x)).
have hh := proj2_sig (constructive_indefinite_description
  (@hP n _ _ (differential_to_cycles n) (@differential_to_cycles_surjective n) aZ)) x.
exact (congr1 (fun z : cycle_module D n => val z) hh).
Qed.

Definition step_remainder n (h : {linear chain_term C n -> chain_term D n.+1})
    (x : chain_term C n.+1) := chain_map_at f n.+1 x - h (chain_d C n x).
Lemma step_remainder_linear n h : linear (@step_remainder n h).
Proof.
move=> r x y; rewrite /step_remainder !linearP scalerBr addrACA.
by rewrite /= scalerN.
Qed.
HB.instance Definition _ n h := GRing.isLinear.Build R _ _ _ (@step_remainder n h) (@step_remainder_linear n h).

Record partial_step n := PartialStep {
  step_map : {linear chain_term C n -> chain_term D n.+1};
  step_remainder_cycle : forall x, @cycle R D n.+1 (step_remainder step_map x)
}.

Definition first_step : partial_step 0%N.
Proof.
pose h := lift_cycle_map (a := chain_map_at f 0%N) (fun _ => I).
refine (@PartialStep 0%N h _).
move=> x; change (chain_d D 0%N (chain_map_at f 1%N x - h (chain_d C 0%N x)) = 0).
by rewrite linearB chain_map_commutes /h lift_cycle_map_d subrr.
Defined.

Definition next_step n (s : partial_step n) : partial_step n.+1.
Proof.
pose h := lift_cycle_map (a := step_remainder (step_map s)) (step_remainder_cycle s).
refine (@PartialStep n.+1 h _).
move=> x; change (chain_d D n.+1 (chain_map_at f n.+2 x - h (chain_d C n.+1 x)) = 0).
rewrite linearB chain_map_commutes /h lift_cycle_map_d /step_remainder /=.
change (chain_map_at f n.+1 (chain_d C n.+1 x) -
  (chain_map_at f n.+1 (chain_d C n.+1 x) - step_map s (chain_d C n (chain_d C n.+1 x))) = 0).
by rewrite chain_d2 linear0 subr0 subrr.
Defined.

Fixpoint constructed_step n : partial_step n :=
  match n as k return partial_step k with
  | 0%N => first_step
  | k.+1 => next_step (constructed_step k)
  end.

Definition null_homotopy_at n := step_map (constructed_step n).
Lemma null_homotopy_zero x :
  chain_d D 0%N (null_homotopy_at 0%N x) = chain_map_at f 0%N x.
Proof. exact: lift_cycle_map_d. Qed.
Lemma null_homotopy_succ n x :
  chain_d D n.+1 (null_homotopy_at n.+1 x) + null_homotopy_at n (chain_d C n x) =
  chain_map_at f n.+1 x.
Proof.
change (chain_d D n.+1
  (lift_cycle_map (step_remainder_cycle (constructed_step n)) x) +
  step_map (constructed_step n) (chain_d C n x) = chain_map_at f n.+1 x).
by rewrite lift_cycle_map_d /step_remainder subrK.
Qed.

Definition zero_at n (_ : chain_term C n) : chain_term D n := 0.
Lemma zero_at_linear n : linear (@zero_at n).
Proof. by move=> r x y; rewrite /zero_at scaler0 addr0. Qed.
HB.instance Definition _ n := GRing.isLinear.Build R _ _ _ (@zero_at n) (@zero_at_linear n).
Definition chain_zero : chain_map C D.
Proof.
refine (@ChainMap R C D (fun n => (@zero_at n : {linear chain_term C n -> chain_term D n})) _).
by move=> n x; change (chain_d D n 0 = 0); rewrite linear0.
Defined.

Definition null_homotopy : chain_homotopy f chain_zero.
Proof.
refine (@ChainHomotopy R C D f chain_zero null_homotopy_at _ _).
- by move=> x; rewrite /= subr0; exact: null_homotopy_zero.
- by move=> n x; rewrite /= subr0; exact: null_homotopy_succ.
Defined.
End NullHomotopy.
End DPChainProjectiveNullHomotopy.
