(** Actual relative column complexes F^p Tot / F^q Tot and their degreewise
    short exact sequences. The quotient is taken inside F^p, so its native
    connecting map has the required filtered-cohomology target. *)
From Coq Require Import Arith Lia.
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import ModuleInfrastructure MackeyModuleCarriers
  MackeyModuleQuotient MackeyModuleMaps HomologicalComplex HomologicalCohomology
  HomologicalCohomologyMaps HomologicalConnecting HomologicalLongExact.
From DiazParkV16b Require Import FirstQuadrantCochainBicomplex
  FirstQuadrantCochainTotal FirstQuadrantCochainTotalSupport
  FirstQuadrantCochainSpectralFiltration.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomological DiazParkCohomology DiazParkCohomologyMaps
  DiazParkHomologicalConnecting DPFirstQuadrantCochain DPFirstQuadrantTotal
  DPFirstQuadrantSupport DPColumnFiltration.
Local Open Scope ring_scope.

Module DPColumnRelative.
Section Relative.
Variable R : pzRingType.
Variable K : bicomplex R.

Definition relative_subspace (p q n : nat) : module_subspace (column_term K p n).
Proof.
refine (@ModuleSubspace R (column_term K p n)
  (fun x => column_subspace K q n (submodule_val x)) _ _ _).
- exact: supported_from_zero.
- intros x y hx hy; exact: supported_from_add hx hy.
- intros a x hx; exact: supported_from_scale hx.
Defined.

Definition relative_term p q n : lmodType R := module_quotient (relative_subspace p q n).

Lemma relative_d_preserves p q n (x : column_term K p n) :
    relative_subspace p q n x -> relative_subspace p q n.+1 (@column_d R K p n x).
Proof. exact: total_d_supported. Qed.

Definition relative_d p q n : {linear relative_term p q n -> relative_term p q n.+1} :=
  @quotient_map R (column_term K p n) (column_term K p n.+1) (@column_d R K p n)
    (relative_subspace p q n) (relative_subspace p q n.+1) (@relative_d_preserves p q n).
Arguments relative_d {p q n}.

Lemma relative_d_pi p q n (x : column_term K p n) :
    relative_d (quotient_pi (relative_subspace p q n) x) =
      quotient_pi (relative_subspace p q n.+1) (@column_d R K p n x).
Proof. exact: quotient_map_pi. Qed.

Lemma relative_d_squared p q n (x : relative_term p q n) : relative_d (relative_d x) = 0.
Proof.
have [y <-] := quotient_pi_surjective x.
by rewrite !relative_d_pi column_d_squared linear0.
Qed.

Definition relative_complex p q : cochain_complex R :=
  @CochainComplex R (relative_term p q) (fun n => @relative_d p q n)
    (relative_d_squared (p := p) (q := q)).

Definition relative_projection p q : cochain_map (column_complex K p) (relative_complex p q).
Proof.
refine (@CochainMap R (column_complex K p) (relative_complex p q)
  (fun n => quotient_pi (relative_subspace p q n)) _).
intros n x; exact: relative_d_pi.
Defined.

Theorem relative_short_exact p q (h : (p <= q)%coq_nat) :
    degreewise_short_exact (column_transition K h) (relative_projection p q).
Proof.
constructor.
- intros n x y hxy; apply submodule_val_injective.
  exact (congr1 (fun z : column_term K p n => submodule_val z) hxy).
- intros n x.
  apply/(quotient_pi_kernel (relative_subspace p q n) (cochain_map_at (column_transition K h) n x)).
  exact: submodule_val_mem.
- intros n y hy.
  have hy' : relative_subspace p q n y by apply/(quotient_pi_kernel (relative_subspace p q n) y).
  exists (@submodule_in R (total_term K n) (column_subspace K q n) (submodule_val y) hy').
  apply submodule_val_injective; reflexivity.
- intros n z; exact: quotient_pi_surjective.
Qed.

Definition relative_connecting p q (h : (p <= q)%coq_nat) n :
    {linear cohomology (relative_complex p q) n -> cohomology (column_complex K q) n.+1} :=
  connecting_map (relative_short_exact h) n.

Theorem relative_cohomology_exact p q (h : (p <= q)%coq_nat) :
    injective (cohomology_map (column_transition K h) 0%N) /\
    forall n,
      linear_exact (cohomology_map (column_transition K h) n)
        (cohomology_map (relative_projection p q) n) /\
      linear_exact (cohomology_map (relative_projection p q) n) (relative_connecting h n) /\
      linear_exact (relative_connecting h n) (cohomology_map (column_transition K h) n.+1).
Proof. exact: (long_exact_cohomology (relative_short_exact h)). Qed.

End Relative.
End DPColumnRelative.
