(** The actual decreasing column filtration of the constructed finite-diagonal
    total complex. Quotients and their short exact sequences are constructed
    from native module subspaces; no spectral-sequence laws are assumptions. *)
From Coq Require Import Arith Lia.
From HB Require Import structures.
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import ModuleInfrastructure MackeyModuleCarriers
  MackeyModuleQuotient MackeyModuleMaps HomologicalComplex.
From DiazParkV16b Require Import FirstQuadrantCochainBicomplex
  FirstQuadrantCochainTotal FirstQuadrantCochainTotalSupport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomological DPFirstQuadrantCochain
  DPFirstQuadrantTotal DPFirstQuadrantSupport.
Local Open Scope ring_scope.

Module DPColumnFiltration.
Section Filtration.
Variable R : pzRingType.
Variable K : bicomplex R.

Definition column_subspace (p n : nat) : module_subspace (total_term K n).
Proof.
refine (@ModuleSubspace R (total_term K n) (fun x => supported_from x p) _ _ _).
- exact: supported_from_zero.
- intros x y hx hy; exact: supported_from_add hx hy.
- intros a x hx; exact: supported_from_scale hx.
Defined.

Definition column_term p n : lmodType R := submodule_carrier (column_subspace p n).

Definition column_d p n : {linear column_term p n -> column_term p n.+1} :=
  @submodule_map R (total_term K n) (total_term K n.+1) (@total_d R K n)
    (column_subspace p n) (column_subspace p n.+1) (fun x hx => total_d_supported hx).
Arguments column_d {p n}.

Lemma column_d_val p n (x : column_term p n) :
    submodule_val (column_d x) = total_d (submodule_val x).
Proof. reflexivity. Qed.

Lemma column_d_squared p n (x : column_term p n) : column_d (column_d x) = 0.
Proof.
apply submodule_val_injective.
change (total_d (total_d (submodule_val x)) = 0).
exact: total_d_squared.
Qed.

Definition column_complex p : cochain_complex R :=
  @CochainComplex R (column_term p) (fun n => @column_d p n) (column_d_squared (p := p)).

Definition column_inclusion p : cochain_map (column_complex p) (total_complex K).
Proof.
refine (@CochainMap R (column_complex p) (total_complex K)
  (fun n => submodule_inclusion (column_subspace p n)) _).
intros n x; reflexivity.
Defined.

Lemma column_inclusion_at p n (x : column_term p n) :
    cochain_map_at (column_inclusion p) n x = submodule_val x.
Proof. reflexivity. Qed.

Lemma column_subspace_decreasing p q n (h : (p <= q)%coq_nat) :
    subspace_le (column_subspace q n) (column_subspace p n).
Proof. intros x hx; exact: supported_from_mono hx h. Qed.

Definition column_transition_at p q (h : (p <= q)%coq_nat) n :
    {linear column_term q n -> column_term p n} :=
  @submodule_map R (total_term K n) (total_term K n) (idfun : {linear total_term K n -> total_term K n})
    (column_subspace q n) (column_subspace p n) (@column_subspace_decreasing p q n h).

Definition column_transition p q (h : (p <= q)%coq_nat) :
    cochain_map (column_complex q) (column_complex p).
Proof.
refine (@CochainMap R (column_complex q) (column_complex p) (column_transition_at h) _).
intros n x; apply submodule_val_injective; reflexivity.
Defined.

Lemma column_transition_val p q (h : (p <= q)%coq_nat) n (x : column_term q n) :
    submodule_val (cochain_map_at (column_transition h) n x) = submodule_val x.
Proof. reflexivity. Qed.

Lemma column_zero_full n (x : total_term K n) : column_subspace 0%N n x.
Proof. intros p q hpq hp; lia. Qed.

Lemma column_beyond_degree_zero p n (h : (n < p)%coq_nat) (x : column_term p n) : x = 0.
Proof.
apply submodule_val_injective.
change (submodule_val x = 0).
apply supported_past_diagonal_zero.
apply: (supported_from_mono (submodule_val_mem x)); lia.
Qed.

Lemma column_inclusion_injective p n : injective (cochain_map_at (column_inclusion p) n).
Proof. exact: submodule_val_injective. Qed.

Definition column_quotient_term p n : lmodType R := module_quotient (column_subspace p n).

Definition column_quotient_d p n :
    {linear column_quotient_term p n -> column_quotient_term p n.+1} :=
  @quotient_map R (total_term K n) (total_term K n.+1) (@total_d R K n)
    (column_subspace p n) (column_subspace p n.+1) (fun x hx => total_d_supported hx).
Arguments column_quotient_d {p n}.

Lemma column_quotient_d_pi p n (x : total_term K n) :
    column_quotient_d (quotient_pi (column_subspace p n) x) =
      quotient_pi (column_subspace p n.+1) (total_d x).
Proof. exact: quotient_map_pi. Qed.

Lemma column_quotient_d_squared p n (x : column_quotient_term p n) :
    column_quotient_d (column_quotient_d x) = 0.
Proof.
have [y <-] := quotient_pi_surjective x.
by rewrite !column_quotient_d_pi total_d_squared linear0.
Qed.

Definition column_quotient_complex p : cochain_complex R :=
  @CochainComplex R (column_quotient_term p) (fun n => @column_quotient_d p n)
    (column_quotient_d_squared (p := p)).

Definition column_quotient_projection p :
    cochain_map (total_complex K) (column_quotient_complex p).
Proof.
refine (@CochainMap R (total_complex K) (column_quotient_complex p)
  (fun n => quotient_pi (column_subspace p n)) _).
intros n x; exact: column_quotient_d_pi.
Defined.

Theorem column_short_exact p :
    degreewise_short_exact (column_inclusion p) (column_quotient_projection p).
Proof.
constructor.
- exact: column_inclusion_injective.
- intros n x; apply/(quotient_pi_kernel (column_subspace p n) (submodule_val x)).
  exact: submodule_val_mem.
- intros n y hy.
  have hy' : column_subspace p n y by apply/(quotient_pi_kernel (column_subspace p n) y).
  exists (@submodule_in R (total_term K n) (column_subspace p n) y hy'); reflexivity.
- intros n z; exact: quotient_pi_surjective.
Qed.

End Filtration.
End DPColumnFiltration.
