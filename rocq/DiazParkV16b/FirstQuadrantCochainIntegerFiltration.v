(** Honest integer extension of the actual column filtration: for every p<=0
    the complex is literally Tot, not zero. Positive indices use the already
    constructed column subcomplex. Transition maps commute with inclusion in
    Tot and satisfy identity/composition. No later pages are assumed here. *)
From Coq Require Import Arith ZArith Lia.
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryModules CategoryModuleLinear CategoryModuleExactness
  ModuleInfrastructure MackeyModuleCarriers MackeyModuleQuotient MackeyModuleMaps HomologicalComplex HomologicalMaps
  HomologicalCohomology HomologicalModuleIso CategoryComplexIso.
From DiazParkV16b Require Import FirstQuadrantCochainBicomplex FirstQuadrantCochainTotal
  FirstQuadrantCochainSpectralFiltration.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomological DiazParkHomologicalMaps DiazParkCohomology
  DiazParkHomologicalModuleIso DPFirstQuadrantCochain DPFirstQuadrantTotal DPColumnFiltration.
Local Open Scope ring_scope.

Module DPIntegerColumnFiltration.
Section IntegerFiltration.
Variable R : pzRingType.
Variable K : bicomplex R.

Definition zero_column_term_iso n : @isomorphism (module_category R)
    (column_term K 0%N n) (total_term K n).
Proof.
apply: (@linear_bijection_iso R (column_term K 0%N n) (total_term K n)
  (submodule_inclusion (column_subspace K 0%N n))).
- exact: submodule_val_injective.
- intro x; exists (@submodule_in R (total_term K n) (column_subspace K 0%N n) x (column_zero_full x)).
  reflexivity.
Defined.

Lemma zero_column_term_commutes n x :
    cochain_d (total_complex K) n (module_hom_fun (iso_hom (zero_column_term_iso n)) x) =
    module_hom_fun (iso_hom (zero_column_term_iso n.+1)) (cochain_d (column_complex K 0%N) n x).
Proof. reflexivity. Qed.

Definition zero_column_total_cochain_map := @term_iso_cochain_map R
  (column_complex K 0%N) (total_complex K) zero_column_term_iso zero_column_term_commutes.
Definition zero_column_total_cohomology_iso n := @term_iso_cohomology_iso R
  (column_complex K 0%N) (total_complex K) zero_column_term_iso zero_column_term_commutes n.

Definition integer_column (p : Z) : cochain_complex R :=
  if Z.leb p 0 then total_complex K else column_complex K (Z.to_nat p).

Lemma integer_column_nonpositive p (hp : Z.le p 0) : integer_column p = total_complex K.
Proof. unfold integer_column; have h : Z.leb p 0 = true by apply Z.leb_le. by rewrite h. Qed.

Lemma integer_column_positive p (hp : Z.lt 0 p) : integer_column p = column_complex K (Z.to_nat p).
Proof. unfold integer_column; have h : Z.leb p 0 = false by apply Z.leb_gt. by rewrite h. Qed.

Lemma integer_column_nat_succ p : integer_column (Z.of_nat p.+1) = column_complex K p.+1.
Proof.
rewrite integer_column_positive; [by rewrite Nat2Z.id|lia].
Qed.

Definition integer_inclusion p : cochain_map (integer_column p) (total_complex K).
Proof.
unfold integer_column; destruct (Z.leb p 0).
- exact (cochain_identity (total_complex K)).
- exact (column_inclusion K (Z.to_nat p)).
Defined.

Definition integer_transition p q (h : Z.le p q) : cochain_map (integer_column q) (integer_column p).
Proof.
unfold integer_column; destruct (Z.leb p 0) eqn:hp; destruct (Z.leb q 0) eqn:hq.
- exact (cochain_identity (total_complex K)).
- exact (column_inclusion K (Z.to_nat q)).
- apply Z.leb_gt in hp; apply Z.leb_le in hq; exfalso; lia.
- apply (column_transition K).
  apply Z.leb_gt in hp; apply Z.leb_gt in hq.
  have hp0 : Z.le 0 p by lia.
  have hq0 : Z.le 0 q by lia.
  exact (proj1 (Z2Nat.inj_le p q hp0 hq0) h).
Defined.

Lemma integer_inclusion_injective p n : injective (cochain_map_at (integer_inclusion p) n).
Proof.
unfold integer_inclusion, integer_column; destruct (Z.leb p 0); simpl.
- exact: (fun x y h => h).
- exact: submodule_val_injective.
Qed.

Lemma integer_transition_total p q (h : Z.le p q) n (x : cochain_term (integer_column q) n) :
    cochain_map_at (integer_inclusion p) n (cochain_map_at (integer_transition h) n x) =
    cochain_map_at (integer_inclusion q) n x.
Proof.
destruct p as [|p|p]; destruct q as [|q|q]; try reflexivity; exfalso; lia.
Qed.

Theorem integer_transition_identity p n (x : cochain_term (integer_column p) n) :
    cochain_map_at (integer_transition (Z.le_refl p)) n x = x.
Proof.
apply (@integer_inclusion_injective p n).
exact: integer_transition_total.
Qed.

Theorem integer_transition_composition p q r (hpq : Z.le p q) (hqr : Z.le q r)
    n (x : cochain_term (integer_column r) n) :
    cochain_map_at (integer_transition hpq) n (cochain_map_at (integer_transition hqr) n x) =
      cochain_map_at (integer_transition (Z.le_trans _ _ _ hpq hqr)) n x.
Proof.
apply (@integer_inclusion_injective p n).
by rewrite !integer_transition_total.
Qed.

Definition integer_nonpositive_cohomology_iso p (hp : Z.le p 0) n : @isomorphism (module_category R)
    (cohomology (integer_column p) n) (cohomology (total_complex K) n).
Proof. rewrite (integer_column_nonpositive hp); exact (@iso_refl (module_category R) _). Defined.

Definition integer_nat_cohomology_iso p n : @isomorphism (module_category R)
    (cohomology (integer_column (Z.of_nat p)) n) (cohomology (column_complex K p) n).
Proof.
destruct p as [|p].
- exact (iso_symm (zero_column_total_cohomology_iso n)).
- rewrite integer_column_nat_succ; exact (@iso_refl (module_category R) _).
Defined.

Theorem integer_term_beyond_degree_zero p n (h : Z.lt (Z.of_nat n) p)
    (x : cochain_term (integer_column p) n) : x = 0.
Proof.
have hp : Z.lt 0 p by lia.
rewrite (integer_column_positive hp) in x *.
apply column_beyond_degree_zero.
have hpn : Z.le 0 p by lia.
have hn := Z2Nat.id p hpn.
lia.
Qed.

End IntegerFiltration.
End DPIntegerColumnFiltration.
