(** Every actual quasi-isomorphism between nonnegative degreewise-projective
    complexes has a constructed chain-homotopy inverse. *)
From mathcomp Require Import all_ssreflect all_algebra.
From DiazParkV16b Require Import ChainComplex LinearProjective ChainQuasiIsomorphism
  ChainProjectiveNullHomotopy ChainMappingCone ChainMappingConeAcyclic ChainConeHomotopyInverse.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPChainComplex DPLinearProjective DPChainQuasiIsomorphism
  DPChainProjectiveNullHomotopy DPChainMappingCone DPChainMappingConeAcyclic.
Local Open Scope ring_scope.

Module DPChainProjectiveQuasiIso.
Section Comparison.
Variable R : pzRingType.
Variables C D : chain_complex R.
Variable f : chain_map C D.
Variable hC : forall n, linear_projective (chain_term C n).
Variable hD : forall n, linear_projective (chain_term D n).
Variable hf : quasi_isomorphism f.
Let K := mapping_cone f.
Definition cone_contraction := @null_homotopy R K K
  (@mapping_cone_projective R C D f hC hD)
  (@mapping_cone_acyclic R C D f hf) (chain_identity K).
Definition contraction_at n := chain_homotopy_at cone_contraction n.
Lemma contraction_zero x : chain_d K 0%N (contraction_at 0%N x) = x.
Proof.
have e := chain_homotopy_zero cone_contraction x.
change (chain_d K 0%N (contraction_at 0%N x) = x - 0) in e.
by rewrite subr0 in e.
Qed.
Lemma contraction_succ n x :
  chain_d K n.+1 (contraction_at n.+1 x) + contraction_at n (chain_d K n x) = x.
Proof.
have e := @chain_homotopy_succ R K K (chain_identity K) (@chain_zero R K K) cone_contraction n x.
change (chain_d K n.+1 (contraction_at n.+1 x) + contraction_at n (chain_d K n x) = x - 0) in e.
by rewrite subr0 in e.
Qed.
Definition quasi_iso_inverse : chain_map D C :=
  @DPChainConeHomotopyInverse.inverse_chain R C D f contraction_at contraction_succ.
Definition quasi_iso_target_homotopy :
  chain_homotopy (chain_composition quasi_iso_inverse f) (chain_identity D) :=
  @DPChainConeHomotopyInverse.target_homotopy R C D f contraction_at contraction_zero contraction_succ.
Definition quasi_iso_source_homotopy :
  chain_homotopy (chain_composition f quasi_iso_inverse) (chain_identity C) :=
  @DPChainConeHomotopyInverse.source_homotopy R C D f contraction_at contraction_succ.

Theorem projective_quasi_iso_homotopy_inverse :
  exists g : chain_map D C,
    inhabited (chain_homotopy (chain_composition f g) (chain_identity C)) /\
    inhabited (chain_homotopy (chain_composition g f) (chain_identity D)).
Proof.
exists quasi_iso_inverse; split; constructor;
 [exact quasi_iso_source_homotopy | exact quasi_iso_target_homotopy].
Qed.
End Comparison.
End DPChainProjectiveQuasiIso.
