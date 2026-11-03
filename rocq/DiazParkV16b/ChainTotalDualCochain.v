(** Finite-total Hom duality commutes with the actual signed differentials in every degree. *)
From Coq Require Import Arith Lia.
From mathcomp Require Import all_ssreflect all_algebra boolp.
From DiazPark Require Import Category CategoryModules HomologicalComplex CategoryComplexIso.
From DiazParkV16b Require Import LinearMapSpace ChainComplex ChainDualCochain ChainTotalDual
  FirstQuadrantChainBicomplex FirstQuadrantChainTotal FirstQuadrantChainTotalSupport
  FirstQuadrantChainTotalInclusionDifferential FirstQuadrantCochainTotal.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomological DPLinearMapSpace DPChainDualCochain DPChainTotalDual
  DPFirstQuadrantChain DPFirstQuadrantChainTotal DPFirstQuadrantChainSupport
  DPFirstQuadrantChainTotalInclusionDifferential.
Local Open Scope ring_scope.

Module DPChainTotalDualCochain.
Section Dual.
Variable R : comPzRingType.
Variable A : lmodType R.
Variable K : bicomplex R.
Let D := dual_bicomplex A K.
Let C := dual_complex A (total_complex K).
Let T := DPFirstQuadrantTotal.total_complex D.

Theorem total_dual_commutes n (f : cochain_term C n) :
  cochain_d T n (@total_dual_forward R A K n f) =
    @total_dual_forward R A K n.+1 (cochain_d C n f).
Proof.
apply functional_extensionality_dep => p; apply functional_extensionality_dep => q;
  apply functional_extensionality_dep => h; apply ext => x.
change (evaluate (@DPFirstQuadrantTotal.total_d R D n (@total_dual_forward R A K n f) p q h) x =
  as_linear f (@total_d R K n (@total_include R K p q n.+1 h x))).
rewrite total_d_split linearD.
case: p h x => [|p] h x; case: q h x => [|q] h x.
- exfalso; lia.
- rewrite horizontal_boundary_include_zero vertical_boundary_include_succ linear0 linearZ.
  reflexivity.
- rewrite horizontal_boundary_include_succ vertical_boundary_include_zero linear0.
  reflexivity.
- rewrite horizontal_boundary_include_succ vertical_boundary_include_succ linearZ.
  reflexivity.
Qed.

Definition total_dual_cochain_map : cochain_map C T :=
  @term_iso_cochain_map R C T (total_dual_degree_iso A K) total_dual_commutes.
Definition total_dual_cochain_inverse : cochain_map T C :=
  @term_iso_cochain_inverse R C T (total_dual_degree_iso A K) total_dual_commutes.
Definition total_dual_cohomology_iso n :=
  @term_iso_cohomology_iso R C T (total_dual_degree_iso A K) total_dual_commutes n.

Theorem total_dual_cochain_component n f p q (h : (p+q)%coq_nat=n) x :
  evaluate (cochain_map_at total_dual_cochain_map n f p q h) x =
    evaluate f (@total_include R K p q n h x).
Proof. reflexivity. Qed.
Theorem total_dual_cochain_zero_column n f x :
  evaluate (cochain_map_at total_dual_cochain_map n f 0%N n erefl) x =
    evaluate f (@total_include R K 0 n n erefl x).
Proof. reflexivity. Qed.
Theorem total_dual_cochain_left n f :
  cochain_map_at total_dual_cochain_inverse n (cochain_map_at total_dual_cochain_map n f) = f.
Proof. exact: total_dual_forwardK. Qed.
Theorem total_dual_cochain_right n a :
  cochain_map_at total_dual_cochain_map n (cochain_map_at total_dual_cochain_inverse n a) = a.
Proof. exact: total_dual_inverseK. Qed.
End Dual.
End DPChainTotalDualCochain.
