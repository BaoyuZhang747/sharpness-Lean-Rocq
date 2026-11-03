(** The dimension-uniform finite-average shrink factor, including n=0. *)
From mathcomp Require Import all_ssreflect all_algebra all_classical.
From mathcomp Require Import reals.
From DiazParkV16b Require Import SingularSubdivisionMeshAverages.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import DPSingularSubdivisionMeshAverages.
Local Open Scope ring_scope.

Module DPSingularSubdivisionMeshFactor.
Section Factor.
Variable Real : realType.

Definition mesh_factor n : Real := n%:R / n.+1%:R.

Lemma mesh_factor_nonnegative n : 0 <= mesh_factor n.
Proof. rewrite /mesh_factor; apply mulr_ge0; [exact: ler0n | by rewrite invr_ge0]. Qed.

Lemma mesh_factor_complement n : mesh_factor n = 1 - (n.+1%:R : Real)^-1.
Proof.
have hc : (n.+1%:R : Real) != 0 by rewrite pnatr_eq0.
have he : (n%:R : Real) = n.+1%:R - 1 by rewrite mulrSr addrK.
by rewrite /mesh_factor he mulrBl mulfV // mul1r.
Qed.

Lemma mesh_factor_lt_one n : mesh_factor n < 1.
Proof. by rewrite /mesh_factor ltr_pdivrMr ?ltr0n // mul1r ltr_nat. Qed.

Lemma mesh_factor_zero : mesh_factor 0 = 0.
Proof. by rewrite /mesh_factor mul0r. Qed.

Lemma nested_cardinality_factor (I : finType) (s t : {set I}) n
    (hs : (0 < #|s|)%N) (hst : s \subset t) (htn : (#|t| <= n.+1)%N) :
  (#|t|%:R : Real)^-1 * #|t :\: s|%:R <= mesh_factor n.
Proof.
have hstc := subset_leq_card hst.
have ht : (0 < #|t|)%N := leq_trans hs hstc.
have hc : (#|t|%:R : Real) != 0 by rewrite pnatr_eq0; exact: lt0n_neq0 ht.
have hp : 0 < (#|t|%:R : Real) by rewrite ltr0n.
have hnp : 0 < (n.+1%:R : Real) by rewrite ltr0n.
have hinv : (n.+1%:R : Real)^-1 <= (#|t|%:R)^-1.
  by rewrite lef_pV2 ?posrE // ler_nat.
have hs1 : (1 : Real) <= #|s|%:R by rewrite ler1n.
rewrite (cardsDS hst) natrB // mulrBr mulVf // mesh_factor_complement lerD2l lerN2.
apply: (le_trans hinv).
rewrite -{1}[(#|t|%:R : Real)^-1]mulr1.
apply: (ler_wpM2l _ hs1); by rewrite invr_ge0.
Qed.

Lemma mesh_average_nested_dimension_bound (I : finType) (s t : {set I}) n
    (hs : (0 < #|s|)%N) (hst : s \subset t) (htn : (#|t| <= n.+1)%N)
    (f : I -> Real) D (hD : 0 <= D)
    (h : forall i, i \in s -> forall j, j \in t -> `|f i - f j| <= D) :
  `|mesh_average s f - mesh_average t f| <= mesh_factor n * D.
Proof.
apply: (le_trans (mesh_average_nested_bound hs hst h)).
exact (ler_wpM2r hD (nested_cardinality_factor hs hst htn)).
Qed.

End Factor.
End DPSingularSubdivisionMeshFactor.
