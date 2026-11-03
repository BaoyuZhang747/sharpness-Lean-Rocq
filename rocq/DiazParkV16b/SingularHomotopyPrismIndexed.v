(** Natural-number indexed faces of the actual singular prism. *)
From mathcomp Require Import all_ssreflect all_algebra all_classical.
From mathcomp Require Import reals topology.
From DiazPark Require Import Category.
From DiazParkV16b Require Import SimplexCategoryIdentities SimplicialSet
  SimplicialSetOperators SimplicialChains SingularSet TopologicalCategory
  TopologicalCategoryHomotopy SingularHomotopyPrism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPSimplexIdentities DPSimplicialSet DPSimplicialOperators DPSimplicialChains
  DPSingularSet DPTopological DPTopologicalHomotopy DPSingularPrism.

Module DPSingularPrismIndexed.
Section Indexed.
Variable Real : realType.
Variables X Y : topologicalType.
Variables f g : hom topological_category X Y.
Variable H : continuous_homotopy Real f g.

Definition singular_indexed_prism n i (s : simplex (singular_set Real X) n) :
    simplex (singular_set Real Y) n.+1 := singular_prism H (inord i) s.
Arguments singular_indexed_prism n i s : clear implicits.

Lemma singular_indexed_prism_first n (s : simplex (singular_set Real X) n) :
  @indexed_face (singular_set Real Y) n 0 (singular_indexed_prism n 0 s) =
    component (singular_map Real g) n s.
Proof.
have e k : (inord 0 : 'I_k.+1) = ord0 by apply val_inj; exact: inordK.
rewrite /indexed_face /singular_indexed_prism !e.
exact: singular_prism_first.
Qed.

Lemma singular_indexed_prism_last n (s : simplex (singular_set Real X) n) :
  @indexed_face (singular_set Real Y) n n.+1 (singular_indexed_prism n n s) =
    component (singular_map Real f) n s.
Proof.
have e k : (inord k : 'I_k.+1) = ord_max by apply val_inj; exact: inordK.
rewrite /indexed_face /singular_indexed_prism !e.
exact: singular_prism_last.
Qed.

Lemma singular_indexed_prism_middle n i (s : simplex (singular_set Real X) n) :
  (i < n)%N ->
  @indexed_face (singular_set Real Y) n i.+1 (singular_indexed_prism n i s) =
  @indexed_face (singular_set Real Y) n i.+1 (singular_indexed_prism n i.+1 s).
Proof.
case: n s => [|n] s hi; first by rewrite ltn0 in hi.
pose I : 'I_n.+1 := Ordinal hi.
have e1 : (inord i : 'I_n.+2) = vertex_widen I.
  apply val_inj; apply inordK; exact: ltn_trans hi (ltnSn _).
have e2 : (inord i.+1 : 'I_n.+2) = vertex_successor I.
  apply val_inj; exact: inordK.
have e3 : (inord i.+1 : 'I_n.+3) = vertex_successor (vertex_widen I).
  apply val_inj; apply inordK; exact: ltn_trans hi (ltnSn _).
rewrite /indexed_face /singular_indexed_prism e1 e2 e3.
exact: singular_prism_middle.
Qed.

Lemma singular_indexed_prism_left n i j (s : simplex (singular_set Real X) n.+1) :
  (i <= n)%N -> (j <= i)%N ->
  @indexed_face (singular_set Real Y) n.+1 j (singular_indexed_prism n.+1 i.+1 s) =
    singular_indexed_prism n i (@indexed_face (singular_set Real X) n j s).
Proof.
move=> hi hj.
have hi' : (i < n.+1)%N by rewrite ltnS.
have hj' : (j < n.+2)%N := leq_ltn_trans hj (ltn_trans hi' (ltnSn _)).
pose I : 'I_n.+1 := Ordinal hi'.
pose J : 'I_n.+2 := Ordinal hj'.
have e1 : (inord i : 'I_n.+1) = I by apply val_inj; exact: inordK.
have e2 : (inord j : 'I_n.+2) = J by apply val_inj; exact: inordK.
have e3 : (inord i.+1 : 'I_n.+2) = vertex_successor I by apply val_inj; exact: inordK.
have e4 : (inord j : 'I_n.+3) = vertex_widen J.
  apply val_inj; apply inordK; exact: ltn_trans hj' (ltnSn _).
rewrite /indexed_face /singular_indexed_prism e1 e2 e3 e4.
apply singular_prism_left; exact hj.
Qed.

Lemma singular_indexed_prism_right n i j (s : simplex (singular_set Real X) n.+1) :
  (i <= j)%N -> (j <= n)%N ->
  @indexed_face (singular_set Real Y) n.+1 j.+2 (singular_indexed_prism n.+1 i s) =
    singular_indexed_prism n i (@indexed_face (singular_set Real X) n j.+1 s).
Proof.
move=> hi hj.
have hi' : (i < n.+1)%N by rewrite ltnS; exact: leq_trans hi hj.
have hj' : (j.+1 < n.+2)%N by rewrite !ltnS.
pose I : 'I_n.+1 := Ordinal hi'.
pose J : 'I_n.+2 := Ordinal hj'.
have e1 : (inord i : 'I_n.+1) = I by apply val_inj; exact: inordK.
have e2 : (inord j.+1 : 'I_n.+2) = J by apply val_inj; exact: inordK.
have e3 : (inord i : 'I_n.+2) = vertex_widen I.
  apply val_inj; apply inordK; exact: ltn_trans hi' (ltnSn _).
have e4 : (inord j.+2 : 'I_n.+3) = vertex_successor J by apply val_inj; exact: inordK.
rewrite /indexed_face /singular_indexed_prism e1 e2 e3 e4.
apply singular_prism_right; exact hi.
Qed.

End Indexed.
End DPSingularPrismIndexed.
