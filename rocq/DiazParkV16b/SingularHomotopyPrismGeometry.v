(** Actual continuous staircase maps from simplices into interval products. *)
From Stdlib Require Import Lia.
From mathcomp Require Import all_ssreflect all_algebra all_classical.
From mathcomp Require Import reals topology normedtype matrix_normedtype subtype_topology.
From DiazPark Require Import Category.
From DiazParkV16b Require Import SimplexCategory SimplexCategoryOperators SimplexCategoryIdentities
  TopologicalCategory TopologicalCategoryHomotopy TopologicalSimplexBasic
  TopologicalSimplexAffine TopologicalSimplexContinuity TopologicalSimplexFunctions
  SingularHomotopyPrismCombinatorics.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldNormedType.Exports.
Import DPTopological DPTopologicalHomotopy DPTopologicalSimplex
  DPTopologicalSimplexAffine DPTopologicalSimplexContinuity
  DPTopologicalSimplexFunctions DPSimplexCategory DPSimplexOperators DPSimplexIdentities
  DPSingularPrismCombinatorics.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Module DPSingularPrismGeometry.
Section Geometry.
Variable Real : realType.

Definition prism_weight n (i : 'I_n.+1) (k : 'I_n.+2) : Real :=
  (prism_time_value i k)%:R.

Lemma prism_weight_nonnegative n (i : 'I_n.+1) k : 0 <= prism_weight i k.
Proof. by rewrite /prism_weight; case: (prism_time_value i k); rewrite ?ler01 ?lexx. Qed.

Lemma prism_weight_le_one n (i : 'I_n.+1) k : prism_weight i k <= 1.
Proof. by rewrite /prism_weight; case: (prism_time_value i k); rewrite ?ler01 ?lexx. Qed.

Definition prism_time n (i : 'I_n.+1) (x : simplex Real n.+1) : unit_interval Real :=
  interval_weighted_value (prism_weight_nonnegative i) (prism_weight_le_one i) x.

Lemma prism_time_continuous n (i : 'I_n.+1) : continuous (@prism_time n i).
Proof. exact: interval_weighted_continuous. Qed.

Definition prism_parameter n (i : 'I_n.+1) (x : simplex Real n.+1) :=
  (prism_time i x, pushforward (codegeneracy i) x).

Lemma prism_parameter_continuous n (i : 'I_n.+1) :
  forall x, @continuous_at (simplex_space Real n.+1)
    [the topologicalType of (unit_interval_space Real * simplex_space Real n)%type]
    x (@prism_parameter n i).
Proof.
move=> x.
apply: (@cvg_pair (simplex_space Real n.+1) (unit_interval_space Real)
  (simplex_space Real n) (nbhs x) (nbhs (prism_time i x))
  (nbhs (pushforward (codegeneracy i) x))
  (@nbhs_filter (simplex_space Real n.+1) x)
  (@nbhs_filter (unit_interval_space Real) (prism_time i x))
  (@nbhs_filter (simplex_space Real n) (pushforward (codegeneracy i) x)));
  [exact: prism_time_continuous | exact: pushforward_continuous].
Qed.

Definition prism_parameter_map n (i : 'I_n.+1) :
    continuousType (simplex_space Real n.+1)
      (unit_interval_space Real * simplex_space Real n)%type :=
  continuous_map (@prism_parameter_continuous n i).

Lemma prism_time_face_value n (i : 'I_n.+1) (j : 'I_n.+2) (x : simplex Real n) :
  val (prism_time i (pushforward (coface j) x)) =
    weighted_value (fun k => (prism_time_value i (coface_value j k))%:R) x.
Proof. exact: weighted_pushforward. Qed.

Lemma prism_parameter_first n (x : simplex Real n) :
  prism_parameter (ord0 : 'I_n.+1) (pushforward (coface ord0) x) =
    (interval_one Real, x).
Proof.
apply pair_equal_spec; split.
- apply val_inj; rewrite prism_time_face_value.
  change (weighted_value (fun k : 'I_n.+1 =>
    (prism_time_value 0 (coface_value 0 k))%:R) x = 1).
  have e : (fun k : 'I_n.+1 => (prism_time_value 0 (coface_value 0 k))%:R) =
      (fun _ : 'I_n.+1 => (1 : Real)).
    by apply functional_extensionality_dep => k; rewrite prism_time_first.
  by rewrite e weighted_constant.
- rewrite pushforward_composition.
  have e : (fun k : 'I_n.+1 => codegeneracy ord0 (coface ord0 k)) = idfun.
    apply functional_extensionality_dep => k; apply val_inj.
    exact: codegeneracy_value_coface_same.
  change (pushforward (fun k : 'I_n.+1 => codegeneracy ord0 (coface ord0 k)) x = x).
  by rewrite e pushforward_identity.
Qed.

Lemma prism_parameter_last n (x : simplex Real n) :
  prism_parameter (ord_max : 'I_n.+1) (pushforward (coface ord_max) x) =
    (interval_zero Real, x).
Proof.
apply pair_equal_spec; split.
- apply val_inj; rewrite prism_time_face_value.
  change (weighted_value (fun k : 'I_n.+1 =>
    (prism_time_value n (coface_value n.+1 k))%:R) x = 0).
  have e : (fun k : 'I_n.+1 => (prism_time_value n (coface_value n.+1 k))%:R) =
      (fun _ : 'I_n.+1 => (0 : Real)).
    apply functional_extensionality_dep => k.
    have hk : (val k <= n)%coq_nat := le_S_n _ _ (elimT ssrnat.leP (ltn_ord k)).
    by rewrite (prism_time_last hk).
  by rewrite e weighted_constant.
- rewrite pushforward_composition.
  have e : (fun k : 'I_n.+1 => codegeneracy ord_max (coface ord_max k)) = idfun.
    apply functional_extensionality_dep => k; apply val_inj.
    exact: codegeneracy_value_coface_successor.
  change (pushforward (fun k : 'I_n.+1 => codegeneracy ord_max (coface ord_max k)) x = x).
  by rewrite e pushforward_identity.
Qed.

Lemma prism_parameter_middle n (i : 'I_n.+1) (x : simplex Real n.+1) :
  prism_parameter (vertex_widen i)
    (pushforward (coface (vertex_successor (vertex_widen i))) x) =
  prism_parameter (vertex_successor i)
    (pushforward (coface (vertex_successor (vertex_widen i))) x).
Proof.
apply pair_equal_spec; split.
- apply val_inj; rewrite !prism_time_face_value.
  congr (weighted_value _ x); apply functional_extensionality_dep => k.
  change ((prism_time_value i (coface_value (val i).+1 k))%:R =
    (prism_time_value (val i).+1 (coface_value (val i).+1 k))%:R :> Real).
  by rewrite prism_time_middle.
- rewrite !pushforward_composition.
  congr (pushforward _ x); apply functional_extensionality_dep => k; apply val_inj.
  change (codegeneracy_value i (coface_value (val i).+1 k) =
    codegeneracy_value (val i).+1 (coface_value (val i).+1 k)).
  by rewrite codegeneracy_value_coface_same codegeneracy_value_coface_successor.
Qed.

Lemma prism_parameter_left n (i : 'I_n.+1) (j : 'I_n.+2)
    (x : simplex Real n.+1) : (j <= i)%N ->
  prism_parameter (vertex_successor i) (pushforward (coface (vertex_widen j)) x) =
    (prism_time i x, pushforward (coface j) (pushforward (codegeneracy i) x)).
Proof.
move=> h; apply pair_equal_spec; split.
- apply val_inj; rewrite prism_time_face_value.
  change (weighted_value (fun k : 'I_n.+2 =>
    (prism_time_value (val i).+1 (coface_value j k))%:R) x =
    weighted_value (fun k : 'I_n.+2 => (prism_time_value i k)%:R) x).
  congr (weighted_value _ x); apply functional_extensionality_dep => k.
  by rewrite (@prism_time_left i j k (elimT ssrnat.leP h)).
- rewrite !pushforward_composition.
  have e := congr1 (@ordinal_function n.+1 n.+1) (coface_codegeneracy_lt h).
  exact (congr1 (fun f : 'I_n.+2 -> 'I_n.+2 => pushforward f x) e).
Qed.

Lemma prism_time_right_successor i j k : (i < j)%coq_nat ->
  prism_time_value i (coface_value j.+1 k) = prism_time_value i k.
Proof.
case: j => [|j] h; first inversion h.
apply prism_time_right; lia.
Qed.

Lemma prism_parameter_right n (i : 'I_n.+1) (j : 'I_n.+2)
    (x : simplex Real n.+1) : (i < j)%N ->
  prism_parameter (vertex_widen i) (pushforward (coface (vertex_successor j)) x) =
    (prism_time i x, pushforward (coface j) (pushforward (codegeneracy i) x)).
Proof.
move=> h; apply pair_equal_spec; split.
- apply val_inj; rewrite prism_time_face_value.
  change (weighted_value (fun k : 'I_n.+2 =>
    (prism_time_value i (coface_value (val j).+1 k))%:R) x =
    weighted_value (fun k : 'I_n.+2 => (prism_time_value i k)%:R) x).
  congr (weighted_value _ x); apply functional_extensionality_dep => k.
  by rewrite (@prism_time_right_successor i j k (elimT ssrnat.ltP h)).
- rewrite !pushforward_composition.
  have e := congr1 (@ordinal_function n.+1 n.+1) (coface_codegeneracy_gt h).
  exact (congr1 (fun f : 'I_n.+2 -> 'I_n.+2 => pushforward f x) e).
Qed.

End Geometry.
End DPSingularPrismGeometry.


