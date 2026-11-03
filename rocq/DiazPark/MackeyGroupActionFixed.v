From HB Require Import structures.
From mathcomp Require Import all_boot all_algebra all_fingroup boolp
  vector pgroup mxrepresentation mxabelem.
From DiazPark Require Import ModuleInfrastructure ModuleFiniteDimensional
  MackeyModuleCarriers MackeyModuleMaps MackeyGroupAction.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope group_scope.
Local Open Scope ring_scope.

Section FiniteCoordinates.
Variable K : fieldType.
Variable V : lmodType K.
Variable hV : module_finitely_generated V.

Lemma finite_coordinates_inverse_exists :
    exists g : 'rV[K]_(dim (chosen_finite_model hV)) -> V,
      cancel (finite_coordinates hV) g /\ cancel g (finite_coordinates hV).
Proof.
have [g hg gh] := finite_coordinates_bijective hV.
exists g; by split.
Qed.

Definition finite_coordinates_inverse := proj1_sig (cid finite_coordinates_inverse_exists).

Lemma finite_coordinatesK : cancel (finite_coordinates hV) finite_coordinates_inverse.
Proof. exact: (proj1 (proj2_sig (cid finite_coordinates_inverse_exists))). Qed.

Lemma finite_coordinates_inverseK : cancel finite_coordinates_inverse (finite_coordinates hV).
Proof. exact: (proj2 (proj2_sig (cid finite_coordinates_inverse_exists))). Qed.

HB.instance Definition _ := GRing.isLinear.Build K V 'rV[K]_(dim (chosen_finite_model hV))
  _ (finite_coordinates hV) (finite_coordinates_linear hV).

Lemma finite_coordinates_inverse_linear : linear finite_coordinates_inverse.
Proof. exact: can2_linear finite_coordinatesK finite_coordinates_inverseK. Qed.

HB.instance Definition _ := GRing.isLinear.Build K 'rV[K]_(dim (chosen_finite_model hV)) V
  _ finite_coordinates_inverse finite_coordinates_inverse_linear.

End FiniteCoordinates.

Arguments finite_coordinates_inverse {K V} hV _.

Section FiniteAction.
Variable K : fieldType.
Variable G : finGroupType.
Variable V : lmodType K.
Variable hV : module_finitely_generated V.
Variable rho : right_linear_action G V.
Local Notation d := (dim (chosen_finite_model hV)).

Definition coordinate_action g (u : 'rV[K]_d) : 'rV[K]_d :=
  finite_coordinates hV (right_action rho g (finite_coordinates_inverse hV u)).

Lemma coordinate_action_linear g : linear (coordinate_action g).
Proof. by move=> a u v; rewrite /coordinate_action !linearP. Qed.

HB.instance Definition _ g := GRing.isLinear.Build K 'rV[K]_d 'rV[K]_d
  _ (coordinate_action g) (coordinate_action_linear g).

Definition coordinate_action_matrix g : 'M[K]_d :=
  lin1_mx (coordinate_action g : {linear 'rV[K]_d -> 'rV[K]_d}).

Lemma coordinate_action_matrixE g u : u *m coordinate_action_matrix g = coordinate_action g u.
Proof. exact: mul_rV_lin1. Qed.

Lemma coordinate_action_one u : coordinate_action 1%g u = u.
Proof. by rewrite /coordinate_action right_action_one finite_coordinates_inverseK. Qed.

Lemma coordinate_action_mul a b u :
    coordinate_action (a*b)%g u = coordinate_action b (coordinate_action a u).
Proof. by rewrite /coordinate_action finite_coordinatesK right_action_mul. Qed.

Lemma coordinate_action_representation : mx_repr [set: G] coordinate_action_matrix.
Proof.
split.
- apply/row_matrixP=> i; rewrite !rowE coordinate_action_matrixE coordinate_action_one mulmx1.
  reflexivity.
- move=> a b _ _; apply/row_matrixP=> i.
  by rewrite !rowE mulmxA !coordinate_action_matrixE coordinate_action_mul.
Qed.

Definition finite_action_representation := MxRepresentation coordinate_action_representation.

Theorem finite_action_pgroup_fixed p (hp : p \in [pchar K]) (H : {group G}) :
    p.-group H -> (exists x : V, x <> 0) ->
    exists x : V, x <> 0 /\ forall g, g \in H -> right_action rho g x = x.
Proof.
move=> hH [v hv].
have hrow : finite_coordinates hV v != 0.
  apply/negP=> /eqP he; apply: hv.
  by rewrite -(finite_coordinatesK hV v) he linear0.
have hd : (0 < d)%N.
  apply: (leq_trans _ (rank_leq_col (finite_coordinates hV v))).
  by rewrite lt0n mxrank_eq0.
have hfix := @rfix_pgroup_pchar K p G hp [set: G] H d
  finite_action_representation hd hH (subsetT H).
pose u := nz_row (rfix_mx finite_action_representation H).
have hu : u != 0 by rewrite /u nz_row_eq0.
have hfixed g : g \in H -> u *m finite_action_representation g = u.
  exact: (rfix_mxP H (nz_row_sub _)).
exists (finite_coordinates_inverse hV u); split.
- move=> he; apply: (negP hu); apply/eqP.
  by rewrite -(finite_coordinates_inverseK (hV := hV) u) he linear0.
- move=> g hg; apply: (can_inj (finite_coordinatesK hV)).
  rewrite finite_coordinates_inverseK.
  exact (eq_trans (esym (coordinate_action_matrixE g u)) (hfixed g hg)).
Qed.

End FiniteAction.

Section ArbitraryFixedVector.
Variable K : fieldType.
Variable G : finGroupType.
Variable V : lmodType K.
Variable rho : right_linear_action G V.

Theorem arbitrary_action_pgroup_fixed p (hp : p \in [pchar K]) (H : {group G}) :
    p.-group H -> (exists x : V, x <> 0) ->
    exists x : V, x <> 0 /\ forall g, g \in H -> right_action rho g x = x.
Proof.
move=> hH [v hv].
pose N := action_orbit_span rho v.
pose rN := submodule_right_action (@action_orbit_span_invariant K G V rho v).
have hn : exists x : submodule_carrier N, x <> 0.
  exists (@submodule_in K V N v (@action_orbit_span_contains K G V rho v)) => hz.
  apply: hv; exact (congr1 (@submodule_val K V N) hz).
have [x [hx hfix]] := @finite_action_pgroup_fixed K G
  [the lmodType K of submodule_carrier N]
  (@action_orbit_span_finitely_generated K G V rho v) rN p hp H hH hn.
exists (submodule_val x); split.
- move=> hz; apply: hx; apply: submodule_val_injective; exact hz.
- move=> g hg; exact (congr1 (@submodule_val K V N) (hfix g hg)).
Qed.

End ArbitraryFixedVector.


