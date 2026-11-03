(** Actual parameterized descent through the attaching quotient via compact-open paths. *)
From mathcomp Require Import all_ssreflect all_algebra all_classical topology
  function_spaces sigT_topology quotient_topology.
From DiazPark Require Import Category.
From DiazParkV16b Require Import TopologicalCategory TopologicalPushoutCarrier TopologicalPushoutUniversal.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPTopological DPTopologicalPushoutCarrier DPTopologicalPushoutUniversal.
Import ArrowAsCompactOpen.
Local Open Scope classical_set_scope.

Module DPTopologicalParametrizedPushout.
Section Descent.
Variables A B X V Y : topologicalType.
Variables (i : hom topological_category A B) (j : hom topological_category A X).
Variables (f : continuousType (B * V)%type Y) (g : continuousType (X * V)%type Y).
Variable w : forall a t, f (i a, t) = g (j a, t).

Definition parametrized_left : continuousType B [the topologicalType of (V -> Y)] :=
  continuous_map (continuous_curry_fun (@cts_fun _ _ f)).
Definition parametrized_right : continuousType X [the topologicalType of (V -> Y)] :=
  continuous_map (continuous_curry_fun (@cts_fun _ _ g)).

Lemma parametrized_commutes : compose i parametrized_left = compose j parametrized_right.
Proof. apply topological_hom_ext => a; apply funext => t; exact: w. Qed.

Definition parametrized_curried : continuousType (attaching_space i j) [the topologicalType of (V -> Y)] :=
  attaching_desc_map parametrized_commutes.

Lemma parametrized_curried_left b t : parametrized_curried (attaching_left i j b) t = f (b,t).
Proof.
have e := attaching_desc_left parametrized_commutes.
exact (congr1 (fun h : hom topological_category B [the topologicalType of (V -> Y)] => h b t) e).
Qed.

Lemma parametrized_curried_right x t : parametrized_curried (attaching_right i j x) t = g (x,t).
Proof.
have e := attaching_desc_right parametrized_commutes.
exact (congr1 (fun h : hom topological_category X [the topologicalType of (V -> Y)] => h x t) e).
Qed.

Lemma parametrized_curried_slice z : continuous (parametrized_curried z).
Proof.
case: (attaching_cases z) => [[b <-]|[x <-]].
- have e : parametrized_curried (attaching_left i j b) = curry f b.
    apply funext => t; exact: parametrized_curried_left.
  rewrite e; exact: (proj2 (continuous_curry (@cts_fun _ _ f)) b).
- have e : parametrized_curried (attaching_right i j x) = curry g x.
    apply funext => t; exact: parametrized_curried_right.
  rewrite e; exact: (proj2 (continuous_curry (@cts_fun _ _ g)) x).
Qed.

Variable lcV : locally_compact [set: V].
Variable hV : hausdorff_space V.

Lemma parametrized_desc_continuous : continuous (uncurry parametrized_curried).
Proof.
apply: continuous_uncurry => //.
- exact: cts_fun.
- exact: parametrized_curried_slice.
Qed.

Definition parametrized_desc : continuousType (attaching_space i j * V)%type Y :=
  continuous_map parametrized_desc_continuous.

Theorem parametrized_desc_left b t : parametrized_desc (attaching_left i j b,t) = f (b,t).
Proof. exact: parametrized_curried_left. Qed.

Theorem parametrized_desc_right x t : parametrized_desc (attaching_right i j x,t) = g (x,t).
Proof. exact: parametrized_curried_right. Qed.

End Descent.
End DPTopologicalParametrizedPushout.
