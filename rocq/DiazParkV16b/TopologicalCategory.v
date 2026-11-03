From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra boolp functions.
From mathcomp Require Import topology_structure discrete_topology.
From DiazPark Require Import Category.

Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Actual MathComp topological spaces and actual continuous functions, using
    the existing ordinary-category layer. Empty spaces are allowed. *)
Module DPTopological.

Definition continuous_map {X Y : topologicalType}
    (f : X -> Y) (hf : continuous f) : continuousType X Y :=
  [the continuousType X Y of mkcts hf].

Lemma continuous_map_at {X Y : topologicalType}
    (f : X -> Y) (hf : continuous f) x : continuous_map hf x = f x.
Proof. reflexivity. Qed.

Definition continuous_identity (X : topologicalType) : continuousType X X :=
  [the continuousType X X of (@idfun X)].

Definition continuous_compose {X Y Z : topologicalType}
    (f : continuousType X Y) (g : continuousType Y Z) : continuousType X Z :=
  [the continuousType X Z of (g \o f)].

Definition topological_category : category.
Proof.
refine (@Build_category topologicalType continuousType continuous_identity
  (@continuous_compose) _ _ _).
- move=> X Y f; apply/continuousEP => x; reflexivity.
- move=> X Y f; apply/continuousEP => x; reflexivity.
- move=> W X Y Z f g h; apply/continuousEP => x; reflexivity.
Defined.

Lemma topological_identity_at (X : topologicalType) (x : X) :
  @identity topological_category X x = x.
Proof. reflexivity. Qed.

Lemma topological_compose_at {X Y Z : topologicalType}
    (f : hom topological_category X Y) (g : hom topological_category Y Z) x :
  compose f g x = g (f x).
Proof. reflexivity. Qed.

Lemma topological_hom_ext {X Y : topologicalType}
    (f g : hom topological_category X Y) :
  (forall x, f x = g x) -> f = g.
Proof. by move=> h; apply/continuousEP. Qed.

Definition homeomorphism (X Y : topologicalType) :=
  @isomorphism topological_category X Y.

Definition homeomorphism_of_inverse {X Y : topologicalType}
    (f : X -> Y) (g : Y -> X) (hf : continuous f) (hg : continuous g)
    (hfg : cancel f g) (hgf : cancel g f) : homeomorphism X Y.
Proof.
refine (@Build_isomorphism topological_category X Y
  (continuous_map hf) (continuous_map hg) _ _).
- apply/continuousEP; exact hfg.
- apply/continuousEP; exact hgf.
Defined.

Lemma homeomorphism_forwardK {X Y : topologicalType} (e : homeomorphism X Y) :
  cancel (iso_hom e) (iso_inv e).
Proof.
move=> x; exact (congr1 (fun f : hom topological_category X X => f x)
  (iso_hom_inv e)).
Qed.

Lemma homeomorphism_inverseK {X Y : topologicalType} (e : homeomorphism X Y) :
  cancel (iso_inv e) (iso_hom e).
Proof.
move=> y; exact (congr1 (fun f : hom topological_category Y Y => f y)
  (iso_inv_hom e)).
Qed.

Lemma homeomorphism_injective {X Y : topologicalType} (e : homeomorphism X Y) :
  injective (iso_hom e).
Proof. exact: (can_inj (homeomorphism_forwardK e)). Qed.

Lemma homeomorphism_surjective {X Y : topologicalType} (e : homeomorphism X Y) :
  forall y, exists x, iso_hom e x = y.
Proof. by move=> y; exists (iso_inv e y); exact: homeomorphism_inverseK. Qed.

Definition empty_space : topologicalType :=
  [the topologicalType of discrete_topology void].

Definition empty_map_fun (Y : topologicalType) (x : empty_space) : Y :=
  match x with end.

Lemma empty_map_continuous (Y : topologicalType) : continuous (empty_map_fun Y).
Proof. by case. Qed.

Definition empty_map (Y : topologicalType) : hom topological_category empty_space Y :=
  continuous_map (@empty_map_continuous Y).

Lemma empty_map_unique (Y : topologicalType)
    (f : hom topological_category empty_space Y) : f = empty_map Y.
Proof. by apply/continuousEP; case. Qed.

Definition point_space : topologicalType :=
  [the topologicalType of discrete_topology unit].

Definition point_map (X : topologicalType) : hom topological_category X point_space :=
  [the continuousType X point_space of (@cst X point_space tt)].

Lemma point_map_unique (X : topologicalType)
    (f : hom topological_category X point_space) : f = point_map X.
Proof. by apply/continuousEP => x; case: (f x). Qed.

End DPTopological.
