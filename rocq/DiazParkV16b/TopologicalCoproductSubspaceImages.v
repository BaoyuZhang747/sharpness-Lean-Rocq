(** Literal injectivity and open/closed image laws for coproduct subspace inclusions. *)
From mathcomp Require Import all_ssreflect all_algebra all_classical topology
  sigT_topology subtype_topology initial_topology.
From DiazPark Require Import Category.
From DiazParkV16b Require Import TopologicalCategory TopologicalCoproductHomotopy
  TopologicalCoproductSubspaces.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPTopological DPTopologicalCoproductHomotopy DPTopologicalCoproductSubspaces.
Local Open Scope classical_set_scope.

Module DPTopologicalCoproductSubspaceImages.

Lemma subtype_val_image_open {X : topologicalType} (U : set X)
    (hU : open U) (S : set [the topologicalType of set_type U]) (hS : open S) :
    open (set_val @` S : set X).
Proof.
have [V hV e] := hS.
have ee : set_val @` S = U `&` V.
  apply/seteqP; split=> x.
  - move=> [y hy <-]; split; [exact: set_valP | change ((set_val @^-1` V) y); by rewrite e].
  - move=> [hx hxV]; exists (exist _ x (mem_set hx)); last reflexivity.
    rewrite -e; exact hxV.
rewrite ee; exact: openI.
Qed.

Lemma subtype_val_image_closed {X : topologicalType} (U : set X)
    (hU : closed U) (S : set [the topologicalType of set_type U]) (hS : closed S) :
    closed (set_val @` S : set X).
Proof.
have hSc : open (~` S) by rewrite openC.
have [V hV e] := hSc.
have ee : set_val @` S = U `&` ~` V.
  apply/seteqP; split=> x.
  - move=> [y hy <-]; split; [exact: set_valP |].
    move=> hVy; have hny : (~` S) y by rewrite -e; exact hVy.
    exact: hny hy.
  - move=> [hx hxV]; exists (exist _ x (mem_set hx)); last reflexivity.
    apply: contrapT => hnS; apply hxV.
    change ((set_val @^-1` V) (exist _ x (mem_set hx))); by rewrite e.
rewrite ee; apply: closedI => //; by rewrite -openC setCK.
Qed.

Lemma homeomorphism_image_preimage {X Y : topologicalType} (e : homeomorphism X Y) (S : set X) :
    iso_hom e @` S = iso_inv e @^-1` S.
Proof.
apply/seteqP; split=> y.
- move=> [x hx <-]; change (S (iso_inv e (iso_hom e x))); by rewrite homeomorphism_forwardK.
- move=> hy; exists (iso_inv e y) => //; exact: homeomorphism_inverseK.
Qed.

Section Family.
Variable I : choiceType.
Variable X : I -> topologicalType.
Variable U : forall i, set (X i).
Arguments U i : clear implicits.

Definition family_subspace_inclusion (z : family_subspaces U) : family_space X :=
  existT X (projT1 z) (val (projT2 z)).

Lemma family_subspace_inclusion_continuous : continuous family_subspace_inclusion.
Proof.
move=> z; apply: (@continuous_comp _ (family_subspace U) (family_space X)
  (iso_hom (family_subspaces_homeomorphism U)) set_val z);
  [exact: cts_fun | exact: initial_continuous].
Qed.

Lemma family_subspace_inclusion_injective : injective family_subspace_inclusion.
Proof.
move=> x y e.
have he : iso_hom (family_subspaces_homeomorphism U) x = iso_hom (family_subspaces_homeomorphism U) y.
  apply: val_inj; exact e.
exact (@homeomorphism_injective _ _ (family_subspaces_homeomorphism U) x y he).
Qed.

Lemma family_subspace_inclusion_image (S : set (family_subspaces U)) :
  family_subspace_inclusion @` S = set_val @` (iso_hom (family_subspaces_homeomorphism U) @` S).
Proof.
rewrite image_comp; reflexivity.
Qed.

Theorem family_subspace_inclusion_open (hU : forall i, open (U i))
    (S : set (family_subspaces U)) (hS : open S) : open (family_subspace_inclusion @` S).
Proof.
rewrite family_subspace_inclusion_image; apply: subtype_val_image_open.
- exact: family_subset_open.
- rewrite homeomorphism_image_preimage; apply: open_comp => // y _; exact: cts_fun.
Qed.

Theorem family_subspace_inclusion_closed (hU : forall i, closed (U i))
    (S : set (family_subspaces U)) (hS : closed S) : closed (family_subspace_inclusion @` S).
Proof.
rewrite family_subspace_inclusion_image; apply: subtype_val_image_closed.
- exact: family_subset_closed.
- rewrite homeomorphism_image_preimage; apply: preimage_closed => // y _; exact: cts_fun.
Qed.
End Family.
End DPTopologicalCoproductSubspaceImages.
