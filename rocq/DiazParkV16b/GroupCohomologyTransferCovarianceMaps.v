(** Actual subgroup-image morphisms and a common normalized vertex map for
    transfer covariance. *)
From mathcomp Require Import all_boot all_algebra all_fingroup boolp.
From DiazParkV16b Require Import GroupCohomologyHomogeneousExtension.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPGroupCohomologyHomogeneousExtension.
Local Open Scope group_scope.

Module DPGroupCohomologyTransferCovarianceMaps.
Section Maps.
Variables G K : finGroupType.
Variables P Q : {group G}.
Hypothesis hPQ : P \subset Q.
Variable e : {morphism Q >-> K}.
Local Notation PI := (e @* P)%G.
Local Notation QI := (e @* Q)%G.

Definition image_value (H : {group G}) (hH : H \subset Q) (x : [subg H]) :
    [subg (e @* H)] :=
  Sub (e (val x)) (mem_morphim e (subsetP hH _ (valP x)) (valP x)).

Lemma image_value_val (H : {group G}) (hH : H \subset Q) (x : [subg H]) :
  val (image_value hH x) = e (val x).
Proof. reflexivity. Qed.

Definition image_hom (H : {group G}) (hH : H \subset Q) :
    {morphism [set: [subg H]] >-> [subg (e @* H)]}.
Proof.
apply: (Morphism (mfun := image_value hH))=> x y _ _.
apply val_inj; change (e (val x * val y) = e (val x) * e (val y)).
exact: morphM (subsetP hH _ (valP x)) (subsetP hH _ (valP y)).
Defined.

Definition lower_hom := image_hom hPQ.
Definition upper_hom := image_hom (subxx Q).
Definition vertex_map := subgroup_hom_vertex_extension upper_hom.

Lemma upper_hom_val (x : [subg Q]) : val (upper_hom x) = e (val x).
Proof. reflexivity. Qed.
Lemma lower_hom_val (x : [subg P]) : val (lower_hom x) = e (val x).
Proof. reflexivity. Qed.

Definition include_lower (x : [subg P]) : [subg Q] :=
  Sub (val x) (subsetP hPQ _ (valP x)).

Lemma vertex_map_upper_equivariant (x : [subg Q]) y :
  vertex_map (val x * y) = val (upper_hom x) * vertex_map y.
Proof. exact: subgroup_hom_vertex_extension_equivariant. Qed.

Lemma vertex_map_lower_equivariant (x : [subg P]) y :
  vertex_map (val x * y) = val (lower_hom x) * vertex_map y.
Proof. exact: (vertex_map_upper_equivariant (include_lower x) y). Qed.

Lemma vertex_map_upper_normalized (x : [subg Q]) :
  vertex_map (val x) = val (upper_hom x).
Proof. exact: subgroup_hom_vertex_extension_subgroup. Qed.

Lemma vertex_map_lower_normalized (x : [subg P]) :
  vertex_map (val x) = val (lower_hom x).
Proof. exact: (vertex_map_upper_normalized (include_lower x)). Qed.

Lemma vertex_map_equivariant x (hx : x \in Q) y :
  vertex_map (x * y) = e x * vertex_map y.
Proof. exact: (vertex_map_upper_equivariant (Sub x hx) y). Qed.

End Maps.
End DPGroupCohomologyTransferCovarianceMaps.
