(** Actual finite-coset transfer on the shared homogeneous Hom complexes. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_algebra all_fingroup boolp.
From DiazPark Require Import Category CategoryModules CategoryDiagramHom
  HomologicalComplex ProjectiveExtComplex.
From DiazParkV16b Require Import GroupCohomologyBase GroupCohomologyHomogeneousComplex
  GroupCohomologyHomogeneousEquivariance GroupCohomologyHomogeneousProjective
  GroupCohomologyHomogeneousResolution GroupCohomologyHomogeneousCohomology
  GroupCohomologyTransferCosets.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPGroupCohomology DiazParkHomological DPProjectiveExt
  DPGroupCohomologyHomogeneousComplex DPGroupCohomologyHomogeneousEquivariance
  DPGroupCohomologyHomogeneousProjective DPGroupCohomologyHomogeneousResolution
  DPGroupCohomologyHomogeneousCohomology DPGroupCohomologyTransferCosets.
Local Open Scope ring_scope.

Module DPGroupCohomologyTransferHomogeneous.
Section Transfer.
Variable R : comPzRingType.
Variable G : finGroupType.
Variables P Q : {group G}.
Variable A : lmodType R.
Local Notation PS := [the finGroupType of [subg P]].
Local Notation QS := [the finGroupType of [subg Q]].

Lemma ambient_functional_invariant n (f : cochain_term (@ambient_hom_complex R G P A) n)
    p : p \in P -> forall v,
  module_hom_fun (component f tt) (homogeneous_action R n p v) =
    module_hom_fun (component f tt) v.
Proof.
move=> hp v.
have hf := congr1 (fun k => module_hom_fun k v)
  (@naturality _ _ _ _ f tt tt (subg P p)).
change (module_hom_fun (component f tt)
    (homogeneous_action R n (val (subg P p)) v) =
  module_hom_fun (component f tt) v) in hf.
by rewrite subgK in hf.
Qed.

Definition transfer_function n (f : cochain_term (@ambient_hom_complex R G P A) n)
    (v : homogeneous_term R G n) : A :=
  coset_sum P Q (fun t => module_hom_fun (component f tt) (homogeneous_action R n t v)).

Lemma transfer_function_linear n (f : cochain_term (@ambient_hom_complex R G P A) n) :
  linear (@transfer_function n f).
Proof.
move=> r v w; rewrite /transfer_function /coset_sum scaler_sumr -big_split.
apply: eq_bigr => C hC; by rewrite linearP module_hom_linear.
Qed.

Lemma transfer_function_invariant n (f : cochain_term (@ambient_hom_complex R G P A) n)
    q : q \in Q -> forall v,
  transfer_function f (homogeneous_action R n q v) = transfer_function f v.
Proof.
move=> hq v.
have hinv : left_invariant P (fun t =>
    module_hom_fun (component f tt) (homogeneous_action R n t v)).
  move=> p hp t; rewrite homogeneous_action_composition.
  exact: ambient_functional_invariant.
change (coset_sum P Q (fun t => module_hom_fun (component f tt)
    (homogeneous_action R n t (homogeneous_action R n q v))) =
  coset_sum P Q (fun t => module_hom_fun (component f tt) (homogeneous_action R n t v))).
transitivity (coset_sum P Q (fun t => module_hom_fun (component f tt)
  (homogeneous_action R n (t * q)%g v))).
- apply: eq_bigr => C hC; by rewrite homogeneous_action_composition.
- exact: coset_sum_right_invariant.
Qed.

Definition ambient_transfer_term n
    (f : cochain_term (@ambient_hom_complex R G P A) n) :
    cochain_term (@ambient_hom_complex R G Q A) n.
Proof.
refine (@Build_nat_trans (opposite (group_category QS)) (module_category R)
  (homogeneous_diagram R Q n) (trivial_codiagram R QS A)
  (fun _ => exist _ (@transfer_function n f) (@transfer_function_linear n f)) _).
move=> x y a; apply module_hom_ext => v.
exact (@transfer_function_invariant n f (val a) (subgP a) v).
Defined.

Lemma ambient_transfer_term_linear n : linear (@ambient_transfer_term n).
Proof.
move=> r f g; apply diagram_hom_ext => x v.
change (coset_sum P Q (fun t => module_hom_fun (component (r *: f + g) tt)
    (homogeneous_action R n t v)) =
  r *: coset_sum P Q (fun t => module_hom_fun (component f tt) (homogeneous_action R n t v)) +
    coset_sum P Q (fun t => module_hom_fun (component g tt) (homogeneous_action R n t v))).
rewrite /coset_sum scaler_sumr -big_split.
apply: eq_bigr => C hC; reflexivity.
Qed.

HB.instance Definition _ n := GRing.isLinear.Build R
  (cochain_term (@ambient_hom_complex R G P A) n)
  (cochain_term (@ambient_hom_complex R G Q A) n) _
  (@ambient_transfer_term n) (@ambient_transfer_term_linear n).

Definition ambient_transfer :
    cochain_map (@ambient_hom_complex R G P A) (@ambient_hom_complex R G Q A).
Proof.
refine (@CochainMap R (@ambient_hom_complex R G P A) (@ambient_hom_complex R G Q A)
  (fun n => (@ambient_transfer_term n : {linear _ -> _})) _).
move=> n f; apply diagram_hom_ext => x v.
change (coset_sum P Q (fun t => module_hom_fun (component f tt)
    (homogeneous_action R n t (homogeneous_boundary R G n v))) =
  coset_sum P Q (fun t => module_hom_fun (component f tt)
    (homogeneous_boundary R G n (homogeneous_action R n.+1 t v)))).
apply: eq_bigr => C hC; by rewrite homogeneous_action_boundary.
Defined.

Lemma ambient_transfer_component n
    (f : cochain_term (@ambient_hom_complex R G P A) n) x v :
  module_hom_fun (component (cochain_map_at ambient_transfer n f) x) v =
    coset_sum P Q (fun t => module_hom_fun (component f tt) (homogeneous_action R n t v)).
Proof. reflexivity. Qed.

Lemma ambient_transfer_representatives n
    (f : cochain_term (@ambient_hom_complex R G P A) n) x v
    (s : {set G} -> G) (hs : forall C, C \in rcosets P Q -> s C \in C) :
  module_hom_fun (component (cochain_map_at ambient_transfer n f) x) v =
    \sum_(C in rcosets P Q)
      module_hom_fun (component f tt) (homogeneous_action R n (s C) v).
Proof.
rewrite ambient_transfer_component.
apply: coset_sum_representatives => // p hp t.
rewrite homogeneous_action_composition; exact: ambient_functional_invariant.
Qed.

End Transfer.
End DPGroupCohomologyTransferHomogeneous.
