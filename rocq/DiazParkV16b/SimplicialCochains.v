(** Actual arbitrary function cochains and their Hom-dual identification. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryModules CategoryModuleProducts CategoryModuleLinear
  BarFreeModule BarAlternating HomologicalComplex HomologicalCohomology CategoryComplexIso.
From DiazParkV16b Require Import SimplicialSet SimplicialChains ChainComplex
  ChainDualCochain LinearMapSpace FreeLinearMapSpace.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkFreeModule DiazParkBarAlternating DiazParkHomological
  DPSimplicialSet DPSimplicialChains DPLinearMapSpace DPFreeLinearMapSpace.
Local Open Scope ring_scope.

Module DPSimplicialCochains.
Section Functions.
Variable R : pzRingType.
Variable X : simplicial_set.
Variable A : lmodType R.

Definition cochain_functions n : lmodType R := module_product_type (fun _ : simplex X n => A).
Definition coface_fun n i (a : cochain_functions n) : cochain_functions n.+1 :=
  fun x => a (@indexed_face X n i x).
Lemma coface_linear n i : linear (@coface_fun n i).
Proof. move=> r a b; apply functional_extensionality_dep => x; reflexivity. Qed.
HB.instance Definition _ n i := GRing.isLinear.Build R (cochain_functions n)
  (cochain_functions n.+1) _ (@coface_fun n i) (@coface_linear n i).

Definition coface_map n i : {linear cochain_functions n -> cochain_functions n.+1} := coface_fun i.
Lemma cofaces n i j (a : cochain_functions n) :
  (i <= j)%N -> (j < n.+2)%N ->
  coface_map n.+1 i (coface_map n j a) = coface_map n.+1 j.+1 (coface_map n i a).
Proof.
move=> hij hj; apply functional_extensionality_dep => x.
change (a (@indexed_face X n j (@indexed_face X n.+1 i x)) =
  a (@indexed_face X n i (@indexed_face X n.+1 j.+1 x))).
by rewrite indexed_faces.
Qed.

Definition complex : cochain_complex R := @cosimplicial_complex R cochain_functions coface_map cofaces.

Lemma differential_at n (a : cochain_functions n) (x : simplex X n.+1) :
  cochain_d complex n a x = \sum_(i < n.+2) (-1) ^+ i *: a (@indexed_face X n i x).
Proof.
pose ev := module_hom_to_linear (module_product_projection (fun _ : simplex X n.+1 => A) x).
change (ev (\sum_(i < n.+2) (-1 : R) ^+ i *: coface_map n i a) =
  \sum_(i < n.+2) (-1) ^+ i *: a (@indexed_face X n i x)).
rewrite linear_sum; apply eq_bigr => i _; by rewrite linearZ.
Qed.
End Functions.

Section DualComparison.
Variable R : comPzRingType.
Variable X : simplicial_set.
Variable A : lmodType R.
Let dual := @DPChainDualCochain.dual_complex R A (chains R X).

Definition dual_function_iso n : @isomorphism (module_category R)
    (cochain_term dual n) (cochain_term (complex X A) n) :=
  @generators_iso R (simplex X n) A.

Lemma dual_function_differential n (a : cochain_term dual n) :
  cochain_d (complex X A) n (module_hom_fun (iso_hom (dual_function_iso n)) a) =
    module_hom_fun (iso_hom (dual_function_iso n.+1)) (cochain_d dual n a).
Proof.
apply functional_extensionality_dep => x.
rewrite differential_at.
change ((\sum_(i < n.+2) (-1 : R) ^+ i *: evaluate a (free_basis R (@indexed_face X n i x))) =
  as_linear a (@boundary R X n (free_basis R x))).
rewrite /boundary linear_sum; apply eq_bigr => i _.
by rewrite linearZ /face_map free_map_basis.
Qed.

Definition dual_function_cohomology_iso n :=
  @term_iso_cohomology_iso R dual (complex X A) dual_function_iso
    dual_function_differential n.
End DualComparison.
End DPSimplicialCochains.
