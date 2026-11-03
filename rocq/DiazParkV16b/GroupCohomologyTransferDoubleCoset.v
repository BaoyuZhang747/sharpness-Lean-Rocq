(** The actual Mackey double-coset identity, first on the shared invariant
    cochains and then on the displayed native ordinary group cohomology. *)
From mathcomp Require Import all_boot all_algebra all_fingroup boolp.
From DiazPark Require Import Category CategoryModules CategoryModuleExactness
  CategoryDiagramHom HomologicalComplex HomologicalCohomology HomologicalCohomologyMaps
  MackeyModuleCarriers MackeyModuleQuotient.
From DiazParkV16b Require Import GroupCohomologyBase GroupCohomologyPullback
  GroupCohomologyHomogeneousComplex GroupCohomologyHomogeneousEquivariance
  GroupCohomologyHomogeneousCohomology GroupCohomologyHomogeneousRestriction
  GroupCohomologyHomogeneousConjugation GroupCohomologyTransferCosets
  GroupCohomologyTransferHomogeneous GroupCohomologyTransferNative
  GroupCohomologyCosetSumsDoubleCosets.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPGroupCohomology DPGroupCohomologyPullback
  DiazParkHomological DiazParkCohomology DiazParkCohomologyMaps
  DPGroupCohomologyHomogeneousComplex DPGroupCohomologyHomogeneousEquivariance
  DPGroupCohomologyHomogeneousCohomology DPGroupCohomologyHomogeneousRestriction
  DPGroupCohomologyHomogeneousConjugation DPGroupCohomologyTransferCosets
  DPGroupCohomologyTransferHomogeneous DPGroupCohomologyTransferNative
  DPGroupCohomologyCosetSumsDoubleCosets.
Local Open Scope ring_scope.

Module DPGroupCohomologyTransferDoubleCoset.

Lemma module_hom_sum (R : pzRingType) (U V : lmodType R) (f : module_hom U V)
    (I : Type) (r : seq I) (p : pred I) (a : I -> U) :
  module_hom_fun f (\sum_(i <- r | p i) a i) =
    \sum_(i <- r | p i) module_hom_fun f (a i).
Proof.
elim: r => [|i r IH]; first by rewrite !big_nil module_hom_zero.
rewrite !big_cons; case: (p i); last exact IH.
by rewrite module_hom_add IH.
Qed.

Lemma diagram_hom_at_sum (R : comPzRingType) (C : category)
    (B D : module_diagram R C) (I : Type) (r : seq I) (p : pred I)
    (a : I -> diagram_hom_type B D) x v :
  diagram_hom_at (\sum_(i <- r | p i) a i) x v =
    \sum_(i <- r | p i) diagram_hom_at (a i) x v.
Proof.
elim: r => [|i r IH]; first by rewrite !big_nil diagram_hom_at_zero.
rewrite !big_cons; case: (p i); last exact IH.
by rewrite diagram_hom_at_add IH.
Qed.

Section DoubleCoset.
Variable R : comPzRingType.
Variable G : finGroupType.
Variables P Q T : {group G}.
Variables (hPT : P \subset T) (hQT : Q \subset T).
Variable A : lmodType R.

Definition intersection (x : G) : {group G} := [group of Q :&: (P :^ x)%g].
Lemma intersection_sub_Q x : intersection x \subset Q.
Proof. exact: subsetIl. Qed.
Lemma intersection_sub_conjugate x : intersection x \subset (P :^ x)%g.
Proof. exact: subsetIr. Qed.

Definition ambient_double_coset_term (D : {set {set G}}) :=
  @ambient_left_conjugation G (intersection (double_coset_repr P D)) P
    (double_coset_repr P D) (intersection_sub_conjugate _) R A.

Theorem ambient_transfer_double_coset n
    (f : cochain_term (@ambient_hom_complex R G P A) n) :
  cochain_map_at (@ambient_restriction R G Q T hQT A) n
    (cochain_map_at (@ambient_transfer R G P T A) n f) =
  \sum_(D in double_cosets P Q T)
    cochain_map_at (@ambient_transfer R G (intersection (double_coset_repr P D)) Q A) n
      (cochain_map_at (ambient_double_coset_term D) n f).
Proof.
apply diagram_hom_ext => a v; case: a v => v.
rewrite diagram_hom_at_sum.
change (coset_sum P T (fun t => module_hom_fun (component f tt)
    (homogeneous_action R n t v)) =
  \sum_(D in double_cosets P Q T)
    diagram_hom_at (cochain_map_at
      (@ambient_transfer R G (intersection (double_coset_repr P D)) Q A) n
      (cochain_map_at (ambient_double_coset_term D) n f)) tt v).
have hinv : left_invariant P (fun t => module_hom_fun (component f tt)
    (homogeneous_action R n t v)).
  move=> p hp t; rewrite homogeneous_action_composition.
  exact: ambient_functional_invariant.
rewrite (@coset_sum_double_coset G P Q T hQT _ _ hinv).
apply: eq_bigr => D hD.
change (coset_sum (intersection (double_coset_repr P D)) Q
    (fun q => module_hom_fun (component f tt)
      (homogeneous_action R n (double_coset_repr P D * q)%g v)) =
  coset_sum (intersection (double_coset_repr P D)) Q
    (fun q => module_hom_fun
      (component (cochain_map_at (ambient_double_coset_term D) n f) tt)
      (homogeneous_action R n q v))).
apply: eq_bigr => C hC.
rewrite ambient_left_conjugation_component homogeneous_action_composition; reflexivity.
Qed.

Theorem ambient_transfer_double_coset_cohomology n
    (q : cohomology (@ambient_hom_complex R G P A) n) :
  cohomology_map (@ambient_restriction R G Q T hQT A) n
    (cohomology_map (@ambient_transfer R G P T A) n q) =
  \sum_(D in double_cosets P Q T)
    cohomology_map (@ambient_transfer R G (intersection (double_coset_repr P D)) Q A) n
      (cohomology_map (ambient_double_coset_term D) n q).
Proof.
have [z <-] := quotient_pi_surjective q.
rewrite !cohomology_map_pi.
transitivity (\sum_(D in double_cosets P Q T)
  quotient_pi (boundaries_in_cycles (@ambient_hom_complex R G Q A) n) (cycle_map (@ambient_transfer R G (intersection (double_coset_repr P D)) Q A) n
    (cycle_map (ambient_double_coset_term D) n z))).
- rewrite -linear_sum; congr (quotient_pi _ _).
  apply submodule_val_injective.
  change (cochain_map_at (@ambient_restriction R G Q T hQT A) n
    (cochain_map_at (@ambient_transfer R G P T A) n (submodule_val z)) =
    val (\sum_(D in double_cosets P Q T)
      cycle_map (@ambient_transfer R G (intersection (double_coset_repr P D)) Q A) n
        (cycle_map (ambient_double_coset_term D) n z))).
  rewrite linear_sum; exact: ambient_transfer_double_coset.
- apply: eq_bigr => D hD; by rewrite !cohomology_map_pi.
Qed.

Definition native_double_coset_term n (D : {set {set G}}) :=
  module_hom_comp
    (pull A (@subgroup_conjugation_hom G (intersection (double_coset_repr P D)) P
      (double_coset_repr P D) (intersection_sub_conjugate _)) n)
    (transfer A (intersection_sub_Q (double_coset_repr P D)) n).

Theorem transfer_double_coset n (q : value R [the finGroupType of [subg P]] A n) :
  module_hom_fun (pull A (subgroup_nested_hom hQT) n)
    (module_hom_fun (transfer A hPT n) q) =
    \sum_(D in double_cosets P Q T) module_hom_fun (native_double_coset_term n D) q.
Proof.
pose eP := @ambient_native_iso R G P A n.
pose eQ := @ambient_native_iso R G Q A n.
pose eT := @ambient_native_iso R G T A n.
pose a := module_hom_fun (iso_inv eP) q.
have hq : module_hom_fun (iso_hom eP) a = q := module_iso_inv_hom_apply eP q.
rewrite -hq.
have ht := congr1 (fun k => module_hom_fun k a) (@transfer_ambient_square R G A P T hPT n).
change (module_hom_fun (transfer A hPT n) (module_hom_fun (iso_hom eP) a) =
  module_hom_fun (iso_hom eT) (cohomology_map (@ambient_transfer R G P T A) n a)) in ht.
rewrite ht.
have hr := congr1 (fun k => module_hom_fun k
    (cohomology_map (@ambient_transfer R G P T A) n a))
  (@ambient_restriction_native_cohomology_square R G Q T hQT A n).
change (module_hom_fun (iso_hom eQ)
    (cohomology_map (@ambient_restriction R G Q T hQT A) n
      (cohomology_map (@ambient_transfer R G P T A) n a)) =
  module_hom_fun (pull A (subgroup_nested_hom hQT) n)
    (module_hom_fun (iso_hom eT) (cohomology_map (@ambient_transfer R G P T A) n a))) in hr.
rewrite -hr ambient_transfer_double_coset_cohomology module_hom_sum.
apply: eq_bigr => D hD.
pose x := double_coset_repr P D.
pose eL := @ambient_native_iso R G (intersection x) A n.
have hc := congr1 (fun k => module_hom_fun k a)
  (@ambient_left_conjugation_native_square G (intersection x) P x
    (intersection_sub_conjugate x) R A n).
change (module_hom_fun (iso_hom eL) (cohomology_map (ambient_double_coset_term D) n a) =
  module_hom_fun (pull A (@subgroup_conjugation_hom G (intersection x) P x
    (intersection_sub_conjugate x)) n) (module_hom_fun (iso_hom eP) a)) in hc.
change (module_hom_fun (iso_hom eQ)
    (cohomology_map (@ambient_transfer R G (intersection x) Q A) n
      (cohomology_map (ambient_double_coset_term D) n a)) =
  module_hom_fun (transfer A (intersection_sub_Q x) n)
    (module_hom_fun (pull A (@subgroup_conjugation_hom G (intersection x) P x
      (intersection_sub_conjugate x)) n) (module_hom_fun (iso_hom eP) a))).
rewrite -hc.
symmetry; exact (congr1 (fun k => module_hom_fun k
  (cohomology_map (ambient_double_coset_term D) n a))
  (@transfer_ambient_square R G A (intersection x) Q (intersection_sub_Q x) n)).
Qed.

End DoubleCoset.
End DPGroupCohomologyTransferDoubleCoset.

