From mathcomp Require Import all_boot all_algebra all_fingroup generic_quotient center pgroup.
From DiazPark Require Import Category CategoryModules CategoryModuleLinear CategoryModuleProducts
  ModuleFiniteProducts ModuleInfrastructure MackeyModuleCarriers
  FusionMaps FusionSystems FusionConjugacy FusionOrbit FusionMackeyShape FusionOrbitRanks
  MackeyStructures MackeyPair MackeyFusionMinimal TraceCrossTransfer.
From DiazParkV29 Require Import SimpleConjugacyIndices SimpleTraceSummands SimpleTraceDecomposition.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPFusionOrbit DPFusionMackey DPSimpleConjugacyIndices
  DPSimpleTraceSummands DPSimpleTraceDecomposition.
Local Open Scope group_scope.
Local Open Scope quotient_scope.
Local Open Scope ring_scope.

Module DPSimpleCentralizerSummands.
Section SimpleCentralizer.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable R : comPzRingType.
Variable M : mackey_module R (fusion_mackey_shape F).
Hypothesis simpleM : mackey_simple M.
Variable Q : {group S}.
Hypothesis minimalQ : DPMackeyMinimal.subgroup_minimal M Q.
Variables L U : {group S}.
Variable hLU : L \subset U.
Variable hQL : DPFusionSystem.conjugate F Q L.

Definition contained_L : contained_conjugate F Q U.
Proof. refine (Sub L _); by apply/andP; split. Defined.
Definition class_L := conjugacy_class contained_L.

Lemma pull_isomorphism_injective P T (e : @isomorphism (orbit_category F) P T) :
  injective (mackey_pull M (iso_hom e)).
Proof.
move=> x y; rewrite !mackey_pull_iso.
exact: (@mackey_push_iso_injective R (orbit_category F) (fusion_mackey_shape F)
  M T P (iso_symm e)).
Qed.

Lemma restriction_other_class (i : conjugacy_index F Q U)
    (v : trace_summand (pair_of_mackey M) (representative_subgroup i) U)
    (hi : i <> class_L) :
    mackey_pull M (orbit_class (inclusion_arrow F hLU))
      (@summand_embedding S F R M simpleM Q minimalQ U i v) = 0.
Proof.
have /exists_inP[t tU /eqP ht] := representative_related contained_L.
have hsub : L :^ t \subset representative_subgroup class_L by rewrite ht.
rewrite (@DPTraceCrossTransfer.inclusion_conjugation_factorization S F
  (representative_subgroup class_L) L U (representative_le class_L) hLU t tU hsub)
  mackey_pull_comp.
rewrite (@restriction_other_summand S F R M simpleM Q minimalQ U i class_L v hi).
exact: linear0.
Qed.

Lemma restriction_own_class_injective :
    injective (fun v : trace_summand (pair_of_mackey M) (representative_subgroup class_L) U =>
      mackey_pull M (orbit_class (inclusion_arrow F hLU))
        (@summand_embedding S F R M simpleM Q minimalQ U class_L v)).
Proof.
have /exists_inP[t tU /eqP ht] := representative_related contained_L.
have hsub : L :^ t \subset representative_subgroup class_L by rewrite ht.
pose f := orbit_class (DPTraceCrossTransfer.conjugation_arrow F hsub).
have hc : #|L| = #|representative_subgroup class_L| by rewrite -ht cardJg.
pose e := DPFusionRanks.orbit_equal_rank_iso f hc.
have he : iso_hom e = f := DPFusionRanks.orbit_equal_rank_iso_hom f hc.
move=> v w.
rewrite (@DPTraceCrossTransfer.inclusion_conjugation_factorization S F
  (representative_subgroup class_L) L U (representative_le class_L) hLU t tU hsub)
  !mackey_pull_comp !restriction_own_summand.
change (mackey_pull M f (submodule_val v) = mackey_pull M f (submodule_val w) -> v = w).
rewrite -he=> hvw; apply: submodule_val_injective.
exact (@pull_isomorphism_injective L (representative_subgroup class_L) e
  (submodule_val v) (submodule_val w) hvw).
Qed.

Variable p : nat.
Hypothesis charp : p%:R = (0 : R).
Hypothesis pU : p.-group U.
Hypothesis noncentric : ~~ (U :&: 'C(L) \subset L).

(** The class of L may have another canonical representative.  The
    preceding injective transport identifies its summand with the one
    obtained by choosing L itself.  The latter is the trace image at L,
    annihilated through L C_U(L)/L. *)
Theorem represented_trace_summand_zero
    (v : trace_summand (pair_of_mackey M) (representative_subgroup class_L) U) : v = 0.
Proof.
apply: restriction_own_class_injective.
have hz := @centralizer_trace_image_zero S F R (pair_of_mackey M) L U hLU p charp pU noncentric.
have hv := @restriction_in_trace_image S F R M simpleM Q minimalQ L U hLU hQL
  (@summand_embedding S F R M simpleM Q minimalQ U class_L v).
have h0 := @restriction_in_trace_image S F R M simpleM Q minimalQ L U hLU hQL
  (@summand_embedding S F R M simpleM Q minimalQ U class_L 0).
by rewrite (hz _ hv) (hz _ h0).
Qed.

Theorem decomposition_centralizer_restriction_zero (x : mackey_value M U) :
    mackey_pull M (orbit_class (inclusion_arrow F hLU)) x = 0.
Proof.
rewrite (@summand_expansion S F R M simpleM Q minimalQ U x) linear_sum.
apply: big1=> i _.
case hi : (i == class_L).
- move/eqP: hi=> ->.
  have hz := represented_trace_summand_zero (@coordinates S F R M simpleM Q minimalQ U x class_L).
  by rewrite hz /summand_embedding !linear0.
- apply: restriction_other_class => he; by move: hi; rewrite he eqxx.
Qed.
End SimpleCentralizer.
End DPSimpleCentralizerSummands.
