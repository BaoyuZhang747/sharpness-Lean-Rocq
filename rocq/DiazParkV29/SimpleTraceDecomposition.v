From HB Require Import structures.
From mathcomp Require Import all_boot all_algebra all_fingroup generic_quotient boolp.
From DiazPark Require Import Category CategoryModules CategoryModuleLinear CategoryModuleExactness
  CategoryModuleProducts ModuleFiniteProducts HomologicalModuleIso
  ModuleInfrastructure MackeyModuleCarriers MackeyModuleMaps
  FusionMaps FusionSystems FusionConjugacy FusionOrbit FusionMackeyShape
  FusionOrbitRanks MackeyStructures MackeyPair MackeyFusionBridge MackeyFusionMinimal
  MackeyMinimal FusionMackeyFullBridge TraceCrossTransfer.
From DiazParkV16b Require Import MackeyMinimalSupportManuscript.
From DiazParkV29 Require Import SimpleTraceSummands SimpleConjugacyIndices SimpleTraceRestriction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPFusionOrbit DPFusionMackey DPSimpleTraceSummands
  DPSimpleConjugacyIndices DPSimpleTraceRestriction.
Local Open Scope group_scope.
Local Open Scope quotient_scope.
Local Open Scope ring_scope.

Module DPSimpleTraceDecomposition.
Section Decomposition.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable R : comPzRingType.
Variable M : mackey_module R (fusion_mackey_shape F).
Hypothesis simpleM : mackey_simple M.
Variable Q : {group S}.
Hypothesis minimalQ : DPMackeyMinimal.subgroup_minimal M Q.

Let leastQ := @DPMackeyMinimalManuscript.minimal_is_least S F R M simpleM Q minimalQ.
Let full_formula := @DPFusionMackeyFullBridge.full_inclusion_mackey S F R M.
Let paired := pair_of_mackey M.

Lemma conjugate_smaller_zero L (hQL : DPFusionSystem.conjugate F Q L) :
  forall A : {group S}, (#|A| < #|L|)%N -> forall x : mackey_value M A, x = 0.
Proof.
move=> A hA x; apply: leastQ.2.
by rewrite (DPFusionConjugacy.conjugate_card hQL).
Qed.

Lemma restriction_in_trace_image (L U : {group S}) (hLU : L \subset U)
    (hQL : DPFusionSystem.conjugate F Q L) (x : mackey_value M U) :
    trace_image paired L U (mackey_pull M (orbit_class (inclusion_arrow F hLU)) x).
Proof.
apply: (@span_least R (mackey_value M U)
  (@DPMackeyMinimal.inclusion_transfer_generator S F R M Q U)
  (linear_preimage (mackey_pull M (orbit_class (inclusion_arrow F hLU)))
     (trace_image paired L U))) _
  (@DPMackeyMinimal.inclusion_transfer_generation S F R M Q leastQ simpleM U x).
move=> y [K [hKU [hQK [v <-]]]].
have hc : #|K| = #|L|.
  by rewrite -(DPFusionConjugacy.conjugate_card hQK)
    (DPFusionConjugacy.conjugate_card hQL).
exact: (@cross_restriction_in_trace_image S F R paired full_formula L K U hLU hKU
  (conjugate_smaller_zero hQL) hc v).
Qed.

Definition simple_coordinates (U : {group S}) : lmodType R :=
  module_product_type (fun i : conjugacy_index F Q U =>
    trace_summand paired (representative_subgroup i) U).

Definition coordinates (U : {group S}) (x : mackey_value M U) : simple_coordinates U :=
  fun i => submodule_in (restriction_in_trace_image (representative_le i)
    (representative_fusion i) x).

Lemma coordinates_at U (x : mackey_value M U) i :
  submodule_val (coordinates x i) =
  mackey_pull M (orbit_class (inclusion_arrow F (representative_le i))) x.
Proof. reflexivity. Qed.

Lemma coordinates_linear U : linear (@coordinates U).
Proof.
move=> a x y; apply functional_extensionality_dep=> i.
apply: submodule_val_injective.
change (mackey_pull M (orbit_class (inclusion_arrow F (representative_le i))) (a *: x + y) =
  a *: mackey_pull M (orbit_class (inclusion_arrow F (representative_le i))) x +
  mackey_pull M (orbit_class (inclusion_arrow F (representative_le i))) y).
exact: linearP.
Qed.
HB.instance Definition _ U := GRing.isLinear.Build R (mackey_value M U)
  (simple_coordinates U) _ (@coordinates U) (@coordinates_linear U).

(** Injectivity is established from the proper kernel subfunctor and
    simplicity.  The old restriction-detection theorem is not invoked.
    Its lower-level kernel-stability proof is shared explicitly. *)
Lemma coordinates_kernel U (x : mackey_value M U) : coordinates x = 0 -> x = 0.
Proof.
move=> hx.
have hz : forall (L : {group S}) (hLU : L \subset U),
    DPFusionSystem.conjugate F Q L ->
    mackey_pull M (orbit_class (inclusion_arrow F hLU)) x = 0.
  move=> L hLU hQL.
  have hL : (L \subset U) && DPFusionSystem.conjugate F Q L by apply/andP; split.
  pose a : contained_conjugate F Q U := Sub L hL.
  have /exists_inP[t tU /eqP ht] := representative_related a.
  have hs : L :^ t \subset representative_subgroup (conjugacy_class a) by rewrite ht.
  rewrite (@DPTraceCrossTransfer.inclusion_conjugation_factorization S F
    (representative_subgroup (conjugacy_class a)) L U
    (representative_le (conjugacy_class a)) hLU t tU hs) mackey_pull_comp.
  have hi := congr1 (fun v : simple_coordinates U => submodule_val (v (conjugacy_class a))) hx.
  change (mackey_pull M (orbit_class (inclusion_arrow F
    (representative_le (conjugacy_class a)))) x = 0) in hi.
  by rewrite hi linear0.
have hker : @detection_value R (orbit_category F) (fusion_mackey_shape F) M Q U x.
  move=> f.
  have hf : orbit_class (repr f) = f := reprK f.
  rewrite -hf -DPFusionMackey.orbit_image_factorization mackey_pull_comp.
  rewrite (hz _ _ (@DPMackeyMinimal.orbit_image_conjugate S F Q U f)).
  exact: linear0.
have [_ hs] := simpleM.
case: (hs (@detection_subfunctor R (orbit_category F) (fusion_mackey_shape F) M
  (fun P : {group S} => #|P|) (@DPFusionRanks.orbit_rank_le S F)
  (@DPMackeyMinimal.equal_rank_iso_exists S F) Q leastQ)) => h.
- exact: h hker.
- have [v hv] := leastQ.1; have he := h Q v (@identity (orbit_category F) Q).
  rewrite mackey_pull_id in he; exact: False_ind _ (hv he).
Qed.

Lemma coordinates_injective U : injective (@coordinates U).
Proof.
move=> x y h; apply/eqP; rewrite -subr_eq0; apply/eqP.
apply: coordinates_kernel; by rewrite linearB /= h subrr.
Qed.

Definition trace_lift U (v : simple_coordinates U) (i : conjugacy_index F Q U) :=
  proj1_sig (constructive_indefinite_description (trace_image_mem (v i))).
Lemma trace_lift_spec U (v : simple_coordinates U) i :
  @normalizer_trace S F R paired (representative_subgroup i) U (trace_lift v i) = submodule_val (v i).
Proof. exact: (proj2_sig (constructive_indefinite_description (trace_image_mem (v i)))). Qed.

Definition assemble U (v : simple_coordinates U) : mackey_value M U :=
  \sum_(i : conjugacy_index F Q U)
    mackey_push M (orbit_class (inclusion_arrow F (representative_le i))) (trace_lift v i).

Lemma coordinates_assemble U (v : simple_coordinates U) : coordinates (assemble v) = v.
Proof.
apply functional_extensionality_dep=> i; apply: submodule_val_injective.
rewrite coordinates_at /assemble linear_sum (bigD1 i) //=.
have hself := @self_restriction_is_trace S F R paired
  (representative_subgroup i) U (representative_le i)
  (conjugate_smaller_zero (representative_fusion i)) full_formula (trace_lift v i).
change (mackey_pull M (orbit_class (inclusion_arrow F (representative_le i)))
  (mackey_push M (orbit_class (inclusion_arrow F (representative_le i))) (trace_lift v i)) =
  @normalizer_trace S F R paired (representative_subgroup i) U (trace_lift v i)) in hself.
rewrite hself trace_lift_spec big1 ?addr0 // => j hji.
have hc : #|representative_subgroup j| = #|representative_subgroup i|.
  by rewrite -(DPFusionConjugacy.conjugate_card (representative_fusion j))
    (DPFusionConjugacy.conjugate_card (representative_fusion i)).
exact: (@nonconjugate_cross_restriction S F R paired full_formula
  (representative_subgroup i) (representative_subgroup j) U
  (representative_le i) (representative_le j)
  (conjugate_smaller_zero (representative_fusion i)) hc
  (representatives_distinct hji) (trace_lift v j)).
Qed.

Theorem coordinates_surjective U : forall v : simple_coordinates U, exists x, coordinates x = v.
Proof. move=> v; exists (assemble v); exact: coordinates_assemble. Qed.

Definition trace_decomposition_iso U :
  @isomorphism (module_category R) (mackey_value M U) (simple_coordinates U) :=
  DiazParkHomologicalModuleIso.linear_bijection_iso
    (@coordinates_injective U) (@coordinates_surjective U).

Definition from_coordinates U : {linear simple_coordinates U -> mackey_value M U} :=
  module_hom_to_linear (iso_inv (trace_decomposition_iso U)).
Arguments from_coordinates {U}.
Lemma coordinates_from U (v : simple_coordinates U) : coordinates (from_coordinates v) = v.
Proof. exact: (module_iso_inv_hom_apply (trace_decomposition_iso U)). Qed.
Lemma from_coordinates_to U (x : mackey_value M U) : from_coordinates (coordinates x) = x.
Proof. exact: (module_iso_hom_inv_apply (trace_decomposition_iso U)). Qed.

Definition summand_embedding U (i : conjugacy_index F Q U)
    (v : trace_summand paired (representative_subgroup i) U) : mackey_value M U :=
  from_coordinates (@finite_product_single R [the finType of conjugacy_index F Q U]
    (fun j => trace_summand paired (representative_subgroup j) U) i v).

Theorem restriction_own_summand U (i : conjugacy_index F Q U)
    (v : trace_summand paired (representative_subgroup i) U) :
    mackey_pull M (orbit_class (inclusion_arrow F (representative_le i)))
      (summand_embedding v) = submodule_val v.
Proof.
rewrite -coordinates_at /summand_embedding coordinates_from finite_product_single_same.
reflexivity.
Qed.

Theorem restriction_other_summand U (i j : conjugacy_index F Q U)
    (v : trace_summand paired (representative_subgroup i) U) (hij : i <> j) :
    mackey_pull M (orbit_class (inclusion_arrow F (representative_le j)))
      (summand_embedding v) = 0.
Proof.
rewrite -coordinates_at /summand_embedding coordinates_from
  (@finite_product_single_away R [the finType of conjugacy_index F Q U]
    (fun k => trace_summand paired (representative_subgroup k) U) i v j hij).
reflexivity.
Qed.

Theorem restriction_own_summand_injective U (i : conjugacy_index F Q U) :
    injective (fun v : trace_summand paired (representative_subgroup i) U =>
      mackey_pull M (orbit_class (inclusion_arrow F (representative_le i))) (summand_embedding v)).
Proof.
move=> v w; rewrite !restriction_own_summand; exact: submodule_val_injective.
Qed.

Lemma summand_expansion U (x : mackey_value M U) :
    x = \sum_(i : conjugacy_index F Q U) summand_embedding (coordinates x i).
Proof.
rewrite -[LHS](from_coordinates_to x) [in LHS](finite_product_expansion (coordinates x)) linear_sum.
reflexivity.
Qed.

Theorem decomposition_restriction_detection U (x : mackey_value M U) :
  (forall (L : {group S}) (hLU : L \subset U), DPFusionSystem.conjugate F Q L ->
    mackey_pull M (orbit_class (inclusion_arrow F hLU)) x = 0) -> x = 0.
Proof.
move=> hx; apply: (@module_iso_hom_injective R _ _ (trace_decomposition_iso U)).
change (coordinates x = coordinates (0 : mackey_value M U)); rewrite linear0.
apply functional_extensionality_dep=> i; apply: submodule_val_injective.
change (mackey_pull M (orbit_class (inclusion_arrow F (representative_le i))) x = 0).
exact: hx (representative_fusion i).
Qed.
End Decomposition.
End DPSimpleTraceDecomposition.
