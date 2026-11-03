From mathcomp Require Import all_boot all_algebra all_fingroup generic_quotient boolp.
From DiazPark Require Import Category CategoryModules CategoryModuleLinear CategoryModuleProducts
  CategoryModuleExactness ModuleFiniteProducts HomologicalModuleIso MackeyModuleCarriers
  FusionSystems FusionOrbit FusionMackeyShape MackeyStructures MackeySubquotients
  MackeyPair MackeyFusionMinimal.
From DiazParkV29 Require Import SimpleConjugacyIndices SimpleTraceSummands
  SimpleTraceDecomposition SimpleTransportedTrace SimpleMackeyTransport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPFusionOrbit DPFusionMackey DPSimpleConjugacyIndices
  DPSimpleTraceSummands DPSimpleTraceDecomposition DPSimpleTransportedTrace
  DPSimpleMackeyTransport DiazParkHomologicalModuleIso.
Local Open Scope group_scope.
Local Open Scope ring_scope.

Module DPSimpleFunctor.
Section TheSimpleFunctor.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable R : comPzRingType.
Variable M : mackey_module R (fusion_mackey_shape F).
Hypothesis simpleM : mackey_simple M.
Variable Q : {group S}.
Hypothesis minimalQ : DPMackeyMinimal.subgroup_minimal M Q.

Definition alpha U (i : conjugacy_index F Q U) :=
  fusion_transport (representative_fusion i).

(** Every summand has carrier a submodule of M(Q), with the transported
    action alpha^{-1} gamma alpha, and is an actual relative-trace image.
    The finite product is the finite direct sum (finite_product_expansion). *)
Definition simple_value (U : {group S}) : lmodType R :=
  module_product_type (fun i : conjugacy_index F Q U =>
    @transported_trace_summand S F R M Q (representative_subgroup i) U (alpha i)).

Definition minimal_to_native U : module_hom (simple_value U) (@simple_coordinates S F R M Q U) :=
  module_product_map (fun i => iso_hom (@transported_trace_iso S F R M Q
    (representative_subgroup i) U (alpha i))).
Definition native_to_minimal U : module_hom (@simple_coordinates S F R M Q U) (simple_value U) :=
  module_product_map (fun i => iso_inv (@transported_trace_iso S F R M Q
    (representative_subgroup i) U (alpha i))).

Definition coordinate_change_iso U :
    @isomorphism (module_category R) (@simple_coordinates S F R M Q U) (simple_value U).
Proof.
refine (@Build_isomorphism (module_category R) _ _
  (native_to_minimal U) (minimal_to_native U) _ _).
- apply module_hom_ext=> v; apply functional_extensionality_dep=> i.
  change (module_hom_fun (iso_hom (@transported_trace_iso S F R M Q
    (representative_subgroup i) U (alpha i)))
    (module_hom_fun (iso_inv (@transported_trace_iso S F R M Q
    (representative_subgroup i) U (alpha i))) (v i)) = v i).
  exact: module_iso_inv_hom_apply.
- apply module_hom_ext=> v; apply functional_extensionality_dep=> i.
  change (module_hom_fun (iso_inv (@transported_trace_iso S F R M Q
    (representative_subgroup i) U (alpha i)))
    (module_hom_fun (iso_hom (@transported_trace_iso S F R M Q
    (representative_subgroup i) U (alpha i))) (v i)) = v i).
  exact: module_iso_hom_inv_apply.
Defined.

Definition simple_value_iso U : @isomorphism (module_category R) (mackey_value M U) (simple_value U) :=
  module_iso_comp (@trace_decomposition_iso S F R M simpleM Q minimalQ U) (coordinate_change_iso U).

Definition S_Q_MQ : mackey_module R (fusion_mackey_shape F) :=
  @transported_mackey R (orbit_category F) (fusion_mackey_shape F) M simple_value simple_value_iso.
Definition simple_functor_identification : mackey_isomorphism M S_Q_MQ :=
  @transported_isomorphism R (orbit_category F) (fusion_mackey_shape F) M simple_value simple_value_iso.

Theorem S_Q_MQ_simple : mackey_simple S_Q_MQ.
Proof. exact: (@transported_simple R (orbit_category F) (fusion_mackey_shape F) M
  simple_value simple_value_iso simpleM). Qed.

Theorem identification_restriction P T (f : orbit_hom F P T) (x : mackey_value M T) :
  mackey_component (mackey_iso_forward simple_functor_identification) P (mackey_pull M f x) =
  mackey_pull S_Q_MQ f (mackey_component (mackey_iso_forward simple_functor_identification) T x).
Proof. exact: mackey_hom_pull. Qed.
Theorem identification_transfer P T (f : orbit_hom F P T) (x : mackey_value M P) :
  mackey_component (mackey_iso_forward simple_functor_identification) T (mackey_push M f x) =
  mackey_push S_Q_MQ f (mackey_component (mackey_iso_forward simple_functor_identification) P x).
Proof. exact: mackey_hom_push. Qed.
Theorem identification_conjugation P T (e : @isomorphism (orbit_category F) P T)
    (x : mackey_value M P) :
  mackey_component (mackey_iso_forward simple_functor_identification) T (mackey_push M (iso_hom e) x) =
  mackey_push S_Q_MQ (iso_hom e) (mackey_component (mackey_iso_forward simple_functor_identification) P x).
Proof. exact: identification_transfer. Qed.

Lemma inverse_native_coordinates U (v : simple_value U) :
  @coordinates S F R M simpleM Q minimalQ U (module_hom_fun (iso_inv (simple_value_iso U)) v) =
  minimal_to_native U v.
Proof. exact: coordinates_from. Qed.

Theorem restriction_component_formula U (v : simple_value U) (i : conjugacy_index F Q U) :
  mackey_pull M (orbit_class (inclusion_arrow F (representative_le i)))
    (module_hom_fun (iso_inv (simple_value_iso U)) v) =
  mackey_push M (iso_hom (alpha i)) (submodule_val (v i)).
Proof.
rewrite -coordinates_at inverse_native_coordinates.
reflexivity.
Qed.

Theorem simple_functor_restriction_detection U (x : mackey_value M U) :
    (forall (L : {group S}) (hLU : L \subset U), DPFusionSystem.conjugate F Q L ->
      mackey_pull M (orbit_class (inclusion_arrow F hLU)) x = 0) -> x = 0.
Proof.
move=> hx.
have hy : module_hom_fun (iso_hom (simple_value_iso U)) x = 0.
  apply functional_extensionality_dep=> i; apply: submodule_val_injective.
  change (submodule_val (module_hom_fun (iso_hom (simple_value_iso U)) x i) = 0).
  apply: (@mackey_push_iso_injective R (orbit_category F) (fusion_mackey_shape F)
    M Q (representative_subgroup i) (alpha i)).
  rewrite linear0.
  have h := restriction_component_formula (module_hom_fun (iso_hom (simple_value_iso U)) x) i.
  rewrite module_iso_hom_inv_apply in h.
  rewrite -h; exact: hx (representative_fusion i).
apply: (@module_iso_hom_injective R (mackey_value M U) (simple_value U) (simple_value_iso U)).
by rewrite module_hom_zero.
Qed.

Theorem simple_functor_value_zero_without_conjugates (U : {group S})
    (empty : forall L : {group S}, L \subset U -> ~~ DPFusionSystem.conjugate F Q L)
    (x : mackey_value M U) : x = 0.
Proof.
apply: simple_functor_restriction_detection=> L hLU hQL.
by move: (empty L hLU); rewrite hQL.
Qed.
End TheSimpleFunctor.
End DPSimpleFunctor.
