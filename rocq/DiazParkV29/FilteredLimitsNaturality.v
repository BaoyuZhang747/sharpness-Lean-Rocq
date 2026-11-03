(** Naturality of the canonical higher-limit/direct-limit isomorphism in
    the full coefficient diagram, not just an objectwise isomorphism. *)
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryExtensionality CategoryFinite
  CategoryModules CategoryModuleLinear CategoryLimits CategoryColimitMaps
  CategoryDerivedLimits ModuleInfrastructure MackeyModuleCarriers MackeyModuleQuotient.
From DiazPark Require Import CategoryEnoughInjectives CategoryInjectiveResolutionComparison.
From DiazParkV29 Require Import FilteredLimitsDirected FilteredLimitsMaps
  FilteredLimitsDiagrams FilteredLimitsDerived.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPFilteredLimits DPFilteredMaps DPFilteredDiagrams DPFilteredDerived.
Local Open Scope ring_scope.
(* Preserve the abstract, already proved resolution interface during conversion. *)
Local Opaque chosen_injective_resolution injective_resolution_comparison
  module_quotient linear_preimage linear_kernel linear_image.

Module DPFilteredNaturality.
Section Natural.
Variable R : pzRingType.
Variable I : directed_poset.
Variable C : finite_category.
Variables F G : functor (stage_category I)
  (functor_category (opposite (fc_category C)) (module_category R)).
Variable a : nat_trans F G.

Definition coefficient_colimit_map : nat_trans (pointwise_colimit F) (pointwise_colimit G) :=
  colimit_map (diagram_colimit F) (diagram_colimit G) a.

Lemma coefficient_colimit_map_leg i :
    nat_comp (pointwise_leg F i) coefficient_colimit_map =
      nat_comp (component a i) (pointwise_leg G i).
Proof. exact (colimit_map_fac (diagram_colimit F) (diagram_colimit G) a i). Qed.

Definition higher_limit_family n i :
    {linear dm_value (derived_system F n) i -> dm_value (derived_system G n) i} :=
  module_hom_to_linear (derived_limit_map R (component a i) n).

Lemma higher_limit_family_natural n i j (h : stage_le i j) q :
    higher_limit_family n j (dm_map (derived_system F n) h q) =
      dm_map (derived_system G n) h (higher_limit_family n i q).
Proof.
have he := congr1 (fun b : nat_trans (fobj F i) (fobj G j) =>
  fmap (derived_limit_functor R (opposite (fc_category C)) n) b) (naturality a h).
rewrite !fmap_compose in he.
exact (congr1 (fun b : module_hom (derived_limit R (fobj F i) n)
  (derived_limit R (fobj G j) n) => module_hom_fun b q) he).
Qed.

Definition higher_limit_colimit_map n : module_hom
    (colimit_module (derived_system F n)) (colimit_module (derived_system G n)) :=
  exist _ (direct_limit_map (higher_limit_family n))
    (@direct_limit_map_linear R I _ _ (higher_limit_family n) (@higher_limit_family_natural n)).

Lemma higher_limit_colimit_map_in n i q :
    higher_limit_colimit_map n (colimit_in (V := derived_system F n) (i := i) q) =
    colimit_in (V := derived_system G n) (i := i) (higher_limit_family n i q).
Proof.
exact (@direct_limit_map_in R I _ _ (higher_limit_family n) (@higher_limit_family_natural n) i q).
Qed.

Local Opaque higher_limit_colimit_iso higher_limit_colimit_map.

Theorem higher_limit_colimit_natural n (q : colimit_module (derived_system F n)) :
    module_hom_fun (derived_limit_map R coefficient_colimit_map n)
      (module_hom_fun (iso_hom (higher_limit_colimit_iso F n)) q) =
    module_hom_fun (iso_hom (higher_limit_colimit_iso G n)) (higher_limit_colimit_map n q).
Proof.
have [i [v <-]] := colimit_in_surjective q.
have he := congr1 (fun b : nat_trans (fobj F i) (pointwise_colimit G) =>
  fmap (derived_limit_functor R (opposite (fc_category C)) n) b) (coefficient_colimit_map_leg i).
rewrite !fmap_compose in he.
have hmid := congr1 (fun b : module_hom (derived_limit R (fobj F i) n)
  (derived_limit R (pointwise_colimit G) n) => module_hom_fun b v) he.
have hleft := congr1 (module_hom_fun (derived_limit_map R coefficient_colimit_map n))
  (@higher_limit_colimit_iso_in R I C F n i v).
have hright := eq_trans
  (congr1 (module_hom_fun (iso_hom (higher_limit_colimit_iso G n)))
    (@higher_limit_colimit_map_in n i v))
  (@higher_limit_colimit_iso_in R I C G n i (higher_limit_family n i v)).
exact (eq_trans hleft (eq_trans hmid (esym hright))).
Qed.

End Natural.

Section Vanishing.
Variable R : pzRingType.
Variable I : directed_poset.
Variable C : finite_category.
Variable F : functor (stage_category I)
  (functor_category (opposite (fc_category C)) (module_category R)).

Theorem higher_limit_colimit_zero n
    (h : forall i (q : derived_limit R (fobj F i) n), q = 0) :
    forall q : derived_limit R (pointwise_colimit F) n, q = 0.
Proof.
move=> q.
pose e := higher_limit_colimit_iso F n.
pose u := module_hom_fun (iso_inv e) q.
have [i [v hv]] := colimit_in_surjective u.
have hz : u = 0.
  rewrite -hv (h i v); exact: linear0.
have he := congr1 (fun b : module_hom (derived_limit R (pointwise_colimit F) n)
  (derived_limit R (pointwise_colimit F) n) => module_hom_fun b q) (iso_inv_hom e).
change (module_hom_fun (iso_hom e) u = q) in he.
rewrite hz module_hom_zero in he; exact: esym he.
Qed.
End Vanishing.
End DPFilteredNaturality.
