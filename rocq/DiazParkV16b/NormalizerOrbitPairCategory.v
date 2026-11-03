(** The actual finite category of centric acting subgroups and normalized
    centric chains, with orbit arrows admitting simultaneous extensions. *)
From mathcomp Require Import all_boot all_fingroup generic_quotient boolp.
From DiazPark Require Import Category CategoryFinite FusionMaps FusionSystems FusionOrbit.
From DiazParkV16b Require Import LinkingChainObjects NormalizerChainNormalizer
  NormalizerChainExtensions.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPFusionOrbit DPLinkingChains DPNormalizerChain DPNormalizerChainExtensions.
Local Open Scope group_scope.
Local Open Scope quotient_scope.

Module DPNormalizerOrbitPair.
Section Pair.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.

Definition object : finType := [the finType of
  {pc : centric_object F * chain F | val pc.1 \subset normalizer pc.2}].
Definition acting (A : object) : centric_object F := (val A).1.
Definition chain_of (A : object) : chain F := (val A).2.

Lemma acting_normalizes (A : object) : val (acting A) \subset normalizer (chain_of A).
Proof. exact (valP A). Qed.

Definition compatible (A B : object) (f : orbit_hom F (val (acting A)) (val (acting B))) : Prop :=
  exists g : DPFusionSystem.arrow F (val (acting A)) (val (acting B)),
    orbit_class g = f /\ inhabited (extension (chain_of A) (chain_of B) (val g)).

Definition pair_hom (A B : object) : finType := [the finType of
  {f : orbit_hom F (val (acting A)) (val (acting B)) | asbool (compatible f)}].

Lemma hom_compatible (A B : object) (f : pair_hom A B) : compatible (val f).
Proof. exact (elimT (asboolP _) (valP f)). Qed.

Definition pair_identity (A : object) : pair_hom A A.
Proof.
apply: (Sub (orbit_identity F (val (acting A)))); apply/asboolP.
exists (DPFusionSystem.arrow_identity F (val (acting A))); split; first reflexivity.
exact (inhabits (identity_extension (val (acting A)) (chain_of A))).
Defined.

Definition pair_compose (A B C : object) (f : pair_hom A B) (g : pair_hom B C) : pair_hom A C.
Proof.
apply: (Sub (orbit_compose (val f) (val g))); apply/asboolP.
have [f0 [hf [a]]] := hom_compatible f.
have [g0 [hg [b]]] := hom_compatible g.
exists (DPFusionSystem.arrow_compose f0 g0); split.
- by rewrite -hf -hg orbit_compose_class.
- exact (inhabits (compose_extension a b)).
Defined.

Lemma pair_identity_left (A B : object) (f : pair_hom A B) :
  pair_compose (pair_identity A) f = f.
Proof.
apply val_inj; exact (@Category.compose_id_left (orbit_category F)
  (val (acting A)) (val (acting B)) (val f)).
Qed.

Lemma pair_identity_right (A B : object) (f : pair_hom A B) :
  pair_compose f (pair_identity B) = f.
Proof.
apply val_inj; exact (@Category.compose_id_right (orbit_category F)
  (val (acting A)) (val (acting B)) (val f)).
Qed.

Lemma pair_associative (A B C D : object)
    (f : pair_hom A B) (g : pair_hom B C) (h : pair_hom C D) :
  pair_compose (pair_compose f g) h = pair_compose f (pair_compose g h).
Proof.
apply val_inj; exact (@Category.compose_assoc (orbit_category F)
  (val (acting A)) (val (acting B)) (val (acting C)) (val (acting D)) (val f) (val g) (val h)).
Qed.

Definition finite_pair_category : finite_category :=
  @Build_finite_category object pair_hom pair_identity pair_compose
    pair_identity_left pair_identity_right pair_associative.

Definition pair_category : category := fc_category finite_pair_category.

Definition forget : functor pair_category (centric_orbit_category F).
Proof.
refine (@Build_functor pair_category (centric_orbit_category F)
  acting (fun A B f => val f) _ _); reflexivity.
Defined.

Lemma forget_faithful (A B : object) : injective (@fmap _ _ forget A B).
Proof. exact: val_inj. Qed.

Definition hom_of_extension (A B : object)
    (f : DPFusionSystem.arrow F (val (acting A)) (val (acting B)))
    (a : extension (chain_of A) (chain_of B) (val f)) : pair_hom A B.
Proof.
apply: (Sub (orbit_class f)); apply/asboolP; exists f; split; first reflexivity.
exact: inhabits a.
Defined.

Lemma forget_hom_of_extension (A B : object)
    (f : DPFusionSystem.arrow F (val (acting A)) (val (acting B)))
    (a : extension (chain_of A) (chain_of B) (val f)) :
  fmap forget (hom_of_extension a) = orbit_class f.
Proof. reflexivity. Qed.

End Pair.
End DPNormalizerOrbitPair.
