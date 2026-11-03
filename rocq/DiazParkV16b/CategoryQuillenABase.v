(** The literal base projection of a simplicial replacement is a chain
    quasi-isomorphism when each actual fibre-to-point map is one. *)
From mathcomp Require Import all_ssreflect all_algebra boolp.
From DiazPark Require Import Category CategoryIsomorphism CategoryExtensionality BarFreeModule.
From DiazParkV16b Require Import SimplexCategoryTypes SimplexCategory SimplicialSet
  SimplicialSetYoneda SimplicialChains SimplicialChainsMaps CategoryNerve
  ChainComplex ChainQuasiIsomorphism ChainQuasiIsomorphismLaws
  BisimplicialSet BisimplicialAlexanderWhitneyNaturality
  SimplicialReplacementTypes SimplicialReplacement SimplicialReplacementMaps
  SimplicialReplacementConstants SimplicialReplacementAugmentation
  SimplicialReplacementComparisonPoly ConstantSimplicialPointChains.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkFreeModule DPSimplicialTypes DPSimplexCategory DPSimplicialSet
  DPSimplicialYoneda DPSimplicialChains DPSimplicialChainMaps DPCategoryNerve
  DPChainComplex DPChainQuasiIsomorphism DPChainQuasiIsomorphismLaws
  DPBisimplicialSet DPAlexanderWhitneyNaturality DPSimplicialReplacementTypes
  DPSimplicialReplacement DPSimplicialReplacementMaps DPSimplicialReplacementConstants
  DPSimplicialReplacementAugmentation DPSimplicialReplacementComparisonPoly DPConstantSimplicialPointChains.
Local Open Scope ring_scope.

Module DPCategoryQuillenABase.
Section Base.
Variable C : category.

Definition point_diagram : functor C simplicial_category :=
  @constant_diagram C simplicial_category point.

Definition point_base_section : simplicial_map (nerve C) (diagonal (replacement point_diagram)).
Proof.
refine (@Build_nat_trans (opposite simplex_category) type_category
  (nerve C) (diagonal (replacement point_diagram)) (fun n s => existT _ s tt) _).
move=> n m f; apply type_morphism_ext=> s; reflexivity.
Defined.

Definition point_base_iso : @isomorphism simplicial_category
  (diagonal (replacement point_diagram)) (nerve C).
Proof.
refine (@Build_isomorphism simplicial_category _ _
  (diagonal_base_projection point_diagram) point_base_section _ _).
- apply nat_trans_ext=> n; apply type_morphism_ext=> [[s u]]; by case: u.
- apply nat_trans_ext=> n; apply type_morphism_ext=> s; reflexivity.
Defined.

Variable F : functor C simplicial_category.

Definition point_cocone : nat_trans F point_diagram.
Proof.
refine (@Build_nat_trans C simplicial_category F point_diagram (fun c => to_point (fobj F c)) _).
move=> c d f; apply nat_trans_ext=> n; apply type_morphism_ext=> x; reflexivity.
Defined.

Lemma base_projection_triangle :
  nat_comp (diagonal_map (replacement_map point_cocone))
    (diagonal_base_projection point_diagram) = diagonal_base_projection F.
Proof. apply nat_trans_ext=> n; apply type_morphism_ext=> [[s u]]; reflexivity. Qed.

Variable R : pzRingType.

Lemma point_base_quasi_isomorphism :
  quasi_isomorphism (chain_map_of R (diagonal_base_projection point_diagram)).
Proof.
apply degreewise_bijective_quasi_isomorphism.
- move=> n x y hxy.
  have h z : map_at R point_base_section n
    (map_at R (diagonal_base_projection point_diagram) n z) = z.
    rewrite -map_composition.
    have he := iso_hom_inv point_base_iso.
    change (nat_comp (diagonal_base_projection point_diagram) point_base_section =
      nat_id (diagonal (replacement point_diagram))) in he.
    rewrite he; exact: map_identity.
  by rewrite -(h x) -(h y) hxy.
- move=> n y; exists (map_at R point_base_section n y).
  change (map_at R (diagonal_base_projection point_diagram) n (map_at R point_base_section n y) = y).
  rewrite -map_composition.
  have he := iso_inv_hom point_base_iso.
  change (nat_comp point_base_section (diagonal_base_projection point_diagram) = nat_id (nerve C)) in he.
  rewrite he; exact: map_identity.
Qed.

Theorem base_projection_quasi_isomorphism
  (hF : forall c, quasi_isomorphism (chain_map_of R (to_point (fobj F c)))) :
  quasi_isomorphism (chain_map_of R (diagonal_base_projection F)).
Proof.
apply (@quasi_isomorphism_ext R _ _
  (chain_composition (diagonal_chains_map R (replacement_map point_cocone))
    (chain_map_of R (diagonal_base_projection point_diagram)))
  (chain_map_of R (diagonal_base_projection F))).
- move=> n x.
  change (map_at R (diagonal_base_projection point_diagram) n
    (map_at R (diagonal_map (replacement_map point_cocone)) n x) =
    map_at R (diagonal_base_projection F) n x).
  by rewrite -map_composition base_projection_triangle.
- apply quasi_isomorphism_composition.
  + exact (@replacement_diagonal_quasi_isomorphism R C F point_diagram point_cocone hF).
  + exact: point_base_quasi_isomorphism.
Qed.
End Base.
End DPCategoryQuillenABase.
