(** Native homology extensionality and two-out-of-three for actual chain maps. *)
From mathcomp Require Import all_ssreflect all_algebra.
From DiazPark Require Import MackeyModuleCarriers MackeyModuleQuotient.
From DiazParkV16b Require Import ChainComplex ChainHomology ChainHomologyMaps
  ChainDegreewiseIso ChainQuasiIsomorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPChainComplex DPChainHomology DPChainHomologyMaps
  DPChainDegreewiseIso DPChainQuasiIsomorphism.

Module DPChainQuasiIsomorphismLaws.
Section Laws.
Variable R : pzRingType.

Theorem homology_map_ext (C D : chain_complex R) (f g : chain_map C D)
  (h : forall n x, chain_map_at f n x = chain_map_at g n x) n (q : homology C n) :
  homology_map f n q = homology_map g n q.
Proof.
have [z <-] := quotient_pi_surjective q.
rewrite !homology_map_pi; congr (quotient_pi _ _).
apply submodule_val_injective; exact: h.
Qed.

Theorem quasi_isomorphism_ext (C D : chain_complex R) (f g : chain_map C D)
  (h : forall n x, chain_map_at f n x = chain_map_at g n x) :
  quasi_isomorphism f -> quasi_isomorphism g.
Proof.
move=> hf n; split.
- move=> x y hxy; apply (proj1 (hf n)).
  by rewrite (homology_map_ext h x) (homology_map_ext h y).
- move=> y; have [x hx] := proj2 (hf n) y; exists x.
  by rewrite -(homology_map_ext h x).
Qed.

Theorem quasi_isomorphism_identity (C : chain_complex R) :
  quasi_isomorphism (chain_identity C).
Proof.
move=> n; split.
- by move=> x y; rewrite !homology_map_identity.
- move=> y; exists y; exact: homology_map_identity.
Qed.

Theorem quasi_isomorphism_composition (C D E : chain_complex R)
  (f : chain_map C D) (g : chain_map D E) :
  quasi_isomorphism f -> quasi_isomorphism g -> quasi_isomorphism (chain_composition f g).
Proof.
move=> hf hg n; split.
- move=> x y hxy; apply (proj1 (hf n)); apply (proj1 (hg n)).
  by rewrite -!homology_map_composition.
- move=> z; have [y hy] := proj2 (hg n) z.
  have [x hx] := proj2 (hf n) y; exists x.
  by rewrite homology_map_composition hx hy.
Qed.

(** If the first map and the composite are quasi-isomorphisms, so is the second. *)
Theorem quasi_isomorphism_cancel_first (C D E : chain_complex R)
  (f : chain_map C D) (g : chain_map D E) :
  quasi_isomorphism f -> quasi_isomorphism (chain_composition f g) -> quasi_isomorphism g.
Proof.
move=> hf hgf n; split.
- move=> x y hxy.
  have [a ha] := proj2 (hf n) x; have [b hb] := proj2 (hf n) y.
  have hab : a = b.
    apply (proj1 (hgf n)); by rewrite !homology_map_composition ha hb.
  by rewrite -ha -hb hab.
- move=> z; have [a ha] := proj2 (hgf n) z.
  exists (homology_map f n a); by rewrite -homology_map_composition.
Qed.

(** If the second map and the composite are quasi-isomorphisms, so is the first. *)
Theorem quasi_isomorphism_cancel_second (C D E : chain_complex R)
  (f : chain_map C D) (g : chain_map D E) :
  quasi_isomorphism g -> quasi_isomorphism (chain_composition f g) -> quasi_isomorphism f.
Proof.
move=> hg hgf n; split.
- move=> x y hxy; apply (proj1 (hgf n)); by rewrite !homology_map_composition hxy.
- move=> y; have [a ha] := proj2 (hgf n) (homology_map g n y).
  exists a; apply (proj1 (hg n)); by rewrite -homology_map_composition.
Qed.

Theorem degreewise_bijective_quasi_isomorphism (C D : chain_complex R)
  (f : chain_map C D) (hi : forall n, injective (chain_map_at f n))
  (hs : forall n y, exists x, chain_map_at f n x = y) : quasi_isomorphism f.
Proof.
move=> n; split.
- move=> x y hxy; rewrite -(inverse_homology_left hi hs x)
    -(inverse_homology_left hi hs y) hxy; reflexivity.
- move=> y; exists (homology_map (inverse_chain hi hs) n y); exact: inverse_homology_right.
Qed.

Theorem quasi_isomorphism_homotopy (C D : chain_complex R)
  (f g : chain_map C D) (h : chain_homotopy f g) :
  quasi_isomorphism f -> quasi_isomorphism g.
Proof.
move=> hf n; split.
- move=> x y hxy; apply (proj1 (hf n)).
  by rewrite (homology_map_homotopy h x) (homology_map_homotopy h y).
- move=> y; have [x hx] := proj2 (hf n) y; exists x.
  by rewrite -(homology_map_homotopy h x).
Qed.
End Laws.
End DPChainQuasiIsomorphismLaws.
