(** The actual singular simplices supplied by a continuous homotopy. *)
From mathcomp Require Import all_ssreflect all_algebra all_classical.
From mathcomp Require Import reals topology normedtype matrix_normedtype subtype_topology.
From DiazPark Require Import Category.
From DiazParkV16b Require Import SimplexCategory SimplexCategoryOperators SimplexCategoryIdentities
  SimplicialSet SimplicialSetOperators SingularSet TopologicalCategory
  TopologicalCategoryHomotopy TopologicalSimplexBasic TopologicalSimplexAffine
  SingularHomotopyPrismGeometry.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPTopological DPTopologicalHomotopy DPTopologicalSimplex
  DPTopologicalSimplexAffine DPSimplexCategory DPSimplexOperators DPSimplexIdentities
  DPSimplicialOperators DPSingularSet DPSingularPrismGeometry.

Module DPSingularPrism.
Section Prism.
Variable Real : realType.
Variables X Y : topologicalType.
Variables f g : hom topological_category X Y.
Variable H : continuous_homotopy Real f g.

Definition interval_product_map n (s : continuousType (simplex_space Real n) X) :
    continuousType (unit_interval_space Real * simplex_space Real n)%type
      (unit_interval_space Real * X)%type.
Proof.
apply (@continuous_map _ _ (fun p => (p.1, s p.2))).
move=> p.
apply: (@cvg_pair
  [the topologicalType of (unit_interval_space Real * simplex_space Real n)%type]
  (unit_interval_space Real) X (nbhs p) (nbhs p.1) (nbhs (s p.2))
  (@nbhs_filter [the topologicalType of
    (unit_interval_space Real * simplex_space Real n)%type] p)
  (@nbhs_filter (unit_interval_space Real) p.1) (@nbhs_filter X (s p.2))).
- exact: cvg_fst.
- apply: (@continuous_comp _ (simplex_space Real n) X snd s p);
    [exact: cvg_snd | exact: cts_fun].
Defined.

Definition singular_prism n (i : 'I_n.+1)
    (s : DPSimplicialSet.simplex (singular_set Real X) n) :
    DPSimplicialSet.simplex (singular_set Real Y) n.+1 :=
  continuous_compose (prism_parameter_map Real i)
    (continuous_compose (interval_product_map s) (homotopy_map H)).

Lemma singular_prism_at n (i : 'I_n.+1)
    (s : DPSimplicialSet.simplex (singular_set Real X) n) x :
  singular_prism i s x =
    homotopy_map H (prism_time (Real := Real) i x, s (pushforward (codegeneracy i) x)).
Proof. reflexivity. Qed.

Lemma singular_prism_first n (s : DPSimplicialSet.simplex (singular_set Real X) n) :
  face (singular_set Real Y) ord0 (singular_prism (ord0 : 'I_n.+1) s) =
    component (singular_map Real g) n s.
Proof.
apply topological_hom_ext => x.
change ((fun p => homotopy_map H (p.1, s p.2))
  (prism_parameter (Real := Real) (ord0 : 'I_n.+1) (pushforward (coface ord0) x)) = g (s x)).
rewrite prism_parameter_first; exact: homotopy_end.
Qed.

Lemma singular_prism_last n (s : DPSimplicialSet.simplex (singular_set Real X) n) :
  face (singular_set Real Y) ord_max (singular_prism (ord_max : 'I_n.+1) s) =
    component (singular_map Real f) n s.
Proof.
apply topological_hom_ext => x.
change ((fun p => homotopy_map H (p.1, s p.2))
  (prism_parameter (Real := Real) (ord_max : 'I_n.+1) (pushforward (coface ord_max) x)) = f (s x)).
rewrite prism_parameter_last; exact: homotopy_start.
Qed.

Lemma singular_prism_middle n (i : 'I_n.+1)
    (s : DPSimplicialSet.simplex (singular_set Real X) n.+1) :
  face (singular_set Real Y) (vertex_successor (vertex_widen i))
    (singular_prism (vertex_widen i) s) =
  face (singular_set Real Y) (vertex_successor (vertex_widen i))
    (singular_prism (vertex_successor i) s).
Proof.
apply topological_hom_ext => x.
change ((fun p => homotopy_map H (p.1, s p.2))
  (prism_parameter (Real := Real) (vertex_widen i)
    (pushforward (coface (vertex_successor (vertex_widen i))) x)) =
  (fun p => homotopy_map H (p.1, s p.2))
  (prism_parameter (Real := Real) (vertex_successor i)
    (pushforward (coface (vertex_successor (vertex_widen i))) x))).
by rewrite prism_parameter_middle.
Qed.

Lemma singular_prism_left n (i : 'I_n.+1) (j : 'I_n.+2)
    (s : DPSimplicialSet.simplex (singular_set Real X) n.+1) : (j <= i)%N ->
  face (singular_set Real Y) (vertex_widen j) (singular_prism (vertex_successor i) s) =
    singular_prism i (face (singular_set Real X) j s).
Proof.
move=> h; apply topological_hom_ext => x.
change ((fun p => homotopy_map H (p.1, s p.2))
  (prism_parameter (Real := Real) (vertex_successor i) (pushforward (coface (vertex_widen j)) x)) =
  homotopy_map H (prism_time (Real := Real) i x,
    s (pushforward (coface j) (pushforward (codegeneracy i) x)))).
by rewrite prism_parameter_left.
Qed.

Lemma singular_prism_right n (i : 'I_n.+1) (j : 'I_n.+2)
    (s : DPSimplicialSet.simplex (singular_set Real X) n.+1) : (i < j)%N ->
  face (singular_set Real Y) (vertex_successor j) (singular_prism (vertex_widen i) s) =
    singular_prism i (face (singular_set Real X) j s).
Proof.
move=> h; apply topological_hom_ext => x.
change ((fun p => homotopy_map H (p.1, s p.2))
  (prism_parameter (Real := Real) (vertex_widen i) (pushforward (coface (vertex_successor j)) x)) =
  homotopy_map H (prism_time (Real := Real) i x,
    s (pushforward (coface j) (pushforward (codegeneracy i) x)))).
by rewrite prism_parameter_right.
Qed.

End Prism.
End DPSingularPrism.

