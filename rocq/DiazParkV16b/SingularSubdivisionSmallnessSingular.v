(** Every singular generator eventually subdivides into actual cover-small simplices. *)
From mathcomp Require Import all_ssreflect all_algebra all_classical all_fingroup.
From mathcomp Require Import reals topology.
From DiazPark Require Import Category.
From DiazParkV16b Require Import TopologicalCategory TopologicalSimplexBasic
  SimplicialSet SimplicialSubcomplex SingularSet SingularSmallChains
  SingularSubdivisionOperators SingularSubdivisionMeshIterates
  SingularSubdivisionSmallnessSimplex.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPTopological DPSingularSet DPSingularSmallChains DPSimplicialSubcomplex
  DPSingularSubdivision DPSingularSubdivisionMeshIterates
  DPSingularSubdivisionSmallnessSimplex.
Local Open Scope classical_set_scope.

Module DPSingularSubdivisionSmallnessSingular.
Section SingularSmallness.
Variable Real : realType.
Variable X : topologicalType.

Definition iterated_singular_barycentric_cell n (ps : seq {perm 'I_n.+1})
    (s : DPSimplicialSet.simplex (singular_set Real X) n) :
    DPSimplicialSet.simplex (singular_set Real X) n :=
  continuous_compose (iterated_barycentric_cell Real ps) s.

Lemma iterated_singular_barycentric_cell_at n (ps : seq {perm 'I_n.+1})
    (s : DPSimplicialSet.simplex (singular_set Real X) n) x :
  iterated_singular_barycentric_cell ps s x = s (iterated_barycentric_cell Real ps x).
Proof. reflexivity. Qed.

Lemma iterated_singular_barycentric_cell_nil n
    (s : DPSimplicialSet.simplex (singular_set Real X) n) :
  iterated_singular_barycentric_cell [::] s = s.
Proof.
apply topological_hom_ext => x.
by rewrite iterated_singular_barycentric_cell_at iterated_barycentric_cell_nil.
Qed.

Lemma iterated_singular_barycentric_cell_cons n (p : {perm 'I_n.+1}) ps
    (s : DPSimplicialSet.simplex (singular_set Real X) n) :
  iterated_singular_barycentric_cell (p :: ps) s =
    singular_barycentric_cell p (iterated_singular_barycentric_cell ps s).
Proof.
apply topological_hom_ext => x.
by rewrite singular_barycentric_cell_at !iterated_singular_barycentric_cell_at
  iterated_barycentric_cell_cons.
Qed.

Lemma iterated_singular_barycentric_cell_cat n (ps qs : seq {perm 'I_n.+1})
    (s : DPSimplicialSet.simplex (singular_set Real X) n) :
  iterated_singular_barycentric_cell (ps ++ qs) s =
    iterated_singular_barycentric_cell ps (iterated_singular_barycentric_cell qs s).
Proof.
elim: ps => [|p ps ih]; first by rewrite cat0s iterated_singular_barycentric_cell_nil.
by rewrite cat_cons !iterated_singular_barycentric_cell_cons ih.
Qed.

Theorem singular_generator_eventually_small n (I : Type) (U : I -> set X)
    (hopen : forall i, open (U i))
    (s : DPSimplicialSet.simplex (singular_set Real X) n)
    (hcover : forall x, exists i, U i (s x)) :
  exists N : nat, forall (ps : seq {perm 'I_n.+1}), (N <= size ps)%N ->
    member (small_subcomplex Real U) n (iterated_singular_barycentric_cell ps s).
Proof.
have hs : continuous s by exact: cts_fun.
have hop : forall i, open (s @^-1` U i).
  move=> i.
  exact ((proj1 (@continuousP (DPTopologicalSimplex.simplex_space Real n) X s)
    hs) (U i) (hopen i)).
case: (@iterated_barycentric_cells_open_cover Real n I (fun i => s @^-1` U i)
  hop hcover) => N hN.
exists N => ps hps; case: (hN ps hps) => i hi; exists i => x.
exact: hi.
Qed.

Theorem singular_generator_eventually_small_of_cover n (I : Type) (U : I -> set X)
    (hopen : forall i, open (U i)) (hcover : forall x, exists i, U i x)
    (s : DPSimplicialSet.simplex (singular_set Real X) n) :
  exists N : nat, forall (ps : seq {perm 'I_n.+1}), (N <= size ps)%N ->
    member (small_subcomplex Real U) n (iterated_singular_barycentric_cell ps s).
Proof. apply: singular_generator_eventually_small => // x; exact: hcover. Qed.

End SingularSmallness.
End DPSingularSubdivisionSmallnessSingular.
