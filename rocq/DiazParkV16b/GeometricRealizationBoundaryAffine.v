From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra all_classical.
From mathcomp Require Import reals topology normedtype matrix_normedtype subtype_topology.
From DiazParkV16b Require Import TopologicalSimplexBasic TopologicalSimplexAffine.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Module DPRealizationBoundaryAffine.
Import DPTopologicalSimplex DPTopologicalSimplexAffine.
Section Affine.
Variable Real : realType.

Lemma pushforward_injective_coordinate n m (f : 'I_n.+1 -> 'I_m.+1)
    (hf : injective f) (x : simplex Real n) i :
  coordinate (pushforward f x) (f i) = coordinate x i.
Proof.
rewrite pushforward_coordinate (bigD1 i) // eqxx /= mulr1.
have -> : \sum_(j | j != i) coordinate x j * (f j == f i)%:R = (0 : Real).
  apply: big1 => j /negbTE hj. by rewrite (inj_eq hf) hj mulr0.
by rewrite addr0.
Qed.

Lemma pushforward_injective n m (f : 'I_n.+1 -> 'I_m.+1) (hf : injective f) :
  injective (@pushforward Real n m f).
Proof.
move=> x y e; apply: simplex_ext => i.
have h := f_equal (fun z : simplex Real m => coordinate z (f i)) e.
by rewrite !pushforward_injective_coordinate in h.
Qed.

Lemma pushforward_missing_coordinate n m (f : 'I_n.+1 -> 'I_m.+1)
    (x : simplex Real n) j (hj : forall i, f i <> j) :
  coordinate (pushforward f x) j = 0.
Proof.
rewrite pushforward_coordinate; apply: big1 => i _.
have hf : (f i == j) = false by apply/negbTE/negP => /eqP e; exact: (hj i e).
by rewrite hf mulr0.
Qed.

Lemma pushforward_same_support n m (f g : 'I_n.+1 -> 'I_m.+1)
    (x : simplex Real n)
    (h : forall i, coordinate x i <> 0 -> f i = g i) :
  pushforward f x = pushforward g x.
Proof.
apply: simplex_ext => j; rewrite !pushforward_coordinate.
apply: eq_bigr => i _.
case: (eqVneq (coordinate x i) 0) => [hi|hi].
- by rewrite hi !mul0r.
- have hi' : coordinate x i <> 0 by move=> he; move: hi; rewrite he eqxx.
  rewrite (h i hi'); reflexivity.
Qed.

Definition vertex_preimage n m (f : 'I_n.+1 -> 'I_m.+1) (y : 'I_m.+1) : 'I_n.+1 :=
  match pselect (exists x, f x = y) with
  | left h => proj1_sig (cid h)
  | right _ => ord0
  end.

Lemma vertex_preimage_hit n m (f : 'I_n.+1 -> 'I_m.+1) y
    (hy : exists x, f x = y) : f (vertex_preimage f y) = y.
Proof.
rewrite /vertex_preimage; case: pselect => [h|h].
- exact: (proj2_sig (cid h)).
- exfalso; exact: (h hy).
Qed.

Lemma vertex_preimage_cancel n m (f : 'I_n.+1 -> 'I_m.+1)
    (hf : injective f) x : vertex_preimage f (f x) = x.
Proof. apply: hf. apply: vertex_preimage_hit. by exists x. Qed.

(** A point supported on the image of a vertex map has an actual affine
    preimage. This uses a globally continuous affine map in the reverse
    direction; it does not assume the reverse vertex map is monotone. *)
Definition supported_on_image n m (f : 'I_n.+1 -> 'I_m.+1) (x : simplex Real m) : Prop :=
  forall j, (forall i, f i <> j) -> coordinate x j = 0.

Lemma pushforward_supported n m (f : 'I_n.+1 -> 'I_m.+1) (x : simplex Real n) :
  supported_on_image f (pushforward f x).
Proof. move=> j hj; exact: pushforward_missing_coordinate. Qed.

Lemma pushforward_preimage_supported n m (f : 'I_n.+1 -> 'I_m.+1)
    (x : simplex Real m) (hx : supported_on_image f x) :
  pushforward f (pushforward (vertex_preimage f) x) = x.
Proof.
rewrite pushforward_composition.
transitivity (pushforward (@idfun 'I_m.+1) x); last exact: pushforward_identity.
apply: pushforward_same_support => j hj.
apply: vertex_preimage_hit.
case: (pselect (exists i, f i = j)) => [h|h]; first exact h.
exfalso; apply: hj; apply: hx => i hi; apply: h; by exists i.
Qed.

End Affine.
End DPRealizationBoundaryAffine.
