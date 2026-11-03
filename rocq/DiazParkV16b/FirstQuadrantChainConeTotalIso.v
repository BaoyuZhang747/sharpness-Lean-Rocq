(** Actual degreewise inverse coordinates and inverse chain maps for the
    total-column-cone comparison. *)
From Coq Require Import Arith Lia.
From mathcomp Require Import all_boot all_algebra boolp.
From DiazParkV16b Require Import ChainComplex ChainMappingCone ChainDegreewiseIso
  FirstQuadrantChainBicomplex FirstQuadrantChainTotal FirstQuadrantChainTotalMaps
  FirstQuadrantChainTotalAcyclic FirstQuadrantChainCone FirstQuadrantChainConeTotalMap.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPChainComplex DPChainMappingCone DPChainDegreewiseIso
  DPFirstQuadrantChain DPFirstQuadrantChainTotal DPFirstQuadrantChainTotalMaps
  DPFirstQuadrantChainTotalAcyclic DPFirstQuadrantChainCone DPFirstQuadrantChainConeTotalMap.
Local Open Scope ring_scope.

Module DPFirstQuadrantChainConeTotalIso.
Section Iso.
Variable R : pzRingType.
Variables K L : bicomplex R.
Variable f : bicomplex_map K L.
Local Notation B := (column_cone f).
Local Notation T := (total_complex B).
Local Notation C := (mapping_cone (total_map f)).

Lemma previous_vertical p q n (h : (p+q.+1)%coq_nat=n.+1) : (p+q)%coq_nat=n.
Proof. lia. Qed.

Definition inverse_zero (y : total_term L 0%N) : total_term B 0%N.
Proof.
move=> p [|q] h; first exact (y p 0%N h).
exfalso; lia.
Defined.

Definition inverse_positive n (y : total_term L n.+1) (x : total_term K n) : total_term B n.+1.
Proof.
move=> p [|q] h; first exact (y p 0%N h).
exact (y p q.+1 h, (-1:R)^+p *: x p q (previous_vertical h)).
Defined.

Definition inverse_coordinates n : chain_term C n -> chain_term T n :=
  match n as k return chain_term C k -> chain_term T k with
  | 0%N => inverse_zero
  | k.+1 => fun a => inverse_positive a.1 a.2
  end.
Arguments inverse_coordinates n x : clear implicits.

Lemma inverse_forward n (a : chain_term T n) :
  inverse_coordinates n (chain_map_at (cone_total_map f) n a) = a.
Proof.
case: n a=> [|n] a.
- apply functional_extensionality_dep=> p;
   apply functional_extensionality_dep=> q; apply functional_extensionality_dep=> h.
  case: q h=> [|q] h; first reflexivity.
  exfalso; lia.
- apply functional_extensionality_dep=> p;
   apply functional_extensionality_dep=> q; apply functional_extensionality_dep=> h.
  case: q h=> [|q] h; first reflexivity.
  change (((a p q.+1 h).1,
    (-1:R)^+p *: ((-1:R)^+p *: (a p q.+1 (vertical_input (previous_vertical h))).2)) = a p q.+1 h).
  have he : vertical_input (previous_vertical h)=h by apply Prop_irrelevance.
  by rewrite he sign_scale_twice; case (a p q.+1 h).
Qed.

Lemma forward_inverse n (a : chain_term C n) :
  chain_map_at (cone_total_map f) n (inverse_coordinates n a) = a.
Proof.
case: n a=> [|n] a.
- apply functional_extensionality_dep=> p;
   apply functional_extensionality_dep=> q; apply functional_extensionality_dep=> h.
  case: q h=> [|q] h; first reflexivity.
  exfalso; lia.
- case: a=> y x; change ((@first_total R K L f n.+1 (inverse_positive y x),
    @second_total R K L f n (inverse_positive y x)) = (y,x)).
  congr (_, _).
  + apply functional_extensionality_dep=> p;
     apply functional_extensionality_dep=> q; apply functional_extensionality_dep=> h.
    by case: q h=> [|q] h.
  + apply functional_extensionality_dep=> p;
     apply functional_extensionality_dep=> q; apply functional_extensionality_dep=> h.
    change ((-1:R)^+p *: ((-1:R)^+p *: x p q (previous_vertical (vertical_input h))) = x p q h).
    have he : previous_vertical (vertical_input h)=h by apply Prop_irrelevance.
    by rewrite he sign_scale_twice.
Qed.

Theorem cone_total_injective n : injective (chain_map_at (cone_total_map f) n).
Proof. exact (can_inj (@inverse_forward n)). Qed.

Theorem cone_total_surjective n : forall y : chain_term C n,
  exists x, chain_map_at (cone_total_map f) n x = y.
Proof. move=> y; exists (inverse_coordinates n y); exact: forward_inverse. Qed.

Definition cone_total_inverse : chain_map C T :=
  @inverse_chain R T C (cone_total_map f) cone_total_injective cone_total_surjective.

Lemma cone_total_inverse_right n y :
  chain_map_at (cone_total_map f) n (chain_map_at cone_total_inverse n y) = y.
Proof. exact: inverse_chain_right. Qed.

Lemma cone_total_inverse_left n x :
  chain_map_at cone_total_inverse n (chain_map_at (cone_total_map f) n x) = x.
Proof. exact: inverse_chain_left. Qed.

Theorem cone_total_acyclic : acyclic T -> acyclic C.
Proof.
move=> ht n y hy.
have hx := @chain_map_cycle R C T cone_total_inverse n y hy.
have [z hz] := @ht n _ hx.
exists (chain_map_at (cone_total_map f) n.+1 z).
rewrite chain_map_commutes hz; exact: cone_total_inverse_right.
Qed.

End Iso.
End DPFirstQuadrantChainConeTotalIso.
