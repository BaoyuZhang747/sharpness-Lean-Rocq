(** The explicit sign-correct map from the total of column cones to the cone
    of the total map. *)
From Coq Require Import Arith Lia.
From HB Require Import structures.
From mathcomp Require Import all_boot all_algebra boolp.
From DiazParkV16b Require Import ChainComplex ChainMappingCone
  FirstQuadrantChainBicomplex FirstQuadrantChainTotal FirstQuadrantChainTotalMaps
  FirstQuadrantChainTotalAcyclic FirstQuadrantChainCone.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPChainComplex DPChainMappingCone DPFirstQuadrantChain
  DPFirstQuadrantChainTotal DPFirstQuadrantChainTotalMaps DPFirstQuadrantChainTotalAcyclic
  DPFirstQuadrantChainCone.
Local Open Scope ring_scope.

Module DPFirstQuadrantChainConeTotalMap.
Section TotalMap.
Variable R : pzRingType.
Variables K L : bicomplex R.
Variable f : bicomplex_map K L.
Local Notation B := (column_cone f).

Definition first_component p q : bicomplex_term B p q -> bicomplex_term L p q :=
  match q as k return bicomplex_term B p k -> bicomplex_term L p k with
  | 0%N => idfun
  | k.+1 => fst
  end.
Arguments first_component p q x : clear implicits.
Lemma first_component_linear p q : linear (first_component p q).
Proof. case: q=> [|q]; move=> r x y; reflexivity. Qed.
HB.instance Definition _ p q := GRing.isLinear.Build R _ _ _
  (first_component p q) (@first_component_linear p q).

Definition first_total n (a : total_term B n) : total_term L n :=
  fun p q h => first_component p q (a p q h).
Lemma first_total_linear n : linear (@first_total n).
Proof.
move=> r a b; apply functional_extensionality_dep=> p;
 apply functional_extensionality_dep=> q; apply functional_extensionality_dep=> h.
exact: linearP.
Qed.
HB.instance Definition _ n := GRing.isLinear.Build R _ _ _ (@first_total n) (@first_total_linear n).

Definition second_total n (a : total_term B n.+1) : total_term K n :=
  fun p q h => (-1:R)^+p *: (a p q.+1 (vertical_input h)).2.
Lemma second_total_linear n : linear (@second_total n).
Proof.
move=> r a b; apply functional_extensionality_dep=> p;
 apply functional_extensionality_dep=> q; apply functional_extensionality_dep=> h.
change ((-1:R)^+p *: (r *: (a p q.+1 (vertical_input h)).2 + (b p q.+1 (vertical_input h)).2) =
 r *: ((-1:R)^+p *: (a p q.+1 (vertical_input h)).2) +
 (-1:R)^+p *: (b p q.+1 (vertical_input h)).2).
by rewrite scalerDr !scalerA commr_sign.
Qed.
HB.instance Definition _ n := GRing.isLinear.Build R _ _ _ (@second_total n) (@second_total_linear n).

Lemma first_total_d n (a : total_term B n.+1) :
  first_total (total_d a) = total_d (first_total a) + total_map_at f (second_total a).
Proof.
apply functional_extensionality_dep=> p;
 apply functional_extensionality_dep=> q; apply functional_extensionality_dep=> h.
case: q h=> [|q] h;
 change (horizontal L p _ (first_component p.+1 _ (a p.+1 _ (horizontal_input h))) +
  (-1:R)^+p *: (vertical L p _ (a p _.+1 (vertical_input h)).1 +
    bicomplex_map_at f p _ (a p _.+1 (vertical_input h)).2) =
  (horizontal L p _ (first_component p.+1 _ (a p.+1 _ (horizontal_input h))) +
   (-1:R)^+p *: vertical L p _ (a p _.+1 (vertical_input h)).1) +
  bicomplex_map_at f p _ ((-1:R)^+p *: (a p _.+1 (vertical_input h)).2));
 by rewrite scalerDr linearZ addrA.
Qed.

Lemma second_total_d n (a : total_term B n.+2) :
  second_total (total_d a) = - total_d (second_total a).
Proof.
apply functional_extensionality_dep=> p;
 apply functional_extensionality_dep=> q; apply functional_extensionality_dep=> h.
have he : horizontal_input (vertical_input h) = vertical_input (horizontal_input h)
  by apply Prop_irrelevance.
change ((-1:R)^+p *:
 (horizontal K p q (a p.+1 q.+1 (horizontal_input (vertical_input h))).2 +
  (-1:R)^+p *: (-vertical K p q (a p q.+2 (vertical_input (vertical_input h))).2)) =
 -(horizontal K p q ((-1:R)^+p.+1 *: (a p.+1 q.+1 (vertical_input (horizontal_input h))).2) +
   (-1:R)^+p *: vertical K p q ((-1:R)^+p *: (a p q.+2 (vertical_input (vertical_input h))).2))).
rewrite he scalerDr !linearZ !sign_scale_twice exprS mulN1r.
change ((-1:R)^+p *: horizontal K p q
  (a p.+1 q.+1 (vertical_input (horizontal_input h))).2 -
  vertical K p q (a p q.+2 (vertical_input (vertical_input h))).2 =
 -((-((-1:R)^+p)) *: horizontal K p q
  (a p.+1 q.+1 (vertical_input (horizontal_input h))).2 +
  vertical K p q (a p q.+2 (vertical_input (vertical_input h))).2)).
by rewrite scaleNr opprD opprK.
Qed.

Definition cone_total_at n : total_term B n ->
    chain_term (mapping_cone (total_map f)) n :=
  match n as k return total_term B k -> chain_term (mapping_cone (total_map f)) k with
  | 0%N => @first_total 0%N
  | k.+1 => fun a => (first_total a, second_total a)
  end.
Arguments cone_total_at n x : clear implicits.

Lemma cone_total_at_linear n : linear (cone_total_at n).
Proof.
case: n=> [|n]; move=> r a b; first exact: linearP.
change ((first_total (r *: a+b),second_total (r *: a+b)) =
 (r *: first_total a+first_total b,r *: second_total a+second_total b)).
by rewrite !linearP.
Qed.
HB.instance Definition _ n := GRing.isLinear.Build R _ _ _ (cone_total_at n) (@cone_total_at_linear n).

Definition cone_total_map : chain_map (total_complex B) (mapping_cone (total_map f)).
Proof.
refine (@ChainMap R (total_complex B) (mapping_cone (total_map f))
  (fun n => (cone_total_at n : {linear _ -> _})) _).
case=> [|n] a.
- exact: esym (first_total_d a).
- change ((total_d (first_total a)+total_map_at f (second_total a), -total_d (second_total a)) =
   (first_total (total_d a), second_total (total_d a))).
  by rewrite first_total_d second_total_d.
Defined.

End TotalMap.
End DPFirstQuadrantChainConeTotalMap.
