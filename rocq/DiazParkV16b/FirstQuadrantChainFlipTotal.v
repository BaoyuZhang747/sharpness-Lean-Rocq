(** The actual sign (-1)^(pq) chain isomorphism for exchanging bicomplex axes. *)
From Coq Require Import Arith.
From HB Require Import structures.
From mathcomp Require Import all_boot all_algebra boolp.
From DiazParkV16b Require Import ChainComplex ChainDegreewiseIso
  FirstQuadrantChainBicomplex FirstQuadrantChainTotal FirstQuadrantChainTotalMaps
  FirstQuadrantChainTotalAcyclic FirstQuadrantChainFlip.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPChainComplex DPChainDegreewiseIso DPFirstQuadrantChain
  DPFirstQuadrantChainTotal DPFirstQuadrantChainTotalMaps DPFirstQuadrantChainTotalAcyclic
  DPFirstQuadrantChainFlip.
Local Open Scope ring_scope.

Module DPFirstQuadrantChainFlipTotal.
Lemma swap_index p q n (h : (p+q)%coq_nat=n) : (q+p)%coq_nat=n.
Proof. rewrite Nat.add_comm; exact h. Qed.

Section Signs.
Variable R : pzRingType.
Variable V : lmodType R.
Lemma flip_horizontal_sign p q (x : V) :
  (-1:R)^+(p*q) *: ((-1:R)^+q *: x) = (-1:R)^+(p.+1*q) *: x.
Proof. by rewrite scalerA -exprD mulSn addnC. Qed.
Lemma flip_vertical_sign p q (x : V) :
  (-1:R)^+p *: ((-1:R)^+(p*q.+1) *: x) = (-1:R)^+(p*q) *: x.
Proof. by rewrite mulnS exprD -scalerA sign_scale_twice. Qed.
End Signs.

Section Total.
Variable R : pzRingType.
Variable K : bicomplex R.

Definition flip_total_at n (a : total_term (flip K) n) : total_term K n :=
  fun p q h => (-1:R)^+(p*q) *: a q p (swap_index h).
Lemma flip_total_at_linear n : linear (@flip_total_at n).
Proof.
move=> r a b; apply functional_extensionality_dep=> p;
 apply functional_extensionality_dep=> q; apply functional_extensionality_dep=> h.
change ((-1:R)^+(p*q) *: (r *: a q p (swap_index h)+b q p (swap_index h)) =
 r *: ((-1:R)^+(p*q) *: a q p (swap_index h)) + (-1:R)^+(p*q) *: b q p (swap_index h)).
by rewrite scalerDr !scalerA commr_sign.
Qed.
HB.instance Definition _ n := GRing.isLinear.Build R _ _ _ (@flip_total_at n) (@flip_total_at_linear n).

Definition flip_total_map : chain_map (total_complex (flip K)) (total_complex K).
Proof.
refine (@ChainMap R (total_complex (flip K)) (total_complex K)
  (fun n => (@flip_total_at n : {linear _ -> _})) _).
move=> n a; apply functional_extensionality_dep=> p;
 apply functional_extensionality_dep=> q; apply functional_extensionality_dep=> h.
have e1 : swap_index (horizontal_input h) = vertical_input (swap_index h) by apply Prop_irrelevance.
have e2 : swap_index (vertical_input h) = horizontal_input (swap_index h) by apply Prop_irrelevance.
change (horizontal K p q ((-1:R)^+(p.+1*q) *: a q p.+1 (swap_index (horizontal_input h))) +
 (-1:R)^+p *: vertical K p q ((-1:R)^+(p*q.+1) *: a q.+1 p (swap_index (vertical_input h))) =
 (-1:R)^+(p*q) *: (vertical K p q (a q.+1 p (horizontal_input (swap_index h))) +
 (-1:R)^+q *: horizontal K p q (a q p.+1 (vertical_input (swap_index h))))).
rewrite e1 e2 !linearZ.
change ((-1:R)^+(p.+1*q) *: horizontal K p q (a q p.+1 (vertical_input (swap_index h))) +
 (-1:R)^+p *: ((-1:R)^+(p*q.+1) *: vertical K p q (a q.+1 p (horizontal_input (swap_index h)))) =
 (-1:R)^+(p*q) *: (vertical K p q (a q.+1 p (horizontal_input (swap_index h))) +
 (-1:R)^+q *: horizontal K p q (a q p.+1 (vertical_input (swap_index h))))).
by rewrite scalerDr flip_horizontal_sign flip_vertical_sign addrC.
Defined.

Definition unflip_coordinates n (a : total_term K n) : total_term (flip K) n :=
  fun p q h => (-1:R)^+(p*q) *: a q p (swap_index h).

Lemma unflip_flip n (a : total_term (flip K) n) : unflip_coordinates (flip_total_at a) = a.
Proof.
apply functional_extensionality_dep=> p;
 apply functional_extensionality_dep=> q; apply functional_extensionality_dep=> h.
have he : swap_index (swap_index h)=h by apply Prop_irrelevance.
change ((-1:R)^+(p*q) *: ((-1:R)^+(q*p) *: a p q (swap_index (swap_index h))) = a p q h).
by rewrite he (mulnC q p) sign_scale_twice.
Qed.

Lemma flip_unflip n (a : total_term K n) : flip_total_at (unflip_coordinates a) = a.
Proof.
apply functional_extensionality_dep=> p;
 apply functional_extensionality_dep=> q; apply functional_extensionality_dep=> h.
have he : swap_index (swap_index h)=h by apply Prop_irrelevance.
change ((-1:R)^+(p*q) *: ((-1:R)^+(q*p) *: a p q (swap_index (swap_index h))) = a p q h).
by rewrite he (mulnC q p) sign_scale_twice.
Qed.

Lemma flip_total_injective n : injective (chain_map_at flip_total_map n).
Proof. exact (can_inj (@unflip_flip n)). Qed.

Lemma flip_total_surjective n : forall y : total_term K n, exists x,
  chain_map_at flip_total_map n x = y.
Proof. move=> y; exists (unflip_coordinates y); exact: flip_unflip. Qed.

Definition unflip_total_map : chain_map (total_complex K) (total_complex (flip K)) :=
  @inverse_chain R _ _ flip_total_map flip_total_injective flip_total_surjective.

Lemma unflip_total_left n x :
  chain_map_at unflip_total_map n (chain_map_at flip_total_map n x) = x.
Proof. exact: inverse_chain_left. Qed.

Lemma unflip_total_right n y :
  chain_map_at flip_total_map n (chain_map_at unflip_total_map n y) = y.
Proof. exact: inverse_chain_right. Qed.

End Total.
End DPFirstQuadrantChainFlipTotal.
