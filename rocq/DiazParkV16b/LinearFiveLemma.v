(** The five lemma for actual linear maps of arbitrary modules. *)
From mathcomp Require Import all_ssreflect all_algebra.
From DiazPark Require Import Category CategoryModules ModuleInfrastructure HomologicalModuleIso.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomologicalModuleIso.
Local Open Scope ring_scope.

Module DPLinearFiveLemma.
Section Five.
Variable R : pzRingType.
Variables A B C D E A' B' C' D' E' : lmodType R.
Variables (ab : {linear A -> B}) (bc : {linear B -> C})
  (cd : {linear C -> D}) (de : {linear D -> E})
  (ab' : {linear A' -> B'}) (bc' : {linear B' -> C'})
  (cd' : {linear C' -> D'}) (de' : {linear D' -> E'}).
Variables (a : {linear A -> A'}) (b : {linear B -> B'})
  (c : {linear C -> C'}) (d : {linear D -> D'}) (e : {linear E -> E'}).
Variables (hab : forall x, b (ab x) = ab' (a x))
  (hbc : forall x, c (bc x) = bc' (b x))
  (hcd : forall x, d (cd x) = cd' (c x))
  (hde : forall x, e (de x) = de' (d x)).
Variables (hexB : linear_exact ab bc) (hexC : linear_exact bc cd)
  (hexD : linear_exact cd de) (hexB' : linear_exact ab' bc')
  (hexC' : linear_exact bc' cd') (hexD' : linear_exact cd' de').

Theorem five_injective
    (ha : forall y, exists x, a x = y) (hb : injective b) (hd : injective d) : injective c.
Proof.
have ker : forall x, c x = 0 -> x = 0.
  move=> x hx.
  have hdx : cd x = 0 by apply hd; rewrite hcd hx !linear0.
  have [y hy] := proj1 (hexC x) hdx.
  have hby : bc' (b y) = 0 by rewrite -hbc hy hx.
  have [z hz] := proj1 (hexB' (b y)) hby.
  have [u hu] := ha z.
  have ey : y = ab u by apply hb; rewrite hab hu hz.
  rewrite -hy ey; apply/(hexB (ab u)); by exists u.
move=> x y h; apply/subr0_eq; apply ker; by rewrite linearB h subrr.
Qed.

Theorem five_surjective
    (hb : forall y, exists x, b x = y)
    (hd : forall y, exists x, d x = y) (he : injective e) :
  forall y, exists x, c x = y.
Proof.
move=> y; have [z hz] := hd (cd' y).
have hdz : de z = 0.
  apply he; rewrite linear0 hde hz; apply/(hexD' (cd' y)); by exists y.
have [x hx] := proj1 (hexD z) hdz.
have hcy : cd' (y - c x) = 0.
  by rewrite linearB -hcd hx hz subrr.
have [v hv] := proj1 (hexC' (y - c x)) hcy.
have [u hu] := hb v.
exists (x + bc u); rewrite linearD hbc hu hv.
by rewrite addrC subrK.
Qed.

Definition five_iso
    (ha : forall y, exists x, a x = y)
    (hbi : injective b) (hbs : forall y, exists x, b x = y)
    (hdi : injective d) (hds : forall y, exists x, d x = y)
    (he : injective e) : @isomorphism (module_category R) C C' :=
  @linear_bijection_iso R C C' c (five_injective ha hbi hdi)
    (five_surjective hbs hds he).
End Five.
End DPLinearFiveLemma.
