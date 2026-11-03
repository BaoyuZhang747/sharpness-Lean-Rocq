From HB Require Import structures.
From mathcomp Require Import all_boot all_algebra boolp vector.
From DiazPark Require Import ModuleInfrastructure ModuleFiniteDimensional.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section NativeDimensions.
Variable K : fieldType.
Variables U V : vectType K.
Variable f : {linear U -> V}.

Lemma linear_injective_dimension : injective f -> (dim U <= dim V)%N.
Proof.
move=> hf.
have hker : lker (linfun f) = 0%VS.
  apply/eqP/lker0P=> x y; rewrite !lfunE; exact: hf.
have him := limg_dim_eq (f := linfun f) (U := fullv).
have hd : \dim (limg (linfun f)) = dim U.
  by rewrite him ?capfv ?hker // dimvf.
rewrite -hd -dimvf; exact: dimvS (subvf _).
Qed.

Lemma linear_surjective_image :
    (forall y, exists x, f x = y) -> limg (linfun f) = fullv.
Proof.
move=> hf; apply/vspaceP=> y; rewrite memvf; apply/memv_imgP.
have [x <-] := hf y; exists x; [exact: memvf | by rewrite lfunE].
Qed.

Lemma linear_surjective_dimension :
    (forall y, exists x, f x = y) -> (dim V <= dim U)%N.
Proof.
move=> hf; have hd := limg_ker_dim (linfun f) fullv.
rewrite linear_surjective_image // !dimvf in hd.
rewrite -hd; exact: leq_addl.
Qed.

Lemma linear_injective_equal_dimension_surjective :
    injective f -> dim U = dim V -> forall y, exists x, f x = y.
Proof.
move=> hf he y.
have hker : lker (linfun f) = 0%VS.
  apply/eqP/lker0P=> x z; rewrite !lfunE; exact: hf.
have him : limg (linfun f) = fullv.
  apply/eqP; rewrite eqEdim subvf /=.
  by rewrite limg_dim_eq ?capfv ?hker // !dimvf he.
have hy : y \in limg (linfun f) by rewrite him memvf.
have /memv_imgP[x _ hx] := hy; exists x; by rewrite -lfunE.
Qed.

Lemma linear_injective_dimension_strict :
    injective f -> (exists y, forall x, f x <> y) -> (dim U < dim V)%N.
Proof.
move=> hf [y hy]; rewrite ltn_neqAle linear_injective_dimension // andbT.
apply/negP=> /eqP he.
have [x hx] := linear_injective_equal_dimension_surjective hf he y.
exact: hy hx.
Qed.

Lemma linear_surjective_dimension_strict :
    (forall y, exists x, f x = y) ->
    (exists x, x <> 0 /\ f x = 0) -> (dim V < dim U)%N.
Proof.
move=> hf [x [hx hfx]].
have hk : (0 < \dim (lker (linfun f)))%N.
  rewrite lt0n dimv_eq0; apply/negP=> /eqP he.
  have hm : x \in lker (linfun f) by rewrite memv_ker lfunE hfx eqxx.
  rewrite he memv0 in hm; exact: hx (eqP hm).
have hd := limg_ker_dim (linfun f) fullv.
rewrite capfv (linear_surjective_image hf) !dimvf in hd.
by rewrite -hd -{1}(add0n (dim V)) ltn_add2r.
Qed.

End NativeDimensions.

Section FiniteModelMap.
Variable K : fieldType.
Variables U V : lmodType K.
Variables (hU : module_finitely_generated U) (hV : module_finitely_generated V).
Variable f : {linear U -> V}.

Definition finite_model_map_fun (x : chosen_finite_model hU) : chosen_finite_model hV :=
  chosen_model_inverse hV (f (chosen_model_map hU x)).

Lemma finite_model_map_linear : linear finite_model_map_fun.
Proof. by move=> a x y; rewrite /finite_model_map_fun !linearP. Qed.

HB.instance Definition _ := GRing.isLinear.Build K (chosen_finite_model hU)
  (chosen_finite_model hV) _ finite_model_map_fun finite_model_map_linear.

Definition finite_model_map :
    {linear chosen_finite_model hU -> chosen_finite_model hV} := finite_model_map_fun.

Lemma finite_model_mapE x :
    chosen_model_map hV (finite_model_map x) = f (chosen_model_map hU x).
Proof. exact: chosen_model_inverseK. Qed.

Lemma finite_model_map_injective : injective f -> injective finite_model_map.
Proof.
move=> hf x y he.
have hxy : chosen_model_map hU x = chosen_model_map hU y.
  apply: hf; by rewrite -!finite_model_mapE he.
by rewrite -(chosen_model_mapK (hfg := hU) x) -(chosen_model_mapK (hfg := hU) y) hxy.
Qed.

Lemma finite_model_map_surjective :
    (forall y, exists x, f x = y) -> forall y, exists x, finite_model_map x = y.
Proof.
move=> hf y; have [x hx] := hf (chosen_model_map hV y).
exists (chosen_model_inverse hU x).
change (chosen_model_inverse hV
  (f (chosen_model_map hU (chosen_model_inverse hU x))) = y).
rewrite chosen_model_inverseK hx.
exact: chosen_model_mapK.
Qed.

Lemma finitely_generated_injective_dimension : injective f ->
    (dim (chosen_finite_model hU) <= dim (chosen_finite_model hV))%N.
Proof. move=> hf; exact: linear_injective_dimension (finite_model_map_injective hf). Qed.

Lemma finitely_generated_surjective_dimension :
    (forall y, exists x, f x = y) ->
    (dim (chosen_finite_model hV) <= dim (chosen_finite_model hU))%N.
Proof. move=> hf; exact: linear_surjective_dimension (finite_model_map_surjective hf). Qed.

Lemma finitely_generated_injective_dimension_strict :
    injective f -> (exists y, forall x, f x <> y) ->
    (dim (chosen_finite_model hU) < dim (chosen_finite_model hV))%N.
Proof.
move=> hf [y hy]; apply: linear_injective_dimension_strict.
- exact: finite_model_map_injective.
- exists (chosen_model_inverse hV y) => x he; apply: (hy (chosen_model_map hU x)).
  by rewrite -finite_model_mapE he chosen_model_inverseK.
Qed.

Lemma finitely_generated_surjective_dimension_strict :
    (forall y, exists x, f x = y) -> (exists x, x <> 0 /\ f x = 0) ->
    (dim (chosen_finite_model hV) < dim (chosen_finite_model hU))%N.
Proof.
move=> hf [x [hx hfx]]; apply: linear_surjective_dimension_strict.
- exact: finite_model_map_surjective.
- exists (chosen_model_inverse hU x); split.
  + move=> hz; apply: hx; by rewrite -(chosen_model_inverseK hU x) hz linear0.
  + change (chosen_model_inverse hV
      (f (chosen_model_map hU (chosen_model_inverse hU x))) = 0).
    by rewrite chosen_model_inverseK hfx linear0.
Qed.

End FiniteModelMap.


