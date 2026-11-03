From HB Require Import structures.
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import ModuleInfrastructure MackeyModuleCarriers
  MackeyModuleMaps MackeyFiniteGeneration ModuleFiniteDimensional.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section FiniteGenerationExtension.
Variable R : pzRingType.
Variables U V W : lmodType R.
Variable f : {linear U -> V}.
Variable g : {linear V -> W}.
Hypothesis ker_image : forall v, g v = 0 -> exists u, f u = v.
Hypothesis g_surjective : forall w, exists v, g v = w.

Definition fg_lift (w : W) : V := projT1 (cid (g_surjective w)).
Lemma fg_liftE w : g (fg_lift w) = w.
Proof. exact: projT2 (cid (g_surjective w)). Qed.

Lemma finite_generation_extension :
    module_finitely_generated U -> module_finitely_generated W ->
    module_finitely_generated V.
Proof.
move=> [su hsu] [sw hsw].
pose s := [seq f u | u <- su] ++ [seq fg_lift w | w <- sw].
pose N := span_subspace (fun v => v \in s).
have hfN : forall u, N (f u).
  move=> u; apply: (@span_least R U _ (linear_preimage f N)) (hsu u).
  move=> z hz; apply: span_generator; rewrite /s mem_cat.
  by apply/orP; left; exact: map_f.
pose gN := (fun v : submodule_carrier N => g (submodule_val v)).
have gNL : linear gN.
  move=> a x y; rewrite /gN.
  change (g (submodule_inclusion N (a *: x + y)) =
    a *: g (submodule_inclusion N x) + g (submodule_inclusion N y)).
  by rewrite !linearP.
pose gNm : {linear submodule_carrier N -> W} :=
  HB.pack gN (GRing.isLinear.Build R _ W _ gN gNL).
have hgN : forall w, linear_image gNm w.
  move=> w; apply: (@span_least R W _ (linear_image gNm)) (hsw w).
  move=> z hz.
  have hNz : N (fg_lift z).
    apply: span_generator; rewrite /s mem_cat.
    by apply/orP; right; exact: map_f.
  exists (@submodule_in R V N (fg_lift z) hNz); exact: fg_liftE.
exists s => v.
have [w hw] := hgN (g v).
have he : g (v - submodule_val w) = 0.
  by rewrite linearB -hw subrr.
have [u hu] := ker_image he.
have ev : v = f u + submodule_val w.
  by rewrite hu subrK.
rewrite ev; exact: span_add (hfN u) (submodule_val_mem w).
Qed.

End FiniteGenerationExtension.

Definition module_noetherian (R : pzRingType) (V : lmodType R) :=
  forall N : module_subspace V,
    module_finitely_generated [the lmodType R of submodule_carrier N].

Section NoetherianClosure.
Variable R : pzRingType.

Lemma module_noetherian_zero (V : lmodType R) :
    (forall x : V, x = 0) -> module_noetherian V.
Proof.
move=> h N; exists [::] => x.
have hx : x = 0.
  apply: submodule_val_injective.
  change (submodule_val x = submodule_inclusion N 0).
  rewrite linear0; exact: h.
rewrite hx; exact: span_zero.
Qed.

Lemma module_noetherian_surjective (U V : lmodType R) (f : {linear U -> V}) :
    module_noetherian U -> (forall v, exists u, f u = v) -> module_noetherian V.
Proof.
move=> hU hf N.
pose P := linear_preimage f N.
have hp : forall x, P x -> N (f x) := fun x hx => hx.
pose fm := @submodule_map R U V f P N hp.
apply: (@finitely_generated_surjective_image R _ _ fm) (hU P).
move=> v; have [u hu] := hf (submodule_val v).
have hPu : P u by change (N (f u)); rewrite hu; exact: submodule_val_mem.
exists (@submodule_in R U P u hPu).
apply: submodule_val_injective; exact hu.
Qed.

Lemma module_noetherian_extension (U V W : lmodType R)
    (f : {linear U -> V}) (g : {linear V -> W}) :
    (forall v, g v = 0 -> exists u, f u = v) ->
    module_noetherian U -> module_noetherian W -> module_noetherian V.
Proof.
move=> hk hU hW N.
pose P := linear_preimage f N.
have hp : forall x, P x -> N (f x) := fun x hx => hx.
pose fm := @submodule_map R U V f P N hp.
pose gN := (fun v : submodule_carrier N => g (submodule_val v)).
have gNL : linear gN.
  move=> a x y; rewrite /gN.
  change (g (submodule_inclusion N (a *: x + y)) =
    a *: g (submodule_inclusion N x) + g (submodule_inclusion N y)).
  by rewrite !linearP.
pose gm : {linear submodule_carrier N -> W} :=
  HB.pack gN (GRing.isLinear.Build R _ W _ gN gNL).
apply: (@finite_generation_extension R _ _ _ fm (linear_to_image gm))
  (hU P) (hW (linear_image gm)).
- move=> v /linear_to_image_zero hv.
  have [u hu] := hk (submodule_val v) hv.
  have hPu : P u by change (N (f u)); rewrite hu; exact: submodule_val_mem.
  exists (@submodule_in R U P u hPu); apply: submodule_val_injective; exact hu.
- exact: linear_to_image_surjective.
Qed.

Lemma module_noetherian_product (U V : lmodType R) :
    module_noetherian U -> module_noetherian V ->
    module_noetherian [the lmodType R of (U * V)%type].
Proof.
move=> hU hV.
pose f (u : U) : (U * V)%type := (u, 0).
have fL : linear f.
  move=> a x y; rewrite /f. change ((a *: x + y, (0 : V)) = (a *: x + y, a *: (0 : V) + 0)).
  by rewrite scaler0 addr0.
pose fm : {linear U -> (U * V)%type} :=
  HB.pack f (GRing.isLinear.Build R _ _ _ f fL).
have gL : linear (@snd U V) by [].
pose gm : {linear (U * V)%type -> V} :=
  HB.pack (@snd U V) (GRing.isLinear.Build R _ _ _ (@snd U V) gL).
apply: (@module_noetherian_extension U _ V fm gm) hU hV.
by move=> [u v] /= ->; exists u.
Qed.

Lemma module_noetherian_injective (U V : lmodType R) (f : {linear U -> V}) :
    module_noetherian V -> injective f -> module_noetherian U.
Proof.
move=> hV hf.
pose zfun (v : V) : U := 0.
have zL : linear zfun by move=> a x y; rewrite /zfun scaler0 addr0.
pose zm : {linear V -> U} := HB.pack zfun (GRing.isLinear.Build R _ _ _ zfun zL).
apply: (@module_noetherian_extension V U V zm f); [|exact hV|exact hV].
move=> u hu; exists 0; change (0 = u).
apply: hf; by rewrite linear0 hu.
Qed.

Lemma noetherian_finitely_generated (V : lmodType R) :
    module_noetherian V -> module_finitely_generated V.
Proof.
move=> hV.
pose N := @ModuleSubspace R V (fun _ => True) I
  (fun _ _ _ _ => I) (fun _ _ _ => I).
apply: (@finitely_generated_surjective_image R _ _ (submodule_inclusion N)) (hV N).
move=> v; exists (@submodule_in R V N v I); by [].
Qed.

End NoetherianClosure.





