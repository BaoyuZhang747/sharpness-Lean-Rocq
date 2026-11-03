From HB Require Import structures.
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import ModuleInfrastructure MackeyModuleMaps
  CategoryModules CategoryModuleLinear CategoryModuleProducts CategoryModuleDirectSums.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section FiniteProducts.
Variable R : pzRingType.
Variable I : finType.
Variable V : I -> lmodType R.

Definition finite_product_single i (x : V i) : module_product_type V :=
  submodule_inclusion (sum_support_subspace V) (sum_single x).

Lemma finite_product_single_linear i : linear (@finite_product_single i).
Proof. by move=> a x y; rewrite /finite_product_single !linearP. Qed.
HB.instance Definition _ i := GRing.isLinear.Build R (V i)
  (module_product_type V) _ (@finite_product_single i) (@finite_product_single_linear i).

Lemma finite_product_single_same i (x : V i) : finite_product_single x i = x.
Proof. exact: sum_single_same. Qed.

Lemma finite_product_single_away i (x : V i) j :
    i <> j -> finite_product_single x j = 0.
Proof. exact: sum_single_away. Qed.

Lemma finite_product_expansion (v : module_product_type V) :
    v = \sum_i finite_product_single (v i).
Proof.
apply functional_extensionality_dep=> j.
change (v j = module_hom_to_linear (module_product_projection V j)
  (\sum_i finite_product_single (v i))).
rewrite linear_sum /= (bigD1 j) //= finite_product_single_same.
rewrite big1 ?addr0 // => i hi; apply: finite_product_single_away.
exact: (elimN eqP hi).
Qed.

Theorem finite_product_finitely_generated :
    (forall i, module_finitely_generated (V i)) ->
    module_finitely_generated (module_product_type V).
Proof.
move=> hV.
pose gens i := projT1 (cid (hV i)).
have hg i x : module_span (fun y => y \in gens i) x.
  exact: (projT2 (cid (hV i))).
pose s := flatten [seq [seq finite_product_single x | x <- gens i] | i <- enum I].
pose N := span_subspace (fun v => v \in s).
have hsingle i (x : V i) : N (finite_product_single x).
  apply: (@span_least R (V i) _
    (linear_preimage (@finite_product_single i : {linear _ -> _}) N)) (hg i x).
  move=> y hy; apply: span_generator; apply/flattenP.
  exists [seq finite_product_single x | x <- gens i].
  + apply/mapP; exists i; [exact: mem_enum | reflexivity].
  + exact: map_f.
exists s => v; rewrite (finite_product_expansion v).
apply: big_ind => [|x y hx hy|i _].
- exact: span_zero.
- exact: span_add hx hy.
- exact: hsingle.
Qed.

End FiniteProducts.


