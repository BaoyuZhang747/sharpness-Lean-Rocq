(** Actual disjoint-family maps and interval homotopies, using the native sum topology. *)
From mathcomp Require Import all_ssreflect all_algebra all_classical.
From mathcomp Require Import reals topology function_spaces sigT_topology unstable.
From DiazPark Require Import Category.
From DiazParkV16b Require Import TopologicalCategory TopologicalCategoryHomotopy TopologicalHomotopyInterval.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPTopological DPTopologicalHomotopy DPTopologicalHomotopyInterval.
Import ArrowAsCompactOpen.
Local Open Scope classical_set_scope.

Module DPTopologicalCoproductHomotopy.

Lemma product_swap_continuous (A B : topologicalType) :
  continuous (fun p : (A * B)%type => (p.2,p.1)).
Proof.
move=> p; apply: (@cvg_pair _ B A (nbhs p) (nbhs p.2) (nbhs p.1)
  (@nbhs_filter [the topologicalType of (A*B)%type] p)
  (@nbhs_filter B p.2) (@nbhs_filter A p.1)); [exact: cvg_snd | exact: cvg_fst].
Qed.

Definition family_space (I : choiceType) (X : I -> topologicalType) : topologicalType :=
  [the topologicalType of {i : I & X i}].

Definition family_map_fun (I : choiceType) (X Y : I -> topologicalType)
    (f : forall i, continuousType (X i) (Y i)) (x : family_space X) : family_space Y :=
  sigT_fun (fun i a => existT Y i (f i a)) x.

Lemma family_map_continuous (I : choiceType) (X Y : I -> topologicalType)
    (f : forall i, continuousType (X i) (Y i)) : continuous (family_map_fun f).
Proof.
apply: (@sigT_continuous I X (family_space Y) (fun i x => existT Y i (f i x))).
move=> i x; apply: (@continuous_comp (X i) (Y i) (family_space Y) (f i) (existT Y i) x);
  [exact: cts_fun | exact: existT_continuous].
Qed.

Definition family_map (I : choiceType) (X Y : I -> topologicalType)
    (f : forall i, continuousType (X i) (Y i)) : continuousType (family_space X) (family_space Y) :=
  continuous_map (@family_map_continuous I X Y f).

Section WithParameter.
Variables (I : choiceType) (X : I -> topologicalType) (V Y : topologicalType).
Variable f : forall i, continuousType (V * X i)%type Y.

Definition family_parameter (p : (V * family_space X)%type) : Y :=
  f (projT1 p.2) (p.1,projT2 p.2).

Lemma family_parameter_continuous (hV : hausdorff_space V)
    (lcV : locally_compact [set: V]) : continuous family_parameter.
Proof.
have hfi i : continuous (fun p : (X i * V)%type => f i (p.2,p.1)).
  move=> p; apply: (@continuous_comp _ [the topologicalType of (V*X i)%type] Y
    (fun q => (q.2,q.1)) (f i) p); [exact: product_swap_continuous | exact: cts_fun].
pose F : family_space X -> V -> Y := fun z t => family_parameter (t,z).
have hc : continuous F.
  apply: (@sigT_continuous I X [the topologicalType of (V -> Y)]
    (fun i x t => f i (t,x))).
  move=> i; exact: continuous_curry_fun (hfi i).
have hs z : continuous (F z).
  case: z => i x; exact: (proj2 (continuous_curry (hfi i)) x).
have hu : continuous (uncurry F) := continuous_uncurry lcV hV hc hs.
move=> p; apply: (@continuous_comp _ [the topologicalType of (family_space X*V)%type] Y
  (fun q => (q.2,q.1)) (uncurry F) p); [exact: product_swap_continuous | exact: hu].
Qed.
End WithParameter.

Section Homotopy.
Variable Real : realType.
Variables (I : choiceType) (X Y : I -> topologicalType).
Variables f g : forall i, continuousType (X i) (Y i).
Variable H : forall i, continuous_homotopy Real (f i) (g i).

Definition family_homotopy_piece i : continuousType (unit_interval_space Real * X i)%type (family_space Y).
Proof.
apply: (@continuous_map _ _ (fun p => existT Y i (homotopy_map (H i) p))).
move=> p; apply: (@continuous_comp _ (Y i) (family_space Y) (homotopy_map (H i)) (existT Y i) p);
  [exact: cts_fun | exact: existT_continuous].
Defined.

Definition family_homotopy : continuous_homotopy Real (family_map f) (family_map g).
Proof.
refine (@ContinuousHomotopy Real _ _ _ _
  (continuous_map (@family_parameter_continuous I X (unit_interval_space Real) (family_space Y)
    family_homotopy_piece (@unit_interval_hausdorff Real) (@unit_interval_locally_compact Real))) _ _).
- move=> [i x]; change (existT Y i (homotopy_map (H i) (interval_zero Real,x)) = existT Y i (f i x)).
  by rewrite homotopy_start.
- move=> [i x]; change (existT Y i (homotopy_map (H i) (interval_one Real,x)) = existT Y i (g i x)).
  by rewrite homotopy_end.
Defined.

Lemma family_homotopy_at i t x :
  homotopy_map family_homotopy (t,existT X i x) = existT Y i (homotopy_map (H i) (t,x)).
Proof. reflexivity. Qed.
End Homotopy.
End DPTopologicalCoproductHomotopy.
