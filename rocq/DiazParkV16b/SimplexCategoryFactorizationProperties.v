From mathcomp Require Import all_ssreflect order boolp.
From DiazParkV16b Require Import SimplexCategory SimplexCategoryFactorization
  SimplexCategoryFactorizationSections.

Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module DPSimplexFactorizationProperties.
Import DPSimplexCategory DPSimplexFactorization DPSimplexSections.

Lemma ordinal_identity_surjective n : ordinal_surjective (ordinal_map_identity n).
Proof. intro i. exists i. reflexivity. Qed.

Lemma ordinal_compose_surjective n m k (f : ordinal_map n m) (g : ordinal_map m k)
    (hf : ordinal_surjective f) (hg : ordinal_surjective g) :
  ordinal_surjective (ordinal_map_compose f g).
Proof.
  intro z. destruct (hg z) as [y hy]. destruct (hf y) as [x hx].
  exists x. change (g (f x) = z). rewrite hx. exact hy.
Qed.

Lemma ordinal_compose_injective n m k (f : ordinal_map n m) (g : ordinal_map m k)
    (hf : ordinal_injective f) (hg : ordinal_injective g) :
  ordinal_injective (ordinal_map_compose f g).
Proof. intros i j h. apply hf. apply hg. exact h. Qed.

Lemma ordinal_image_dimension_le_source n m (f : ordinal_map n m) :
  (ordinal_image_dimension f <= n)%N.
Proof. exact (ordinal_surjective_dimension (@image_surjection_surjective n m f)). Qed.

Lemma ordinal_image_dimension_le_target n m (f : ordinal_map n m) :
  (ordinal_image_dimension f <= m)%N.
Proof. exact (ordinal_injective_dimension (@image_injection_injective n m f)). Qed.

Lemma image_dimension_equal_injective n m (f : ordinal_map n m)
    (e : ordinal_image_dimension f = n) : ordinal_injective f.
Proof.
  rewrite <- (image_factorization f). apply ordinal_compose_injective.
  - exact (@ordinal_surjective_same_dimension_injective _ _ _
      (@image_surjection_surjective n m f) (esym e)).
  - exact (@image_injection_injective n m f).
Qed.

Lemma noninjective_image_dimension_lt n m (f : ordinal_map n m)
    (hf : ~ ordinal_injective f) : (ordinal_image_dimension f < n)%N.
Proof.
  rewrite ltn_neqAle. apply/andP. split.
  - apply/eqP. intro e. exact (hf (image_dimension_equal_injective e)).
  - exact (ordinal_image_dimension_le_source f).
Qed.

Lemma ordinal_epimono_factorization n m (f : ordinal_map n m) :
  exists k, exists q : ordinal_map n k, exists i : ordinal_map k m,
    ordinal_surjective q /\ ordinal_injective i /\ ordinal_map_compose q i = f.
Proof.
  exists (ordinal_image_dimension f), (image_surjection f), (image_injection f).
  split; first exact (@image_surjection_surjective n m f).
  split; [exact (@image_injection_injective n m f)|exact (image_factorization f)].
Qed.

End DPSimplexFactorizationProperties.
