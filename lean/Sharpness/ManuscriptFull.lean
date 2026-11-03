import Sharpness.ManuscriptSharpness
import Sharpness.Unconditional.SubgroupBousfieldKanCollapse
import Sharpness.Unconditional.NormalizerBousfieldKanCollapse

/-! Full main-result aggregate for the supplied v1.6b manuscript.

`ManuscriptSharpness` supplies the elementary algebraic and geometric
sharpness proofs. The additional imports construct and prove collapse of
the cohomological Bousfield–Kan spectral sequences in the unnormalized
singular-cochain replacement model. Their pages come from the actual column
filtration; their second pages are the actual derived limits; their finite
convergence is transported along the constructed decomposition augmentations
to singular cohomology of the linking-system classifying space.

This model convention does not assert a separately formalized identification
with an independently defined geometric skeletal sequence or Tot tower.
-/
