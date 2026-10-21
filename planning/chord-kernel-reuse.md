# Actual chord-kernel reuse route

Bounded read-only API inspection, 2026-10-21, pinned Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679. This records both the inspected APIs and the now implemented chord foundation; it does not claim a completed source theorem.

Mathlib/Probability/Kernel/CondDistrib.lean supplies a genuine conditional Markov kernel, joint-law factorization via compProd_map_condDistrib, and uniqueness almost everywhere via condDistrib_ae_eq_of_measure_eq_compProd and its measurable variant. The latter requires proving the actual joint law equals the proposed measure-kernel product; it does not identify an arbitrary conditional distribution with geometric uniform chord sampling automatically. condExp_ae_eq_integral_condDistrib can then connect the identified kernel to the L2 projection foundation.

The implemented route in Geometry/ChordMeasure and Markov/ChordKernel avoids interval-endpoint functions entirely. It normalizes one-dimensional volume on the measurable line preimage of the body, then pushes this law forward along the continuous affine line map. Joint measurability follows from measurable section volumes via Fubini. Positivity and finiteness follow from openness, an actual body starting point, unit direction, boundedness, and the line isometry. The kernel is probability-valued on the subtype of valid point/direction pairs and has body mass one. For a convex body the line intersection is the source interval chord; no endpoint-measurability gap remains in this construction.

The remaining concrete obligations are the body-valued restriction, direction mixing, stationarity, and geometric Fubini/disintegration identification with the conditional law under uniform volume. These are not established by probability-valuedness alone.

Mathlib/MeasureTheory/Measure/Haar/Disintegration.lean contains Haar pushforward/proportionality results, not a ready-made normalized restricted-body chord kernel. Mathlib/Probability/Distributions/Uniform.lean provides IsUniform measure/PDF/integration APIs but does not discharge endpoint measurability.

For finite-chi-square initial laws, equality outside a uniform-null exceptional set may suffice for law evolution. That must be proved and stated separately from an everywhere pointwise chord-algorithm theorem. The generic Markov and conditional-projection helpers alone do not close this gap.
