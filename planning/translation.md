# Actual translation transport

The translation packet works on every bounded open nonempty Euclidean domain, without convexity or boundary smoothness assumptions.

- `K.translate c` is the literal image of the domain under `x ↦ c+x`.
- Haar invariance proves equal volume and equal normalized ambient Haar measures. Restricting the actual measure-preserving translation proves normalized-uniform pushforward.
- Homeomorphic frontier transport and isometry invariance prove exact boundary-distance equality at every point.
- Scalar mean/variance integrals transport under the actual uniform measure. Lebesgue and normalized integrals are related by the positive finite domain-volume factor; no mathematical statement is silently rescaled.
- Actual scalar/vector L2 pullbacks construct a genuine H1Graph pullback. Membership of W12 is proved by transporting every compact smooth constraint test and applying the derivative chain rule; the weak derivative relation is not assumed.
- The transported H1 graph preserves variance, gradient energy and distance-weighted gradient energy. Consequently both sets of admissible PI/IPI constants, and hence their literal least ENNReal constants, are unchanged.
- Translating an inner ball centered at `a` by `-a` puts its center at zero without altering its radius. This is the intended removal of the intermediate center-zero hypothesis in the source weighted inequality.

Compilation and imported-consumer evidence are tracked separately in the verification receipt; a draft is not a source completion. Original manuscript bytes and dependency pins are unchanged.
