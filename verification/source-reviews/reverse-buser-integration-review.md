# Reverse-Buser source review: S07 and S08

Accepted 2026-10-21 15:53 UTC. The successful normal configured Lake build and separate full importing consumer are recorded in [reverse-buser-source.json](../reverse-buser-source.json). This review is specific to the S07/S08 dependency slice, not a claim that the later complete KLS-integrated project has passed a fresh source rebuild.

## Dependency and permission scope

The selected 45-module MilmanPoincare closure is pinned to `chewisinho/cvx_body_lean@41678c03373f8d3ac9d95bab31bcc17022d85bec`: 29 authored modules and 16 separately attributed external modules. Private-project reuse does not grant public redistribution permission. Exact original/adapted hashes and retained notices are in [CvxBody/PROVENANCE.json](../../CvxBody/PROVENANCE.json) and [PRIVATE-REUSE.md](../../CvxBody/PRIVATE-REUSE.md).

The three shared external Model, Rademacher, and convex-measure modules are canonical definitions. The later KLS integration reuses them rather than creating duplicate carriers. Original upstream `autoImplicit=true` is confined to the CvxBody library; project adapters retain `autoImplicit=false`.

## Mathematical correspondence

- Needle existence constructs the probability-kernel disintegration from actual measurable nonnegative log-concave density, probability, first moment, and a set of strictly intermediate mass. Cheeger or a desired decomposition is not assumed.
- Needle-to-Cheeger uses a positive scale and an actual integrable 1-Lipschitz guide, with coefficient `1/(256*s)`. The uniform adapter supplies the square root of the actual optimal Poincaré constant and proves its positivity and finiteness.
- Median positive/negative parts have disjoint strict-sign derivative supports, including the zero derivative at the truncation minimum, so the L1 adapter does not double the coefficient.
- Compact smooth cutoffs equal one near the entire bounded closure and preserve function/derivative germs there. No extra compact-support or global-Lipschitz premise remains for the final ambient C1 class.
- Body endpoints retain all ambient locally Lipschitz functions, arbitrary inscribed-ball center, whole-body volume integrals, actual boundary distance, and actual weak-Sobolev optimal constants. The positive maximum inscribed radius and a maximizing center are constructed.
- The ordinary coefficient 256 gives explicit sufficient weighted coefficient 1036 and squared IPI coefficient 4293184. These witness the manuscript's universal constants; sharpness is not claimed.

The port preserves exported statements. One local continuous-linear-map identity in `RayShift` is proved by operator-level normalization instead of pointwise simplification; the precise compatibility change is recorded in the provenance.

Eight full importing examples and fourteen standard-only transitive reports passed. Final source-form S07/S08 endpoints have no reverse-Buser supplier, finite-CPI premise, restricted test class, or assumed maximum-radius attainment.
