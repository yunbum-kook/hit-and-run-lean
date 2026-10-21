# Affine covariance transport

This packet proves actual pushforward facts for the uniform measure on a bounded, nonempty open Euclidean domain. It does not postulate isotropy or increment source completion.

1. The linear image is an actual bounded open nonempty domain.
2. Haar pushforward is imported from Mathlib's determinant change of variables. Restriction to the image and positive finite normalization give the exact probability pushforward; the determinant factor cancels.
3. The actual vector mean transforms linearly. Mathlib's centered covariance bilinear form transforms by adjoints in both variables, yielding L Σ L* for the actual covariance operator.
4. Translation changes the mean and leaves centered covariance unchanged.
5. Composing translation by minus the true mean with the separately proved inverse-square-root linear equivalence gives an actual domain with mean zero and identity centered covariance.

This is preparation for any subsequently licensed isotropic analytic result. No reverse Buser or KLS theorem is assumed or proved by this transport packet. Original manuscript and dependency pins are unchanged.
