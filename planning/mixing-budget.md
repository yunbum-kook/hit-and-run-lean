# Integer-time accuracy convention

The submitted source Corollary 1.2 writes a logarithmic time sufficient for a
positive accuracy. For a finite initial chi-square M, the formal budget is zero
when M <= epsilon, including M = 0. Otherwise it is the natural ceiling of
log(M/epsilon)/(2 lambda), with the exact proven positive spectral lower bound
lambda. This explicitly resolves negative displayed times and log(0); it does
not modify the submitted manuscript bytes or claim a new rate.

Infinite initial chi-square remains a vacuous infinite upper bound at every
finite time, not a finite accuracy guarantee. Both actual non-lazy algorithms
are covered by the finite-CBA comparison rates. The full covariance/logarithm
source corollary remains pending its geometric rate substitution.
