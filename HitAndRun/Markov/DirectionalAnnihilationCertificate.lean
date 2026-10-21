module
public import HitAndRun.Markov.DirectionalAnnihilationSobolev
public import HitAndRun.Markov.SphereCertificateMoments
@[expose] public section

namespace HitAndRun.Markov
open MeasureTheory Set EllipticPdes EllipticPdes.H1Graph HitAndRun.Sobolev HitAndRun.Geometry
variable {n : ℕ} [NeZero n] (K : BoundedOpenDomain n) (θ : UnitDirection n)

/-- Every actual zero-trace gradient has vanishing conditional directional derivative. -/
theorem gradient_directional_projection (w : gradientSpace K.ambient K.carrier) :
    conditionalProjection (directionalSigma_le θ)
      ((innerSL ℝ (θ : EuclideanSpace ℝ (Fin n))).compLpL 2
        (K.ambient.restrict K.carrier) (w : Lp (EuclideanSpace ℝ (Fin n)) 2
          (K.ambient.restrict K.carrier))) = 0 := by
  rcases w.property with ⟨u, hu⟩
  rw [← hu]
  exact h01_directional_projection K θ u

/-- The coordinate sum is the actual directional weak derivative, not a certificate premise. -/
theorem directional_weakPartial_sum (u : VectorField K.ambient K.carrier) (i : Fin n) :
    (∑ j, θ.val j • weakPartial u i j) =
      (innerSL ℝ (θ : EuclideanSpace ℝ (Fin n))).compLpL 2
        (K.ambient.restrict K.carrier) (u i : Lp (EuclideanSpace ℝ (Fin n)) 2
          (K.ambient.restrict K.carrier)) := by
  let B := (innerSL ℝ : EuclideanSpace ℝ (Fin n) →L[ℝ]
    EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ).compLpL₂ 2 (K.ambient.restrict K.carrier)
  have hb (v : EuclideanSpace ℝ (Fin n)) : B v
      (u i : Lp (EuclideanSpace ℝ (Fin n)) 2 (K.ambient.restrict K.carrier)) =
      (innerSL ℝ v).compLpL 2 (K.ambient.restrict K.carrier)
        (u i : Lp (EuclideanSpace ℝ (Fin n)) 2 (K.ambient.restrict K.carrier)) := by
    simp only [B, ContinuousLinearMap.compLpL₂_apply_apply]
    apply Lp.ext
    exact ((innerSL ℝ v).coeFn_compLp' _).trans ((innerSL ℝ v).coeFn_compLpL _).symm
  have he := congrArg (fun v => B v (u i : Lp (EuclideanSpace ℝ (Fin n)) 2
      (K.ambient.restrict K.carrier)))
    ((EuclideanSpace.basisFun (Fin n) ℝ).sum_repr (θ : EuclideanSpace ℝ (Fin n)))
  simpa only [map_sum, map_smul, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, EuclideanSpace.basisFun_repr, hb, weakPartial] using he

/-- The manuscript sphere certificate is annihilated by the actual perpendicular
conditional expectation. No annihilation assumption is supplied. -/
theorem sphereCertificate_directional_projection (u : VectorField K.ambient K.carrier) :
    conditionalProjection (directionalSigma_le θ) (sphereCertificate u θ) = 0 := by
  have hz (i : Fin n) : conditionalProjection (directionalSigma_le θ)
      (∑ j, θ.val j • weakPartial u i j) = 0 := by
    rw [directional_weakPartial_sum K θ u i]
    exact gradient_directional_projection K θ (u i)
  have he : sphereCertificate u θ =
      (n : ℝ) • ∑ i, θ.val i • (∑ j, θ.val j • weakPartial u i j) := by
    simp only [sphereCertificate, sphereHilbertQuadratic, Finset.smul_sum, smul_smul]
  have hz' (i : Fin n) : (condExpL2 ℝ ℝ (directionalSigma_le θ))
      (∑ j, θ.val j • weakPartial u i j) = 0 := Subtype.ext (hz i)
  have h : (condExpL2 ℝ ℝ (directionalSigma_le θ)) (sphereCertificate u θ) = 0 := by
    rw [he, map_smul, map_sum]
    simp only [map_smul, hz', smul_zero, Finset.sum_const_zero]
  exact congrArg Subtype.val h

end HitAndRun.Markov
