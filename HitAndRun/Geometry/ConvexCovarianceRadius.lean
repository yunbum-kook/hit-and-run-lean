module
public import HitAndRun.Geometry.CovariancePoincare
public import HitAndRun.Geometry.WeightedPoincareGeometry
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
@[expose] public section
noncomputable section
namespace HitAndRun.Geometry
open MeasureTheory Set
open scoped Pointwise
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Affine contraction of a convex body: the exact Haar Jacobian bounds every
nonnegative integrable observable, without assumptions on the body's centroid. -/
theorem convex_affine_homothety_integral_le (μ : Measure E) [μ.IsAddHaarMeasure]
    {K : Set E} (hc : Convex ℝ K) {x : E} (hx : x ∈ K)
    {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    {f : E → ℝ} (hf : IntegrableOn f K μ) (hpos : ∀ y, 0 ≤ f y) :
    (a ^ Module.finrank ℝ E) *
      (∫ z in K, f ((1-a) • x + a • z) ∂μ) ≤ ∫ z in K, f z ∂μ := by
  have hsub : (fun y => (1-a) • x + y) '' (a • K) ⊆ K := by
    rintro y ⟨w, ⟨z, hz, rfl⟩, rfl⟩
    exact hc hx hz (sub_nonneg.mpr ha1) ha.le (by ring)
  have hi := setIntegral_mono_set hf (Filter.Eventually.of_forall hpos)
    (Filter.Eventually.of_forall hsub)
  rw [(measurePreserving_add_left μ ((1-a) • x)).setIntegral_image_emb
    (measurableEmbedding_addLeft _) f (a • K)] at hi
  rw [Measure.setIntegral_comp_smul_of_pos μ (fun z => f ((1-a) • x + z)) K ha,
    smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ ha.ne'), one_mul]
  exact hi
end HitAndRun.Geometry

namespace HitAndRun.Sobolev.BoundedOpenDomain
open MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {n : ℕ} [NeZero n]

def barycenter (K : BoundedOpenDomain n) : EuclideanSpace ℝ (Fin n) :=
  ∫ z, z ∂uniformMeasure K.carrier

def centeredProjection (K : BoundedOpenDomain n) (v z : EuclideanSpace ℝ (Fin n)) : ℝ :=
  inner ℝ v (z - K.barycenter)

theorem centeredProjection_memLp (K : BoundedOpenDomain n)
    (v : EuclideanSpace ℝ (Fin n)) :
    MemLp (K.centeredProjection v) 2 (uniformMeasure K.carrier) := by
  letI := uniformMeasure_isProbabilityMeasure K.isOpen K.nonempty K.isBounded
  exact (K.uniform_memLp_id.sub (memLp_const K.barycenter)).const_inner v

theorem integral_centeredProjection (K : BoundedOpenDomain n)
    (v : EuclideanSpace ℝ (Fin n)) :
    (∫ z, K.centeredProjection v z ∂uniformMeasure K.carrier) = 0 := by
  letI := uniformMeasure_isProbabilityMeasure K.isOpen K.nonempty K.isBounded
  have hi := K.uniform_memLp_id.integrable (by norm_num)
  simp only [centeredProjection, inner_sub_right]
  rw [integral_sub (hi.const_inner v) (integrable_const _)]
  have he : (∫ z, inner ℝ v z ∂uniformMeasure K.carrier) = inner ℝ v K.barycenter := integral_inner hi v
  rw [he]
  simp

theorem integral_centeredProjection_sq (K : BoundedOpenDomain n)
    (v : EuclideanSpace ℝ (Fin n)) :
    (∫ z, K.centeredProjection v z ^ 2 ∂uniformMeasure K.carrier) =
      inner ℝ (K.centeredCovarianceOperator v) v := by
  letI := uniformMeasure_isProbabilityMeasure K.isOpen K.nonempty K.isBounded
  rw [K.centeredCovarianceOperator_inner, covarianceBilin_apply K.uniform_memLp_id]
  simp only [centeredProjection, barycenter, pow_two, id_eq]

theorem integral_centeredProjection_affine_sq (K : BoundedOpenDomain n)
    (v x : EuclideanSpace ℝ (Fin n)) (a : ℝ) :
    (∫ z, K.centeredProjection v ((1-a) • x + a • z) ^ 2 ∂uniformMeasure K.carrier) =
      (1-a)^2 * K.centeredProjection v x ^ 2 +
        a^2 * inner ℝ (K.centeredCovarianceOperator v) v := by
  letI := uniformMeasure_isProbabilityMeasure K.isOpen K.nonempty K.isBounded
  have hi := (K.centeredProjection_memLp v).integrable (by norm_num)
  have hs := (K.centeredProjection_memLp v).integrable_sq
  have he : ∀ z, K.centeredProjection v ((1-a) • x + a • z) ^ 2 =
      (1-a)^2 * K.centeredProjection v x ^ 2 +
      ((2*(1-a)*a*K.centeredProjection v x) * K.centeredProjection v z +
      a^2 * K.centeredProjection v z ^ 2) := by
    intro z
    simp only [centeredProjection, inner_sub_right, inner_add_right, inner_smul_right]
    ring
  simp_rw [he]
  rw [integral_add (f := fun _ => (1-a)^2 * K.centeredProjection v x ^ 2)
      (g := fun z => (2*(1-a)*a*K.centeredProjection v x) * K.centeredProjection v z + a^2 * K.centeredProjection v z ^ 2)
      (integrable_const _) ((hi.const_mul _).add (hs.const_mul _)),
    integral_add (f := fun z => (2*(1-a)*a*K.centeredProjection v x) * K.centeredProjection v z)
      (g := fun z => a^2 * K.centeredProjection v z ^ 2)
      (hi.const_mul _) (hs.const_mul _)]
  simp only [integral_const_mul, K.integral_centeredProjection, K.integral_centeredProjection_sq]
  simp

/-- A centered linear projection at any body point is controlled by its actual
second moment. The coefficient follows from a half-volume contraction. -/
theorem centeredProjection_sq_le (K : BoundedOpenDomain n) (hc : Convex ℝ K.carrier)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ K.carrier)
    (v : EuclideanSpace ℝ (Fin n)) :
    K.centeredProjection v x ^ 2 ≤
      8 * (n : ℝ)^2 * inner ℝ (K.centeredCovarianceOperator v) v := by
  letI := uniformMeasure_isProbabilityMeasure K.isOpen K.nonempty K.isBounded
  let a : ℝ := 1 - 1 / (2 * (n : ℝ))
  have hn : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (NeZero.one_le : 1 ≤ n)
  have ha : 0 < a := by
    dsimp [a]
    have ht : 1 / (2 * (n : ℝ)) ≤ 1/2 := by
      apply (div_le_iff₀ (by positivity)).mpr
      linarith
    linarith
  have ha1 : a ≤ 1 := by
    dsimp [a]
    exact sub_le_self _ (by positivity)
  have hp : (1/2 : ℝ) ≤ a^n := Geometry.contraction_power_lower n (NeZero.pos n)
  have hi : IntegrableOn (fun z => K.centeredProjection v z ^ 2) K.carrier K.ambient := by
    rw [IntegrableOn, K.measure_eq_uniform]
    exact (K.centeredProjection_memLp v).integrable_sq
  have hh := Geometry.convex_affine_homothety_integral_le K.ambient hc hx ha ha1 hi
    (fun z => sq_nonneg (K.centeredProjection v z))
  simp only [finrank_euclideanSpace, Fintype.card_fin, K.measure_eq_uniform] at hh
  rw [K.integral_centeredProjection_affine_sq, K.integral_centeredProjection_sq] at hh
  have hq := K.centeredCovarianceOperator_positive.inner_nonneg_left v
  have hd : 0 ≤ (1-a)^2 * K.centeredProjection v x ^ 2 := mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hhalf : (1/2 : ℝ) * ((1-a)^2 * K.centeredProjection v x ^ 2) ≤
      inner ℝ (K.centeredCovarianceOperator v) v := by
    calc
      _ ≤ a^n * ((1-a)^2 * K.centeredProjection v x ^ 2) := mul_le_mul_of_nonneg_right hp hd
      _ ≤ a^n * ((1-a)^2 * K.centeredProjection v x ^ 2 +
          a^2 * inner ℝ (K.centeredCovarianceOperator v) v) :=
        mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (mul_nonneg (sq_nonneg _) hq))
          (pow_nonneg ha.le _)
      _ ≤ _ := hh
  have he : (8 * (n : ℝ)^2) * ((1/2 : ℝ) * ((1-a)^2 * K.centeredProjection v x ^ 2)) =
      K.centeredProjection v x ^ 2 := by
    dsimp [a]
    field_simp
    <;> ring
  simpa only [he] using mul_le_mul_of_nonneg_left hhalf (by positivity : 0 ≤ 8 * (n : ℝ)^2)

/-- Squared centered radius, proved directly from actual covariance. -/
theorem norm_sub_barycenter_sq_le (K : BoundedOpenDomain n) (hc : Convex ℝ K.carrier)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ K.carrier) :
    ‖x - K.barycenter‖^2 ≤ 8 * (n : ℝ)^2 * ‖K.centeredCovarianceOperator‖ := by
  let v := x - K.barycenter
  have hs := K.centeredProjection_sq_le hc hx v
  have hq : inner ℝ (K.centeredCovarianceOperator v) v ≤
      ‖K.centeredCovarianceOperator‖ * ‖v‖^2 := by
    calc
      _ ≤ ‖K.centeredCovarianceOperator v‖ * ‖v‖ := real_inner_le_norm _ _
      _ ≤ (‖K.centeredCovarianceOperator‖ * ‖v‖) * ‖v‖ :=
        mul_le_mul_of_nonneg_right (K.centeredCovarianceOperator.le_opNorm v) (norm_nonneg _)
      _ = _ := by ring
  have hp : K.centeredProjection v x = ‖v‖^2 := by
    exact real_inner_self_eq_norm_sq v
  rw [hp] at hs
  have hh := hs.trans (mul_le_mul_of_nonneg_left hq (by positivity : 0 ≤ 8 * (n : ℝ)^2))
  by_cases hv : v = 0
  · simp only [v] at hv
    simp only [hv, norm_zero, zero_pow (by decide : (2:ℕ) ≠ 0)]
    positivity
  · have hpos : 0 < ‖v‖^2 := sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hv)
    change ‖v‖^2 ≤ _
    apply (mul_le_mul_iff_of_pos_right hpos).mp
    nlinarith [hh]

/-- A convenient explicit centered radius bound, including zero covariance. -/
theorem norm_sub_barycenter_le (K : BoundedOpenDomain n) (hc : Convex ℝ K.carrier)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ K.carrier) :
    ‖x - K.barycenter‖ ≤ 3 * (n : ℝ) * Real.sqrt ‖K.centeredCovarianceOperator‖ := by
  have h := K.norm_sub_barycenter_sq_le hc hx
  have hs := Real.sq_sqrt (norm_nonneg K.centeredCovarianceOperator)
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hr := Real.sqrt_nonneg ‖K.centeredCovarianceOperator‖
  have hprod : (3 * (n : ℝ) * Real.sqrt ‖K.centeredCovarianceOperator‖)^2 =
      9 * (n : ℝ)^2 * ‖K.centeredCovarianceOperator‖ := by rw [mul_pow, mul_pow, hs]; ring
  have hnon : 0 ≤ (n : ℝ)^2 * ‖K.centeredCovarianceOperator‖ := by positivity
  nlinarith [mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 3) hn) hr]

/-- If the origin belongs to the body, its full outer radius is controlled by
centered covariance. The origin need not be the barycenter. -/
theorem norm_le_covariance_radius (K : BoundedOpenDomain n) (hc : Convex ℝ K.carrier)
    (hzero : (0 : EuclideanSpace ℝ (Fin n)) ∈ K.carrier)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ K.carrier) :
    ‖x‖ ≤ 6 * (n : ℝ) * Real.sqrt ‖K.centeredCovarianceOperator‖ := by
  have hx' := K.norm_sub_barycenter_le hc hx
  have hzero' := K.norm_sub_barycenter_le hc hzero
  simp only [zero_sub, norm_neg] at hzero'
  have ht : ‖x‖ ≤ ‖x - K.barycenter‖ + ‖K.barycenter‖ := by
    simpa only [sub_add_cancel] using norm_add_le (x - K.barycenter) K.barycenter
  linarith

/-- A fully independent covariance-to-PI substitution for the outer radius. -/
theorem norm_le_poincare_radius (K : BoundedOpenDomain n) (hc : Convex ℝ K.carrier)
    (hzero : (0 : EuclideanSpace ℝ (Fin n)) ∈ K.carrier)
    (hfin : K.poincareConstant < ⊤)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ K.carrier) :
    ‖x‖ ≤ 6 * (n : ℝ) * Real.sqrt K.poincareConstant.toReal := by
  exact (K.norm_le_covariance_radius hc hzero hx).trans
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (K.norm_centeredCovarianceOperator_le hfin))
      (by positivity))
end HitAndRun.Sobolev.BoundedOpenDomain
