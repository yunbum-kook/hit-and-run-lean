module
public import HitAndRun.Sobolev.TranslationIntegrals
public import HitAndRun.Sobolev.SmoothGraph
@[expose] public section
noncomputable section
namespace HitAndRun.Sobolev.BoundedOpenDomain
open MeasureTheory EllipticPdes EllipticPdes.H1Graph Set
open scoped RealInnerProductSpace
variable {n : ℕ} [NeZero n] (K : BoundedOpenDomain n) (c : EuclideanSpace ℝ (Fin n))

def translationL2 {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] :
    Lp F 2 ((K.translate c).ambient.restrict (K.translate c).carrier) →ₗᵢ[ℝ]
      Lp F 2 (K.ambient.restrict K.carrier) :=
  Lp.compMeasurePreservingₗᵢ ℝ (fun x => c + x) (K.translate_measurePreserving c)

theorem translationL2_ae {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Lp F 2 ((K.translate c).ambient.restrict (K.translate c).carrier)) :
    K.translationL2 c f =ᵐ[K.ambient.restrict K.carrier] fun x => f (c + x) :=
  Lp.coeFn_compMeasurePreserving f (K.translate_measurePreserving c)

def translationGraph (u : H1Graph (K.translate c).ambient (K.translate c).carrier) :
    H1Graph K.ambient K.carrier :=
  H1Graph.mk (K.translationL2 c (fnL u)) (K.translationL2 c (gradL u))

def translatedTest (φ : testFunctions K.carrier) : testFunctions (K.translate c).carrier :=
  ⟨fun x => (φ : EuclideanSpace ℝ (Fin n) → ℝ) (-c + x), (contDiff_of_mem φ.property).comp (contDiff_const.add contDiff_id),
    φ.property.2.1.comp_homeomorph (Homeomorph.addLeft (-c)), by
      change tsupport ((φ : EuclideanSpace ℝ (Fin n) → ℝ) ∘ (Homeomorph.addLeft (-c))) ⊆ _
      rw [tsupport_comp_eq_preimage (φ : EuclideanSpace ℝ (Fin n) → ℝ)
        (Homeomorph.addLeft (-c))]
      intro x hx
      have h := φ.property.2.2 hx
      exact ⟨-c + x, h, by simp⟩⟩

theorem translatedTest_fderiv (φ : testFunctions K.carrier) (x : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (K.translatedTest c φ : EuclideanSpace ℝ (Fin n) → ℝ) (c + x) =
      fderiv ℝ (φ : EuclideanSpace ℝ (Fin n) → ℝ) x := by
  have hd := ((contDiff_of_mem φ.property).differentiable (by simp) (-c + (c + x))).hasFDerivAt.comp
    (c + x) ((hasFDerivAt_id (c + x)).const_add (-c))
  simpa [translatedTest, Function.comp_def] using hd.fderiv

lemma constraint_integral (φ : testFunctions K.carrier) (v : EuclideanSpace ℝ (Fin n))
    (u : H1Graph K.ambient K.carrier) :
    ⟪constraintVec K.ambient K.carrier φ v, u⟫ =
      (∫ x, fderiv ℝ (φ : EuclideanSpace ℝ (Fin n) → ℝ) x v * fnL u x
        ∂K.ambient.restrict K.carrier) +
      ∫ x, (φ : EuclideanSpace ℝ (Fin n) → ℝ) x * ⟪v, gradL u x⟫
        ∂K.ambient.restrict K.carrier := by
  rw [inner_constraintVec, L2.inner_def, L2.inner_def]
  congr 1
  · apply integral_congr_ae
    filter_upwards [coeFn_partialCls (μ := K.ambient) φ v] with x hx
    simp [hx, Real.inner_apply, mul_comm]
  · apply integral_congr_ae
    filter_upwards [coeFn_smulCls (μ := K.ambient) φ v] with x hx
    simp [hx, inner_smul_left]

theorem translationGraph_mem_W12 (u : (K.translate c).H1) :
    K.translationGraph c u.val ∈ W12 K.ambient K.carrier := by
  rw [mem_W12_iff]
  intro φ v
  have h := (mem_W12_iff u.val).mp u.property (K.translatedTest c φ) v
  rw [(K.translate c).constraint_integral] at h
  rw [K.constraint_integral]
  have h1 : (∫ x, fderiv ℝ (φ : EuclideanSpace ℝ (Fin n) → ℝ) x v *
      fnL (K.translationGraph c u.val) x ∂K.ambient.restrict K.carrier) =
      ∫ x, fderiv ℝ (K.translatedTest c φ : EuclideanSpace ℝ (Fin n) → ℝ) x v * fnL u.val x
        ∂(K.translate c).ambient.restrict (K.translate c).carrier := by
    rw [← K.translate_integral c]
    apply integral_congr_ae
    filter_upwards [K.translationL2_ae c (fnL u.val)] with x hx
    simp only [translationGraph, fnL_mk, hx, K.translatedTest_fderiv]
  have h2 : (∫ x, (φ : EuclideanSpace ℝ (Fin n) → ℝ) x *
      ⟪v, gradL (K.translationGraph c u.val) x⟫ ∂K.ambient.restrict K.carrier) =
      ∫ x, (K.translatedTest c φ : EuclideanSpace ℝ (Fin n) → ℝ) x * ⟪v, gradL u.val x⟫
        ∂(K.translate c).ambient.restrict (K.translate c).carrier := by
    rw [← K.translate_integral c]
    apply integral_congr_ae
    filter_upwards [K.translationL2_ae c (gradL u.val)] with x hx
    simp [translationGraph, hx, translatedTest]
  rw [h1, h2]
  exact h

def translationH1 (u : (K.translate c).H1) : K.H1 :=
  ⟨K.translationGraph c u.val, K.translationGraph_mem_W12 c u⟩
end HitAndRun.Sobolev.BoundedOpenDomain
