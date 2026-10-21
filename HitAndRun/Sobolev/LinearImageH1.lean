module
public import HitAndRun.Geometry.LinearImageDomain
public import HitAndRun.Sobolev.TranslationH1
@[expose] public section
noncomputable section
namespace HitAndRun.Sobolev.BoundedOpenDomain
open MeasureTheory EllipticPdes EllipticPdes.H1Graph Set
open scoped RealInnerProductSpace
variable {n : ℕ} [NeZero n] (K : BoundedOpenDomain n)
  (L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))

theorem linearImage_restrict_measurePreserving :
    MeasurePreserving L (K.ambient.restrict K.carrier)
      ((K.linearImage L).ambient.restrict (K.linearImage L).carrier) := by
  rw [K.measure_eq_uniform, (K.linearImage L).measure_eq_uniform]
  exact K.linearImage_measurePreserving L

def linearImageL2 {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] :
    Lp F 2 ((K.linearImage L).ambient.restrict (K.linearImage L).carrier) →ₗᵢ[ℝ]
      Lp F 2 (K.ambient.restrict K.carrier) :=
  Lp.compMeasurePreservingₗᵢ ℝ L (K.linearImage_restrict_measurePreserving L)

theorem linearImageL2_ae {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Lp F 2 ((K.linearImage L).ambient.restrict (K.linearImage L).carrier)) :
    K.linearImageL2 L f =ᵐ[K.ambient.restrict K.carrier] fun x => f (L x) :=
  Lp.coeFn_compMeasurePreserving f (K.linearImage_restrict_measurePreserving L)

def linearImageGraph (u : H1Graph (K.linearImage L).ambient (K.linearImage L).carrier) :
    H1Graph K.ambient K.carrier :=
  H1Graph.mk (K.linearImageL2 L (fnL u))
    (L.toContinuousLinearMap.adjoint.compLp (K.linearImageL2 L (gradL u)))

def linearImageTest (φ : testFunctions K.carrier) : testFunctions (K.linearImage L).carrier :=
  ⟨fun x => (φ : EuclideanSpace ℝ (Fin n) → ℝ) (L.symm x),
    (contDiff_of_mem φ.property).comp L.symm.contDiff,
    φ.property.2.1.comp_homeomorph L.symm.toHomeomorph, by
      change tsupport ((φ : EuclideanSpace ℝ (Fin n) → ℝ) ∘ L.symm.toHomeomorph) ⊆ _
      rw [tsupport_comp_eq_preimage (φ : EuclideanSpace ℝ (Fin n) → ℝ) L.symm.toHomeomorph]
      intro x hx
      exact ⟨L.symm x, φ.property.2.2 hx, L.apply_symm_apply x⟩⟩

theorem linearImageTest_fderiv (φ : testFunctions K.carrier)
    (x v : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (K.linearImageTest L φ : EuclideanSpace ℝ (Fin n) → ℝ) (L x) (L v) =
      fderiv ℝ (φ : EuclideanSpace ℝ (Fin n) → ℝ) x v := by
  have hd := ((contDiff_of_mem φ.property).differentiable (by simp) (L.symm (L x))).hasFDerivAt.comp
    (L x) (L.symm.hasFDerivAt)
  simpa [linearImageTest, Function.comp_def] using congrArg (fun A => A (L v)) hd.fderiv

theorem linearImageGraph_mem_W12 (u : (K.linearImage L).H1) :
    K.linearImageGraph L u.val ∈ W12 K.ambient K.carrier := by
  rw [mem_W12_iff]
  intro φ v
  have h := (mem_W12_iff u.val).mp u.property (K.linearImageTest L φ) (L v)
  rw [(K.linearImage L).constraint_integral] at h
  rw [K.constraint_integral]
  have hi (f : EuclideanSpace ℝ (Fin n) → ℝ) :
      (∫ x, f (L x) ∂K.ambient.restrict K.carrier) =
      ∫ x, f x ∂(K.linearImage L).ambient.restrict (K.linearImage L).carrier :=
    (K.linearImage_restrict_measurePreserving L).integral_comp L.toHomeomorph.measurableEmbedding f
  have h1 : (∫ x, fderiv ℝ (φ : EuclideanSpace ℝ (Fin n) → ℝ) x v *
      fnL (K.linearImageGraph L u.val) x ∂K.ambient.restrict K.carrier) =
      ∫ x, fderiv ℝ (K.linearImageTest L φ : EuclideanSpace ℝ (Fin n) → ℝ) x (L v) * fnL u.val x
        ∂(K.linearImage L).ambient.restrict (K.linearImage L).carrier := by
    rw [← hi]
    apply integral_congr_ae
    filter_upwards [K.linearImageL2_ae L (fnL u.val)] with x hx
    simp only [linearImageGraph, fnL_mk, hx, K.linearImageTest_fderiv]
  have h2 : (∫ x, (φ : EuclideanSpace ℝ (Fin n) → ℝ) x *
      ⟪v, gradL (K.linearImageGraph L u.val) x⟫ ∂K.ambient.restrict K.carrier) =
      ∫ x, (K.linearImageTest L φ : EuclideanSpace ℝ (Fin n) → ℝ) x * ⟪L v, gradL u.val x⟫
        ∂(K.linearImage L).ambient.restrict (K.linearImage L).carrier := by
    rw [← hi]
    apply integral_congr_ae
    filter_upwards [K.linearImageL2_ae L (gradL u.val),
      L.toContinuousLinearMap.adjoint.coeFn_compLp (K.linearImageL2 L (gradL u.val))] with x hx hy
    simp only [linearImageGraph, gradL_mk, hy, Function.comp_apply, hx,
      ContinuousLinearMap.adjoint_inner_right, linearImageTest, L.symm_apply_apply]
    rfl
  rw [h1, h2]
  exact h

def linearImageH1 (u : (K.linearImage L).H1) : K.H1 :=
  ⟨K.linearImageGraph L u.val, K.linearImageGraph_mem_W12 L u⟩
end HitAndRun.Sobolev.BoundedOpenDomain
