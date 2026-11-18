import PowerConvexity.Calculus.ClassicalCMAJetsFromValues
import CHS.Calculus.AffinePullback

/-! # Transport of the CHS jet criterion through a fixed real isometry

The complex frame is transported with the isometry. The same physical
potentials and their actual derivatives occur on both sides. No nonlinear
change of domain is used and no invariance under such a change is asserted.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open Set Metric Filter
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus CHS.Analysis
variable {n : ℕ} {E T : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace T]

theorem realHessian_comp_linearIsometry
    (L : DeGiorgi.AmbientSpace (n+n) ≃ₗᵢ[ℝ] E) {u : E → ℝ}
    {x : DeGiorgi.AmbientSpace (n+n)} (hu : ContDiffAt ℝ 2 u (L x))
    (v w : DeGiorgi.AmbientSpace (n+n)) :
    realHessian (fun y => u (L y)) x v w = realHessian u (L x) (L v) (L w) := by
  simpa only [zero_add,ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv] using realHessian_comp_affine
    L.toContinuousLinearEquiv.toContinuousLinearMap 0 (x := x)
    (by simpa only [zero_add,ContinuousLinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toContinuousLinearEquiv] using hu) v w

theorem complexHessian_comp_linearIsometry
    (L : DeGiorgi.AmbientSpace (n+n) ≃ₗᵢ[ℝ] E) {u : E → ℝ}
    {x : DeGiorgi.AmbientSpace (n+n)} (hu : ContDiffAt ℝ 2 u (L x)) :
    complexHessian realDirections imagDirections (fun y => u (L y)) x =
      complexHessian (fun i => L (realDirections i)) (fun i => L (imagDirections i)) u (L x) := by
  simpa only [zero_add,ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv] using complexHessian_comp_affine
    L.toContinuousLinearEquiv.toContinuousLinearMap 0 (x := x)
    (by simpa only [zero_add,ContinuousLinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toContinuousLinearEquiv] using hu) realDirections imagDirections

theorem realHessian_family_continuousAt_of_values_CMA_isometric_bound
    (hn : 2 ≤ n) (L : DeGiorgi.AmbientSpace (n+n) ≃ₗᵢ[ℝ] E)
    {u : T → E → ℝ} {t₀ : T} {x₀ : E} {R M : ℝ} (hR : 0 < R) (hM : 0 ≤ M)
    (hval : ∀ y ∈ closedBall x₀ (3*R),
      ContinuousAt (fun p : T × E => u p.1 p.2) (t₀,y))
    (hdata : ∀ᶠ t in 𝓝 t₀,
      ContDiffOn ℝ 4 (u t) (ball x₀ (4*R)) ∧
      (∀ x ∈ ball x₀ (4*R),
        (complexHessian (fun i => L (realDirections i)) (fun i => L (imagDirections i)) (u t) x).det = 1) ∧
      (∀ x ∈ ball x₀ (4*R),
        (complexHessian (fun i => L (realDirections i)) (fun i => L (imagDirections i)) (u t) x).PosDef) ∧
      (∀ x ∈ ball x₀ (4*R), ‖realHessian (u t) x‖ ≤ M)) :
    ContinuousAt (fun p : T × E => fderiv ℝ (u p.1) p.2) (t₀,x₀) ∧
    ContinuousAt (fun p : T × E => realHessian (u p.1) p.2) (t₀,x₀) := by
  let v : T → DeGiorgi.AmbientSpace (n+n) → ℝ := fun t x => u t (L x)
  let z₀ := L.symm x₀
  have hball (r : ℝ) (x : DeGiorgi.AmbientSpace (n+n)) :
      x ∈ ball z₀ r ↔ L x ∈ ball x₀ r := by
    rw [mem_ball,mem_ball]
    simpa only [z₀,L.apply_symm_apply] using (show dist x (L.symm x₀) < r ↔
      dist (L x) (L (L.symm x₀)) < r by rw [L.dist_map])
  have hclosed (r : ℝ) (x : DeGiorgi.AmbientSpace (n+n)) :
      x ∈ closedBall z₀ r ↔ L x ∈ closedBall x₀ r := by
    rw [mem_closedBall,mem_closedBall]
    simpa only [z₀,L.apply_symm_apply] using (show dist x (L.symm x₀) ≤ r ↔
      dist (L x) (L (L.symm x₀)) ≤ r by rw [L.dist_map])
  have hvval (y : DeGiorgi.AmbientSpace (n+n)) (hy : y ∈ closedBall z₀ (3*R)) :
      ContinuousAt (fun p : T × DeGiorgi.AmbientSpace (n+n) => v p.1 p.2) (t₀,y) := by
    have hp : ContinuousAt (fun p : T × DeGiorgi.AmbientSpace (n+n) => (p.1,L p.2))
        (t₀,y) := by fun_prop
    simpa only [Function.comp_def,v] using
      (hval (L y) ((hclosed _ y).mp hy)).comp_of_eq hp rfl
  have hvdata : ∀ᶠ t in 𝓝 t₀,
      ContDiffOn ℝ 4 (v t) (ball z₀ (4*R)) ∧
      (∀ x ∈ ball z₀ (4*R), (complexHessian realDirections imagDirections (v t) x).det = 1) ∧
      (∀ x ∈ ball z₀ (4*R), (complexHessian realDirections imagDirections (v t) x).PosDef) ∧
      (∀ x ∈ ball z₀ (4*R), ∀ i j, |euclideanHessian (v t) x i j| ≤ M) := by
    filter_upwards [hdata] with t ht
    have hreg (x : DeGiorgi.AmbientSpace (n+n)) (hx : x ∈ ball z₀ (4*R)) :
        ContDiffAt ℝ 2 (u t) (L x) :=
      (ht.1.contDiffAt (isOpen_ball.mem_nhds ((hball _ x).mp hx))).of_le (by norm_num)
    refine ⟨ht.1.comp L.toContinuousLinearEquiv.contDiff.contDiffOn
      (fun x hx => (hball _ x).mp hx),?_,?_,?_⟩
    · intro x hx
      rw [complexHessian_comp_linearIsometry L (hreg x hx)]
      exact ht.2.1 _ ((hball _ x).mp hx)
    · intro x hx
      rw [complexHessian_comp_linearIsometry L (hreg x hx)]
      exact ht.2.2.1 _ ((hball _ x).mp hx)
    · intro x hx i j
      change |realHessian (fun y => u t (L y)) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)| ≤ M
      rw [realHessian_comp_linearIsometry L (hreg x hx)]
      have hh := (realHessian (u t) (L x)).le_opNorm₂
        (L (EuclideanSpace.single i 1)) (L (EuclideanSpace.single j 1))
      simpa only [L.norm_map,EuclideanSpace.norm_single,norm_one,mul_one,Real.norm_eq_abs] using
        hh.trans (by simpa using ht.2.2.2 _ ((hball _ x).mp hx))
  have hv := realHessian_family_continuousAt_of_values_CMA_entry_bound hn hR hM hvval hvdata
  let S := L.symm.toContinuousLinearEquiv.toContinuousLinearMap
  let C : (DeGiorgi.AmbientSpace (n+n) →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) :=
    (ContinuousLinearMap.compL ℝ E (DeGiorgi.AmbientSpace (n+n)) ℝ).flip S
  have hpre : ContinuousAt (fun p : T × E => (p.1,L.symm p.2)) (t₀,x₀) := by fun_prop
  have hDin : ContinuousAt (fun p : T × E => fderiv ℝ (v p.1) (L.symm p.2)) (t₀,x₀) := by
    simpa only [Function.comp_def,z₀] using hv.1.comp_of_eq hpre rfl
  have hHin : ContinuousAt (fun p : T × E => realHessian (v p.1) (L.symm p.2)) (t₀,x₀) := by
    simpa only [Function.comp_def,z₀] using hv.2.comp_of_eq hpre rfl
  have hD : ContinuousAt
      (fun p : T × E => (fderiv ℝ (v p.1) (L.symm p.2)).comp S) (t₀,x₀) :=
    C.continuous.continuousAt.comp hDin
  have hmap : Continuous (fun H : DeGiorgi.AmbientSpace (n+n) →L[ℝ]
      DeGiorgi.AmbientSpace (n+n) →L[ℝ] ℝ => C.comp (H.comp S)) :=
    (continuous_id.clm_comp_const S).const_clm_comp C
  have hH : ContinuousAt
      (fun p : T × E => C.comp ((realHessian (v p.1) (L.symm p.2)).comp S)) (t₀,x₀) :=
    hmap.continuousAt.comp hHin
  have hnear : ∀ᶠ p : T × E in 𝓝 (t₀,x₀), ContDiffAt ℝ 2 (u p.1) p.2 := by
    have htnear := (continuous_fst.continuousAt (x := (t₀,x₀))).tendsto.eventually hdata
    have hxnear : ∀ᶠ p : T × E in 𝓝 (t₀,x₀), p.2 ∈ ball x₀ (4*R) :=
      (continuous_snd.continuousAt (x := (t₀,x₀))).tendsto.eventually
        (isOpen_ball.mem_nhds (mem_ball_self (by positivity : 0 < 4*R)))
    filter_upwards [htnear,hxnear] with p ht hx
    exact (ht.1.contDiffAt (isOpen_ball.mem_nhds hx)).of_le (by norm_num)
  constructor
  · apply hD.congr_of_eventuallyEq
    filter_upwards [hnear] with p hp
    ext w
    have hp' : DifferentiableAt ℝ (u p.1) (L (L.symm p.2)) := by
      simpa only [L.apply_symm_apply] using hp.differentiableAt (by norm_num)
    have hder := (hp'.hasFDerivAt.comp (L.symm p.2)
      L.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt).fderiv
    simpa only [v,S,Function.comp_def,ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe,LinearIsometryEquiv.coe_toContinuousLinearEquiv,
      L.apply_symm_apply] using
      (congrArg (fun D : DeGiorgi.AmbientSpace (n+n) →L[ℝ] ℝ => D (L.symm w)) hder).symm
  · apply hH.congr_of_eventuallyEq
    filter_upwards [hnear] with p hp
    ext w z
    have hh := realHessian_comp_linearIsometry L
      (show ContDiffAt ℝ 2 (u p.1) (L (L.symm p.2)) by simpa only [L.apply_symm_apply] using hp)
      (L.symm w) (L.symm z)
    simpa only [v,C,S,ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply,
      ContinuousLinearMap.compL_apply,ContinuousLinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toContinuousLinearEquiv,L.apply_symm_apply] using hh.symm

end PowerConvexity
