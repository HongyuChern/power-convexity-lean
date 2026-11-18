import PowerConvexity.Calculus.FixedFrameLocalBoundsTwo
import PowerConvexity.Calculus.NormalizedSpectralJetBoundsTwo

/-! # One uniform polynomial bound for every normalized frame at a point -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem transformedPowerHessian_first_bounds {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 4 u x) (hx : u x < 0) (Q : Matrix (Fin 2) (Fin 2) ℂ)
    (a b : Fin 2 → E) {K : ℝ} (hK : 0 ≤ K) (hQ : matrixEntryBoundTwo Q K)
    (hp : ∀ k p, matrixEntryBoundTwo (matrixDZ (a p) (b p) (powerHessianFieldsTwo a b u k) x) K)
    (hm : ∀ k p, matrixEntryBoundTwo (matrixDZ (a p) (-b p) (powerHessianFieldsTwo a b u k) x) K)
    (k : Fin 4) (p : Fin 2) :
    matrixEntryBoundTwo (matrixDZ (complexFrameReal Q a b p) (complexFrameImag Q a b p)
      (powerHessianFieldsTwo (complexFrameReal Q a b) (complexFrameImag Q a b) u k) x) (8*K^4) ∧
    matrixEntryBoundTwo (matrixDZ (complexFrameReal Q a b p) (-complexFrameImag Q a b p)
      (powerHessianFieldsTwo (complexFrameReal Q a b) (complexFrameImag Q a b) u k) x) (8*K^4) := by
  have hF : MatrixDifferentiableAt (powerHessianFieldsTwo a b u k) x :=
    fun i j => (powerHessianFieldsTwo_contDiffAt_two hu hx a b k i j).differentiableAt (by norm_num)
  have he := powerHessianFieldsTwo_eventually_complexFrame hu hx Q a b k
  have hR := powerHessianRightFrameTwo_entry_bound hQ k
  constructor
  · convert matrixDZ_frame_sandwich_entry_bound_two hF Q Q (powerHessianRightFrameTwo Q k)
      a b he hK hK hQ hQ hR (hp k) p using 1 <;> ring
  · convert matrixDZbar_frame_sandwich_entry_bound_two hF Q Q (powerHessianRightFrameTwo Q k)
      a b he hK hK hQ hQ hR (hm k) p using 1 <;> ring

theorem transformedModifiedA_second_bound {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 4 u x) (hx : u x < 0) (Q : Matrix (Fin 2) (Fin 2) ℂ)
    (a b : Fin 2 → E) {K : ℝ} (hK : 0 ≤ K) (hQ : matrixEntryBoundTwo Q K)
    (hJ : ∀ p q, matrixEntryBoundTwo (matrixDZ (a q) (-b q) (matrixDZ (a p) (b p) (modifiedA a b u)) x) K)
    (p q : Fin 2) :
    matrixEntryBoundTwo (matrixDZ (complexFrameReal Q a b q) (-complexFrameImag Q a b q)
      (matrixDZ (complexFrameReal Q a b p) (complexFrameImag Q a b p)
        (modifiedA (complexFrameReal Q a b) (complexFrameImag Q a b) u)) x) (16*K^5) := by
  have he : modifiedA (complexFrameReal Q a b) (complexFrameImag Q a b) u =ᶠ[𝓝 x]
      (fun y => Q*modifiedA a b u y*Q.conjTranspose) := by
    simpa [powerHessianFieldsTwo,powerHessianRightFrameTwo] using
      powerHessianFieldsTwo_eventually_complexFrame hu hx Q a b 2
  convert matrixDZ_mixed_frame_sandwich_entry_bound_two (modifiedA_contDiffAt_two hu hx a b)
    Q Q Q.conjTranspose a b he hK hK hQ hQ (matrixEntryBoundTwo_conjTranspose hQ) hJ p q using 1 <;> ring

theorem complexHessian_inverse_transformed_bound {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (Q : Matrix (Fin 2) (Fin 2) ℂ) (a b : Fin 2 → E)
    {K : ℝ} (hK : 0 ≤ K) (hQi : matrixEntryBoundTwo Q⁻¹ K)
    (hG : matrixEntryBoundTwo (complexHessian a b u x)⁻¹ K) :
    matrixEntryBoundTwo (complexHessian (complexFrameReal Q a b) (complexFrameImag Q a b) u x)⁻¹ (4*K^3) := by
  rw [complexHessian_complexFrame hu]
  simp only [Matrix.mul_inv_rev,← Matrix.conjTranspose_nonsing_inv]
  rw [← Matrix.mul_assoc]
  convert matrixEntryBoundTwo_sandwich hK hK (matrixEntryBoundTwo_conjTranspose hQi) hQi hG using 1 <;> ring

theorem normalizedSpectralJetBoundTwo_of_fixedFrame {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 4 u x) (hx : u x < 0) (a b : Fin 2 → E)
    (Q : Matrix (Fin 2) (Fin 2) ℂ) (hQ : IsUnit Q.det) (d : Fin 2 → ℝ)
    (hI : modifiedA (complexFrameReal Q a b) (complexFrameImag Q a b) u x = 1)
    (hD : modifiedB (complexFrameReal Q a b) (complexFrameImag Q a b) u x =
      Matrix.diagonal (fun i => (d i:ℂ)))
    (hd0 : 0 ≤ d 0) (hd1 : d 0 ≤ 1) {K : ℝ} (hK : 1 ≤ K)
    (hjets : fixedFrameJetBoundTwo a b u x K) :
    normalizedSpectralJetBoundTwo (complexFrameReal Q a b) (complexFrameImag Q a b) u x (32*K^5) := by
  obtain ⟨hAm,hiAm,hG,hh,hg,hp,hm,hJ,ha,hb⟩ := hjets
  have hK0 : 0 ≤ K := by linarith
  have hpow (n : ℕ) (hn : n ≤ 5) : K^n ≤ K^5 := pow_le_pow_right₀ hK hn
  have h1 : K ≤ K^5 := by simpa using hpow 1 (by decide)
  have h2 := hpow 2 (by decide)
  have h3 := hpow 3 (by decide)
  have h4 := hpow 4 (by decide)
  have h5 : 0 ≤ K^5 := pow_nonneg hK0 5
  have h8 : 8*K^4 ≤ 32*K^5 := by nlinarith
  have h16 : 16*K^4 ≤ 32*K^5 := by nlinarith
  have hN : Q*modifiedA a b u x*Q.conjTranspose = 1 := by
    rw [← modifiedA_complexFrame (hu.of_le (by norm_num)) hx Q a b]
    exact hI
  obtain ⟨hQb,hQib⟩ := normalizingFrame_entry_bounds_two Q (modifiedA a b u x) hQ hN hK hAm hiAm
  let a' := complexFrameReal Q a b
  let b' := complexFrameImag Q a b
  have hfirst := transformedPowerHessian_first_bounds hu hx Q a b hK0 hQb hp hm
  have hplus (k : Fin 4) (p : Fin 2) := (hfirst k p).1
  have hminus (k : Fin 4) (p : Fin 2) := (hfirst k p).2
  have hg' (i : Fin 2) : ‖complexGradient a' b' u x i‖ ≤ 2*K^2 := by
    rw [complexGradient_complexFrame]
    convert matrix_mulVec_entry_bound_two hK0 hQb hg i using 1 <;> ring
  have hG' : matrixEntryBoundTwo (complexHessian a' b' u x)⁻¹ (4*K^3) :=
    complexHessian_inverse_transformed_bound (hu.of_le (by norm_num)) Q a b hK0 hQib hG
  have hAp (p : Fin 2) : matrixEntryBoundTwo (matrixDZ (a' p) (b' p) (modifiedA a' b' u) x) (8*K^4) := by
    simpa [powerHessianFieldsTwo] using hplus 2 p
  have hBp (p : Fin 2) : matrixEntryBoundTwo (matrixDZ (a' p) (b' p) (modifiedB a' b' u) x) (8*K^4) := by
    simpa [powerHessianFieldsTwo] using hplus 3 p
  have hBm (p : Fin 2) : matrixEntryBoundTwo (matrixDZ (a' p) (-b' p) (modifiedB a' b' u) x) (8*K^4) := by
    simpa [powerHessianFieldsTwo] using hminus 3 p
  have hP (p : Fin 2) : matrixEntryBoundTwo (matrixDZ (a' p) (-b' p) (pureHessian a' b' u) x) (8*K^4) := by
    simpa [powerHessianFieldsTwo] using hminus 1 p
  have hdN : ‖(d 0:ℂ)‖ ≤ 1 := by simpa [Complex.norm_real,abs_of_nonneg hd0] using hd1
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · refine ⟨matrixEntryBoundTwo_mono hG' (by nlinarith),hh.trans (by nlinarith),
      (fun i => (hg' i).trans (by nlinarith)),?_,?_,?_,?_⟩
    · intro p; exact matrixEntryBoundTwo_mono (hP p) h8
    · intro p
      rw [matrixDZ_map_star,neg_neg]
      apply matrixEntryBoundTwo_mono (matrixEntryBoundTwo_map_star ?_) h8
      simpa [powerHessianFieldsTwo] using hplus 0 p
    · intro p
      rw [matrixDZ_map_star]
      exact matrixEntryBoundTwo_mono (matrixEntryBoundTwo_map_star (hP p)) h8
    · intro p
      rw [matrixDZ_map_star]
      apply matrixEntryBoundTwo_mono (matrixEntryBoundTwo_map_star ?_) h8
      simpa [powerHessianFieldsTwo] using hminus 0 p
  · unfold skewThirdHessian
    have hp0 : matrixEntryBoundTwo (matrixDZ (a' 0) (b' 0) (complexHessian a' b' u) x) (8*K^4) := by
      simpa [powerHessianFieldsTwo] using hplus 0 0
    have hm0 : matrixEntryBoundTwo (matrixDZ (a' 0) (-b' 0) (complexHessian a' b' u) x) (8*K^4) := by
      simpa [powerHessianFieldsTwo] using hminus 0 0
    exact matrixEntryBoundTwo_mono (matrixEntryBoundTwo_sub hp0 hm0) (by nlinarith)
  · intro p s
    rw [modifiedCompensated_normalized_entry (hu.of_le (by norm_num)) a' b' d hI hD]
    calc
      _ ≤ ‖dz (a' p) (b' p) (fun y => modifiedB a' b' u y 0 s) x‖+
        ‖(d 0:ℂ)*dz (a' p) (b' p) (fun y => modifiedA a' b' u y s 0) x‖ := norm_sub_le _ _
      _ ≤ 8*K^4+1*(8*K^4) := by rw [norm_mul]; gcongr <;> first | exact hBp p 0 s | exact hAp p s 0
      _ ≤ _ := by nlinarith
  · calc
      _ ≤ ‖(powerWeight (u x):ℂ)‖*(‖complexGradient a' b' u x 0‖+‖star (complexGradient a' b' u x 0)‖) := by
        rw [norm_mul]; gcongr; exact norm_sub_le _ _
      _ ≤ K*(2*K^2+2*K^2) := by rw [norm_star]; gcongr <;> exact hg' 0
      _ ≤ _ := by nlinarith
  · intro p s
    unfold normalizedThirdRemainder
    rw [dz_star_reverse]
    calc
      _ ≤ ‖star (dz (a' p) (-b' p) (fun y => pureHessian a' b' u y 0 s) x)‖+
        ‖(powerWeight (u x):ℂ)*star (complexGradient a' b' u x 0)*(1 : Matrix (Fin 2) (Fin 2) ℂ) p s‖ := norm_add_le _ _
      _ ≤ 8*K^4+K*(2*K^2)*1 := by
        simp only [norm_star,norm_mul]
        gcongr <;> first | exact hP p 0 s | exact hg' 0 | exact matrixEntryBoundTwo_one p s
      _ ≤ _ := by nlinarith
  · intro p i j; exact (hAp p i j).trans h8
  · intro p i j
    rw [dz_star_reverse,norm_star]
    exact (hBm p i j).trans h8
  · intro p q
    exact (transformedModifiedA_second_bound hu hx Q a b hK0 hQb hJ p q 0 0).trans (by nlinarith)
  · intro p
    obtain ⟨hr,hi⟩ := complexFrame_norm_bound_two a b hK0 hK0 hQb ha hb p
    change (‖complexFrameReal Q a b p‖+‖complexFrameImag Q a b p‖)/2 ≤ _
    nlinarith

end PowerConvexity
