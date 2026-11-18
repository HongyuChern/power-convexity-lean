import PowerConvexity.Calculus.NormalizedFrameJetEstimatesGeneral

/-! # A common actual jet bound for every pointwise normalizing frame

The neighborhood constant is derived from C4 regularity in the original
fixed frame. Each Q is fixed while differentiating the transformed fields;
no continuity or differentiability of a choice y ↦ Q(y) is assumed.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open scoped BigOperators ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def normalizedFrameJetBoundConstantGeneral (n : ℕ) (K : ℝ) : ℝ :=
  1+K+(n : ℝ)^2*K^3+3*((n : ℝ)*K^2)+(n : ℝ)^4*K^5+
    16*((n : ℝ)^3*K^4)+8*K*((n : ℝ)*K^2)

theorem normalizedQJetBoundGeneral_of_fixedFrame
    {u : E → ℝ} {U : Set E} (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U)
    (hneg : ∀ y ∈ U, u y < 0) (a b : ι → E)
    (hpos : ∀ y ∈ U, (complexHessian a b u y).PosDef) {x : E} (hx : x ∈ U)
    (Q : Matrix ι ι ℂ) (hQ : IsUnit Q.det) (d : ι → ℝ) (i : ι)
    (hI : modifiedA (complexFrameReal Q a b) (complexFrameImag Q a b) u x = 1)
    (hD : modifiedB (complexFrameReal Q a b) (complexFrameImag Q a b) u x =
      Matrix.diagonal (fun j => (d j : ℂ)))
    (hd0 : ∀ j, 0 ≤ d j) (hd1 : ∀ j, d j ≤ 1) {K : ℝ} (hK : 1 ≤ K)
    (hjets : fixedFrameJetBoundGeneral a b u x K) :
    NormalizedQJetBoundGeneral (complexFrameReal Q a b) (complexFrameImag Q a b) u x d i
      (normalizedFrameJetBoundConstantGeneral (Fintype.card ι) K) := by
  have hu0 := hu.contDiffAt (hU.mem_nhds hx)
  have hx0 := hneg x hx
  obtain ⟨hAm,hiAm,hG,hh,hg,hp,hm,hJ,ha,hb⟩ := hjets
  have hK0 : 0 ≤ K := by linarith
  let n : ℝ := Fintype.card ι
  let T := n^3*K^4
  let R := n*K^2
  let S := n^2*K^3
  let J := n^4*K^5
  let C := 1+K+S+3*R+J+16*T+8*K*R
  have hn : 0 ≤ n := by dsimp [n]; positivity
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hJJ : 0 ≤ J := by dsimp [J]; positivity
  have hKR : 0 ≤ K*R := mul_nonneg hK0 hR
  have hcT : T ≤ C := by dsimp [C]; linarith
  have hcS : S ≤ C := by dsimp [C]; linarith
  have hcR : R ≤ C := by dsimp [C]; linarith
  have hcK : K ≤ C := by dsimp [C]; linarith
  have hcJ : J ≤ C := by dsimp [C]; linarith
  have hc2 : 2*T ≤ C := by dsimp [C]; linarith
  have hc4 : 4*T ≤ C := by dsimp [C]; linarith
  have hcN : T+K*R ≤ C := by dsimp [C]; linarith
  have hcV : 4*T+2*K*R ≤ C := by dsimp [C]; linarith
  have hcX : 2*T+2*K*R ≤ C := by dsimp [C]; linarith
  have hcDir : 2*R ≤ C := by dsimp [C]; linarith
  have hN : Q*modifiedA a b u x*Q.conjTranspose = 1 := by
    rw [← modifiedA_complexFrame (hu0.of_le (by norm_num)) hx0 Q a b]
    exact hI
  obtain ⟨hQb,hQib⟩ := normalizingFrame_entry_bounds_general Q (modifiedA a b u x) hQ hN hK hAm hiAm
  let a' := complexFrameReal Q a b
  let b' := complexFrameImag Q a b
  have hp' : ∀ k p, matrixEntryBoundGeneral
      (matrixDZ (a' p) (b' p) (powerHessianFieldsGeneral a' b' u k) x) T :=
    fun k p => (transformedPowerHessian_first_bounds_general hu0 hx0 Q a b hK0 hQb hp hm k p).1
  have hm' : ∀ k p, matrixEntryBoundGeneral
      (matrixDZ (a' p) (-b' p) (powerHessianFieldsGeneral a' b' u k) x) T :=
    fun k p => (transformedPowerHessian_first_bounds_general hu0 hx0 Q a b hK0 hQb hp hm k p).2
  have hg' (j : ι) : ‖complexGradient a' b' u x j‖ ≤ R := by
    rw [complexGradient_complexFrame]
    convert matrix_mulVec_entry_bound_general hK0 hQb hg j using 1 <;> dsimp [R,n] <;> ring
  have hG' : matrixEntryBoundGeneral (complexHessian a' b' u x)⁻¹ S :=
    complexHessian_inverse_transformed_bound_general (hu0.of_le (by norm_num)) Q a b hK0 hQib hG
  have hAp (p : ι) : matrixEntryBoundGeneral (matrixDZ (a' p) (b' p) (modifiedA a' b' u) x) T := by
    simpa [powerHessianFieldsGeneral] using hp' 2 p
  have hAn (p : ι) : matrixEntryBoundGeneral (matrixDZ (a' p) (-b' p) (modifiedA a' b' u) x) T := by
    simpa [powerHessianFieldsGeneral] using hm' 2 p
  have hBp (p : ι) : matrixEntryBoundGeneral (matrixDZ (a' p) (b' p) (modifiedB a' b' u) x) T := by
    simpa [powerHessianFieldsGeneral] using hp' 3 p
  have hBn (p : ι) : matrixEntryBoundGeneral (matrixDZ (a' p) (-b' p) (modifiedB a' b' u) x) T := by
    simpa [powerHessianFieldsGeneral] using hm' 3 p
  have hP (p : ι) : matrixEntryBoundGeneral (matrixDZ (a' p) (-b' p) (pureHessian a' b' u) x) T := by
    simpa [powerHessianFieldsGeneral] using hm' 1 p
  have hdN (j : ι) : ‖(d j : ℂ)‖ ≤ 1 := by
    simpa [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hd0 j)] using hd1 j
  have hstarB (p l m : ι) : ‖dz (a' p) (b' p) (fun y => star (modifiedB a' b' u y l m)) x‖ ≤ T := by
    rw [dz_star_reverse,norm_star]
    exact hBn p l m
  have hComp (p l m : ι) : ‖modifiedCompensatedHessian a' b' u p x l m‖ ≤ 2*T := by
    rw [modifiedCompensated_normalized_entry (hu0.of_le (by norm_num)) a' b' d hI hD]
    calc
      _ ≤ ‖dz (a' p) (b' p) (fun y => modifiedB a' b' u y l m) x‖+
          ‖(d l : ℂ)*dz (a' p) (b' p) (fun y => modifiedA a' b' u y m l) x‖ := norm_sub_le _ _
      _ ≤ T+1*T := by
        rw [norm_mul]
        exact add_le_add (hBp p l m) (mul_le_mul (hdN l) (hAp p m l) (norm_nonneg _) (by norm_num))
      _ = _ := by ring
  have hpos' : ∀ y ∈ U, (complexHessian a' b' u y).PosDef := by
    intro y hy
    exact (complexHessian_posDef_complexFrame_iff
      ((hu.contDiffAt (hU.mem_nhds hy)).of_le (by norm_num)) Q hQ a b).mpr (hpos y hy)
  have hMp (p l m : ι) : ‖dz (a' p) (b' p) (fun y => modifiedSchur a' b' u y l m) x‖ ≤ 4*T := by
    rw [modifiedSchur_dz_normalized_direct hu0 hx0 a' b' (hpos' x hx) d hI hD]
    calc
      _ ≤ (‖dz (a' p) (b' p) (fun y => modifiedA a' b' u y l m) x‖+
          ‖(d m : ℂ)*modifiedCompensatedHessian a' b' u p x l m‖)+
          ‖(d l : ℂ)*dz (a' p) (b' p) (fun y => star (modifiedB a' b' u y l m)) x‖ :=
        (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
      _ ≤ (T+1*(2*T))+1*T := by
        simp only [norm_mul]
        exact add_le_add (add_le_add (hAp p l m)
          (mul_le_mul (hdN m) (hComp p l m) (norm_nonneg _) (by norm_num)))
          (mul_le_mul (hdN l) (hstarB p l m) (norm_nonneg _) (by norm_num))
      _ = _ := by ring
  have hW : matrixEntryBoundGeneral (skewThirdHessian a' b' u i x) (2*T) := by
    have hp0 : matrixEntryBoundGeneral (matrixDZ (a' i) (b' i) (complexHessian a' b' u) x) T := by
      simpa [powerHessianFieldsGeneral] using hp' 0 i
    have hm0 : matrixEntryBoundGeneral (matrixDZ (a' i) (-b' i) (complexHessian a' b' u) x) T := by
      simpa [powerHessianFieldsGeneral] using hm' 0 i
    simpa [skewThirdHessian,two_mul] using matrixEntryBoundGeneral_sub hp0 hm0
  let τ := (powerWeight (u x) : ℂ)*(complexGradient a' b' u x i-star (complexGradient a' b' u x i))
  have hτ : ‖τ‖ ≤ 2*K*R := by
    dsimp only [τ]
    calc
      _ ≤ ‖(powerWeight (u x) : ℂ)‖*(‖complexGradient a' b' u x i‖+‖star (complexGradient a' b' u x i)‖) := by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (norm_sub_le _ _) (norm_nonneg _)
      _ ≤ K*(R+R) := by
        rw [norm_star]
        exact mul_le_mul hh (add_le_add (hg' i) (hg' i)) (by positivity) hK0
      _ = _ := by ring
  have hX (p s : ι) : ‖skewThirdHessian a' b' u i x p s+τ*(1 : Matrix ι ι ℂ) p s‖ ≤ 2*T+2*K*R := by
    exact (norm_add_le _ _).trans (add_le_add (hW p s) (by
      rw [norm_mul]
      simpa using mul_le_mul hτ (matrixEntryBoundGeneral_one p s) (norm_nonneg _) (by positivity : 0 ≤ 2*K*R)))
  change NormalizedQJetBoundGeneral a' b' u x d i C
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · refine ⟨matrixEntryBoundGeneral_mono hG' hcS,hh.trans hcK,
      (fun j => (hg' j).trans hcR),?_,?_,?_,?_⟩
    · intro p; exact matrixEntryBoundGeneral_mono (hP p) hcT
    · intro p
      rw [matrixDZ_map_star,neg_neg]
      apply matrixEntryBoundGeneral_mono (matrixEntryBoundGeneral_map_star ?_) hcT
      simpa [powerHessianFieldsGeneral] using hp' 0 p
    · intro p
      rw [matrixDZ_map_star]
      exact matrixEntryBoundGeneral_mono (matrixEntryBoundGeneral_map_star (hP p)) hcT
    · intro p
      rw [matrixDZ_map_star]
      apply matrixEntryBoundGeneral_mono (matrixEntryBoundGeneral_map_star ?_) hcT
      simpa [powerHessianFieldsGeneral] using hm' 0 p
  · intro p l m; exact (hMp p l m).trans hc4
  · intro p l m
    rw [modifiedSchur_dzbar_eq_star_swap_general hU hu a' b' hneg hpos' hx,norm_star]
    exact (hMp p m l).trans hc4
  · intro p l m; exact (hAp p l m).trans hcT
  · intro p l m; exact (hAn p l m).trans hcT
  · intro p q
    exact (transformedModifiedA_second_bound_general hu0 hx0 Q a b hK0 hQb hJ p q i i).trans hcJ
  · intro p s; exact (hComp p i s).trans hc2
  · intro p s
    unfold normalizedThirdRemainder
    rw [dz_star_reverse]
    apply (norm_add_le _ _).trans
    have hterm : ‖(powerWeight (u x) : ℂ)*star (complexGradient a' b' u x i)*(1 : Matrix ι ι ℂ) p s‖ ≤ K*R := by
      simp only [norm_mul,norm_star]
      exact (mul_le_mul (mul_le_mul hh (hg' i) (norm_nonneg _) hK0)
        (matrixEntryBoundGeneral_one p s) (norm_nonneg _) hKR).trans_eq (by ring)
    have hp0 : ‖star (dz (a' p) (-b' p) (fun y => pureHessian a' b' u y i s) x)‖ ≤ T := by
      rw [norm_star]; exact hP p i s
    exact (add_le_add hp0 hterm).trans hcN
  · intro p s; exact (hstarB p i s).trans hcT
  · intro s p
    change ‖skewThirdHessian a' b' u i x p s+τ*(1 : Matrix ι ι ℂ) p s-
      (d s : ℂ)*modifiedCompensatedHessian a' b' u p x i s‖ ≤ C
    apply (norm_sub_le _ _).trans
    have hdD : ‖(d s : ℂ)*modifiedCompensatedHessian a' b' u p x i s‖ ≤ 2*T := by
      rw [norm_mul]
      simpa using mul_le_mul (hdN s) (hComp p i s) (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    exact (add_le_add (hX p s) hdD).trans (by linarith [hcV])
  · intro s p
    change ‖(d s : ℂ)*(skewThirdHessian a' b' u i x p s+τ*(1 : Matrix ι ι ℂ) p s)-
      modifiedCompensatedHessian a' b' u p x i s‖ ≤ C
    apply (norm_sub_le _ _).trans
    have hdX : ‖(d s : ℂ)*(skewThirdHessian a' b' u i x p s+τ*(1 : Matrix ι ι ℂ) p s)‖ ≤ 2*T+2*K*R := by
      rw [norm_mul]
      simpa using mul_le_mul (hdN s) (hX p s) (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    exact (add_le_add hdX (hComp p i s)).trans (by linarith [hcV])
  · intro p; exact (hX p i).trans hcX
  · intro p
    have hh := (complexFrame_norm_bound_general a b hK0 hK0 hQb ha hb p).1
    apply hh.trans
    change 2*n*K*K ≤ C
    nlinarith [hcDir]
  · intro p
    have hh := (complexFrame_norm_bound_general a b hK0 hK0 hQb ha hb p).2
    apply hh.trans
    change 2*n*K*K ≤ C
    nlinarith [hcDir]

theorem normalizedQJetBoundGeneral_eventually
    {u : E → ℝ} {U : Set E} (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U)
    (hneg : ∀ y ∈ U, u y < 0) (a b : ι → E)
    (hpos : ∀ y ∈ U, (complexHessian a b u y).PosDef) {x : E} (hx : x ∈ U) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ᶠ y in 𝓝 x, ∀ (Q : Matrix ι ι ℂ), IsUnit Q.det →
      ∀ (d : ι → ℝ) (i : ι),
      modifiedA (complexFrameReal Q a b) (complexFrameImag Q a b) u y = 1 →
      modifiedB (complexFrameReal Q a b) (complexFrameImag Q a b) u y = Matrix.diagonal (fun j => (d j : ℂ)) →
      (∀ j, 0 ≤ d j) → (∀ j, d j ≤ 1) →
      NormalizedQJetBoundGeneral (complexFrameReal Q a b) (complexFrameImag Q a b) u y d i B := by
  obtain ⟨K,hK,hjets⟩ := fixedFrameJetBoundGeneral_eventually
    (hu.contDiffAt (hU.mem_nhds hx)) (hneg x hx) a b (hpos x hx)
  refine ⟨normalizedFrameJetBoundConstantGeneral (Fintype.card ι) K,?_,?_⟩
  · have hK0 : 0 ≤ K := by linarith
    unfold normalizedFrameJetBoundConstantGeneral
    have hrest : 0 ≤ K+(Fintype.card ι : ℝ)^2*K^3+3*((Fintype.card ι : ℝ)*K^2)+
        (Fintype.card ι : ℝ)^4*K^5+16*((Fintype.card ι : ℝ)^3*K^4)+
        8*K*((Fintype.card ι : ℝ)*K^2) := by positivity
    linarith
  · filter_upwards [hjets,hU.mem_nhds hx] with y hy hyU
    intro Q hQ d i hI hD hd0 hd1
    exact normalizedQJetBoundGeneral_of_fixedFrame hU hu hneg a b hpos hyU Q hQ d i hI hD hd0 hd1 hK hy

end PowerConvexity
