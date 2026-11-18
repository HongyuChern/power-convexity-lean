import PowerConvexity.Algebra.FullMatrixDefectBoundTwo
import PowerConvexity.Calculus.NormalizedSpectralJetBoundsTwo
import PowerConvexity.Calculus.NormalizedWeight

/-! # An actual Schur diagonal estimate uniform as both eigenvalues vanish

The derivative term is a full Schur-row derivative bound, not a scalar trace
or minimum-eigenvalue derivative. Closing that distinction is still required.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open scoped BigOperators ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem modifiedSchur_LM_normalized_trace_row_bound_two {u : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U) (a b : Fin 2 → E)
    {ρ : ℂ} (hρ : ρ ≠ 0)
    (hdet : ∀ y ∈ U, (complexHessian a b u y).det = ρ)
    (hneg : ∀ y ∈ U, u y < 0)
    (hpos : ∀ y ∈ U, (complexHessian a b u y).PosDef)
    {x : E} (hx : x ∈ U) (d : Fin 2 → ℝ)
    (hI : modifiedA a b u x = 1)
    (hD : modifiedB a b u x = Matrix.diagonal (fun i => (d i:ℂ)))
    (hd : ∀ i, 0 ≤ d i ∧ d i ≤ 1)
    {B g : ℝ} (hB : 1 ≤ B) (hg : 0 ≤ g)
    (hjets : normalizedSpectralJetBoundTwo a b u x B)
    (hgrad : ∀ p s, ‖dz (a p) (b p) (fun y => modifiedSchur a b u y 0 s) x‖ ≤ g) :
    (matrixL a b u (modifiedSchur a b u) x 0 0).re ≤
      (768*B^5+96*B^3)*(2-(d 0)^2-(d 1)^2)+48*B^2*g := by
  obtain ⟨hbase,hW,hDb,hτ,hR,_,_,_,_⟩ := hjets
  let W := skewThirdHessian a b u 0 x
  let D : Matrix (Fin 2) (Fin 2) ℂ := fun p s => modifiedCompensatedHessian a b u p x 0 s
  let τ : ℂ := (powerWeight (u x):ℂ)*(complexGradient a b u x 0-star (complexGradient a b u x 0))
  let G := (complexHessian a b u x)⁻¹
  let r := normalizedRankOneVector (powerWeight (u x)) (complexGradient a b u x)
  let S := 2-(d 0)^2-(d 1)^2
  have hB0 : 0 ≤ B := by linarith
  have hμ (i : Fin 2) : 0 ≤ 1-(d i)^2 := (one_sub_takagi_le_sigma (hd i).1 (hd i).2 rfl).2.2
  have hμS (i : Fin 2) : 1-(d i)^2 ≤ S := by
    fin_cases i
    · change 1-(d 0)^2 ≤ 2-(d 0)^2-(d 1)^2
      linarith [hμ 1]
    · change 1-(d 1)^2 ≤ 2-(d 0)^2-(d 1)^2
      linarith [hμ 0]
  have hS : 0 ≤ S := (hμ 0).trans (hμS 0)
  have hu4 := hu.contDiffAt (hU.mem_nhds hx)
  have hu3 : ContDiffAt ℝ 3 u x := hu4.of_le (by norm_num)
  have hG : G = rankOneWeightTwo r :=
    originalHessian_inverse_eq_normalized_rankOne a b (hneg x hx) hI (hpos x hx)
  have htr := skewThirdHessian_trace_zero hu3 a b (Filter.Eventually.mono (hU.mem_nhds hx) hdet) 0
  change (∑ p,∑ q,G q p*W p q) = 0 at htr
  rw [hG] at htr
  have hdef (p s : Fin 2) :
      ‖D p s-(W p s+τ*(1 : Matrix (Fin 2) (Fin 2) ℂ) p s)‖ ≤ 2*B*S+g := by
    have he := modifiedSchur_dz_normalized_remainder hu4 (hneg x hx) a b (hpos x hx) d hI hD 0 s p
    have hh := normalized_full_entry_defect_bound (hd 0).1 (hd 0).2 (hd s).1 (hd s).2
      rfl rfl hB0 (D p s) (normalizedThirdRemainder a b u 0 x p s)
      (W p s+τ*(1 : Matrix (Fin 2) (Fin 2) ℂ) p s)
      (dz (a p) (b p) (fun y => modifiedSchur a b u y 0 s) x)
      (hDb p s) (hR p s) (hgrad p s) he
    refine hh.trans ?_
    nlinarith [mul_le_mul_of_nonneg_left (hμS 0) hB0,
      mul_le_mul_of_nonneg_left (hμS s) hB0]
  have hF := typeI_full_column_defect_bound_two W D (skewThirdHessian_conjTranspose hu3 a b 0)
    r τ htr hB0 (show 0 ≤ 3*B by positivity) (show 0 ≤ 2*B*S+g by positivity)
    (fun p q => by rw [← hG]; exact hbase.1 q p)
    (fun p s => (contactShiftedColumn_entry_bound_two hB0 W τ hW hτ p s).trans (by linarith))
    (fun p s => (hDb p s).trans (by linarith)) hdef
  rw [← hG] at hF
  have herror := modifiedSchur_LM_normalized_error_two hU hu a b hρ hdet hneg hpos hx d hI hD
    hB (hd 0).1 (hd 0).2 (hd 1).1 (hd 1).2 rfl hbase
  have herr := (Complex.re_le_norm _).trans herror
  rw [Complex.sub_re] at herr
  have hsmall := mul_le_mul_of_nonneg_left (hμS 0) (show 0 ≤ 768*B^5 by positivity)
  dsimp only [W,D,τ,G] at hF
  dsimp only [S] at hF hsmall
  nlinarith only [hF,herr,hsmall]

end PowerConvexity
