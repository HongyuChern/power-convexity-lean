import PowerConvexity.Calculus.NormalizedPencilContractionGeneral

/-! # The complete actual normalized full-Q remainder in finite dimension

Normalization is imposed only at the evaluation point, after fixing the
frame. The constant depends explicitly on dimension, primitive actual jet
bounds, direction bounds and the least spectral gap. No sign is asserted
for the trace-minus-Frobenius quadratic form in dimension greater than two.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open scoped BigOperators ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus CHS.SchurContractionCore
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

noncomputable def normalizedFullQErrorCoefficientGeneral (n m : ℕ) (B δ : ℝ) : ℝ :=
  readingTableErrorCoefficientGeneral n*B^5+(n : ℝ)^2*B^2+10*(n : ℝ)^2*B^3+
    44*(n : ℝ)^2*(m : ℝ)*B^3/δ+2*(n : ℝ)^2*(m : ℝ)*B^3/δ^2

noncomputable def normalizedFullQExpressionGeneral (a b : ι → E) (u : E → ℝ)
    (x : E) (d : ι → ℝ) (i : ι) : ℂ :=
  (Complex.normSq (skewThirdHessian a b u i x).trace : ℂ)-
    (∑ p, ∑ s, (Complex.normSq (skewThirdHessian a b u i x p s) : ℂ))-
    2*∑ s ∈ Finset.univ.erase i,
      weightedSquare (complexHessian a b u x)⁻¹
        (fun p => dz (a p) (b p) (fun y => modifiedSchur a b u y s i) x)/(1-(d s : ℂ)^2)

private theorem absorb_two_nonnegative_errors {A C σ g : ℝ}
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hσ : 0 ≤ σ) (hg : 0 ≤ g) :
    A*σ+C*g ≤ (A+C)*(σ+g) := by
  nlinarith [mul_nonneg hA hg,mul_nonneg hC hσ]

theorem modifiedSigma_normalized_fullQ_error_general
    {u : E → ℝ} {U : Set E} (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U)
    (a b : ι → E) {ρ : ℂ} (hρ : ρ ≠ 0)
    (hdet : ∀ y ∈ U, (complexHessian a b u y).det = ρ)
    (hneg : ∀ y ∈ U, u y < 0)
    (hA : ∀ y ∈ U, (complexHessian a b u y).PosDef) {x : E} (hx : x ∈ U)
    (i : ι) (d : ι → ℝ) (hI : modifiedA a b u x = 1)
    (hD : modifiedB a b u x = Matrix.diagonal (fun j => (d j : ℂ)))
    {B δ : ℝ} (hB1 : 1 ≤ B) (hδ : 0 < δ)
    (hd0 : ∀ j, 0 ≤ d j) (hgap : ∀ j, j ≠ i → δ ≤ d i^2-d j^2)
    (hσ : 0 ≤ modifiedSigma a b u x) (hJ : NormalizedQJetBoundGeneral a b u x d i B) :
    ‖(∑ p, ∑ q, (complexHessian a b u x)⁻¹ q p*
      dz (a q) (-b q) (dz (a p) (b p) (fun y => (modifiedSigma a b u y : ℂ))) x)-
      normalizedFullQExpressionGeneral a b u x d i‖ ≤
    normalizedFullQErrorCoefficientGeneral (Fintype.card ι) (Fintype.card {j : ι // j ≠ i}) B δ*
      (modifiedSigma a b u x+‖fderiv ℝ (modifiedSigma a b u) x‖) := by
  let G := (complexHessian a b u x)⁻¹
  let W := skewThirdHessian a b u i x
  let D : Matrix ι ι ℂ := fun p s => modifiedCompensatedHessian a b u p x i s
  let τ : ℂ := (powerWeight (u x) : ℂ)*(complexGradient a b u x i-star (complexGradient a b u x i))
  let V := contactUpperVector W D τ d
  let H := contactLowerVector W D τ d
  let R : ι → ι → ℂ := fun s p => dz (a p) (b p) (fun y => modifiedSchur a b u y i s) x
  let C : ι → ι → ℂ := fun s p => dz (a p) (b p) (fun y => modifiedSchur a b u y s i) x
  let X : ι → ℂ := fun p => W p i+τ*(1 : Matrix ι ι ℂ) p i
  let κ : ι → ℂ := fun j => ((d i^2-d j^2 : ℝ) : ℂ)
  let μ : ι → ℂ := fun j => 1-(d j : ℂ)^2
  let n : ℝ := Fintype.card ι
  let m : ℝ := Fintype.card {j : ι // j ≠ i}
  let σ := modifiedSigma a b u x
  let g := ‖fderiv ℝ (modifiedSigma a b u) x‖
  let η := σ+g
  let L := ∑ p, ∑ q, G q p*dz (a q) (-b q)
    (dz (a p) (b p) (fun y => (modifiedSigma a b u y : ℂ))) x
  let LM := matrixL a b u (modifiedSchur a b u) x i i
  let F := typeIQuadratic G W+(Complex.normSq τ : ℂ)*G.trace-∑ s, weightedSquare G (fun p => D p s)
  let Sa := ∑ j : {j : ι // j ≠ i}, (weightedSquare G (R j)+weightedSquare G (C j))/κ j
  let Sm := ∑ j : {j : ι // j ≠ i}, (weightedSquare G (V j)+weightedSquare G (H j))/μ j
  let Q := contactFullQuadratic G W D τ d i
  let T0 := (Complex.normSq W.trace : ℂ)-(∑ p, ∑ s, (Complex.normSq (W p s) : ℂ))
  let TH := T0-2*∑ j : {j : ι // j ≠ i}, weightedSquare G (H j)/μ j
  let TC := T0-2*∑ j : {j : ι // j ≠ i}, weightedSquare G (C j)/μ j
  have hB : 0 ≤ B := by linarith
  have hn : 0 ≤ n := by dsimp [n]; positivity
  have hm : 0 ≤ m := by dsimp [m]; positivity
  have hσ0 : 0 ≤ σ := hσ
  have hg : 0 ≤ g := norm_nonneg _
  have hση : σ ≤ η := le_add_of_nonneg_right hg
  have hG : matrixEntryBoundGeneral G B := hJ.table.1
  have hgp : ∀ j, j ≠ i → d j^2 < d i^2 := by intro j hj; linarith [hgap j hj]
  have hj := modifiedSigma_normalized_jet hU hu a b hneg hA hx i d hI hD hgp
  have hσeq : σ = 1-d i^2 := hj.2.1
  have hd1 : ∀ j, d j ≤ 1 := by
    have hi : d i ≤ 1 := by nlinarith
    intro j
    by_cases hji : j=i
    · simpa [hji] using hi
    · have h := hgp j hji
      nlinarith [hd0 i,hd0 j]
  have hμ (j : {j : ι // j ≠ i}) : δ ≤ 1-d j^2 := by
    have h := hgap j j.property
    linarith
  have hR (s p : ι) : ‖R s p-V s p‖ ≤ B*σ :=
    modifiedSchur_row_normalized_error_bound_general hU hu a b hneg hA hx i d hI hD hgp
      (hd0 i) hσ s p hB (hJ.third p s)
  have hC (s p : ι) : ‖C s p-H s p‖ ≤ 6*B*σ :=
    modifiedSchur_column_normalized_error_bound_general hU hu a b hneg hA hx i d hI hD hgp
      hd0 hd1 hσ hB hJ s p
  have hRow (j : {j : ι // j ≠ i}) :
      ‖weightedSquare G (R j)/κ j-weightedSquare G (V j)/μ j‖ ≤
        (2*n^2*B^3/δ+n^2*B^3/δ^2)*σ := by
    have hb := weightedSquare_gap_replacement_bound_general G (R j) (V j)
      hB hB hB hσ0 hδ (hgap j j.property) (hμ j) (by linarith : (1-d j^2)-(d i^2-d j^2)=σ)
      hG (fun p => hJ.Mfirst p i j) (hJ.upper j) (hR j)
    convert hb using 1 <;> dsimp [κ,μ,n] <;> push_cast <;> ring
  have hCol (j : {j : ι // j ≠ i}) :
      ‖weightedSquare G (C j)/κ j-weightedSquare G (H j)/μ j‖ ≤
        (12*n^2*B^3/δ+n^2*B^3/δ^2)*σ := by
    have hb := weightedSquare_gap_replacement_bound_general G (C j) (H j)
      hB hB (by positivity : 0 ≤ 6*B) hσ0 hδ (hgap j j.property) (hμ j)
      (by linarith : (1-d j^2)-(d i^2-d j^2)=σ)
      hG (fun p => hJ.Mfirst p j i) (hJ.lower j) (hC j)
    convert hb using 1 <;> dsimp [κ,μ,n] <;> push_cast <;> ring
  have hPair (j : {j : ι // j ≠ i}) :
      ‖(weightedSquare G (R j)+weightedSquare G (C j))/κ j-
          (weightedSquare G (V j)+weightedSquare G (H j))/μ j‖ ≤
        (14*n^2*B^3/δ+2*n^2*B^3/δ^2)*σ := by
    rw [show (weightedSquare G (R j)+weightedSquare G (C j))/κ j-
        (weightedSquare G (V j)+weightedSquare G (H j))/μ j =
      (weightedSquare G (R j)/κ j-weightedSquare G (V j)/μ j)+
      (weightedSquare G (C j)/κ j-weightedSquare G (H j)/μ j) by ring]
    exact (norm_add_le _ _).trans ((add_le_add (hRow j) (hCol j)).trans_eq (by ring))
  have hS : ‖Sa-Sm‖ ≤ (m*(14*n^2*B^3/δ+2*n^2*B^3/δ^2))*η := by
    dsimp only [Sa,Sm]
    rw [← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ j : {j : ι // j ≠ i}, ‖(weightedSquare G (R j)+weightedSquare G (C j))/κ j-
          (weightedSquare G (V j)+weightedSquare G (H j))/μ j‖ := norm_sum_le _ _
      _ ≤ ∑ _j : {j : ι // j ≠ i}, (14*n^2*B^3/δ+2*n^2*B^3/δ^2)*σ :=
        Finset.sum_le_sum (fun j _ => hPair j)
      _ = (m*(14*n^2*B^3/δ+2*n^2*B^3/δ^2))*σ := by simp [m]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hση (by positivity)
  have hP : ‖L-(LM-Sa)‖ ≤ (n^2*B*(B+6*m*B^2/δ)+2*n^2*B^3)*η := by
    have hb := modifiedSigma_contraction_pencil_remainder_general hU hu a b hneg hA hx i d hI hD
      hB hδ hgap hσ hJ
    exact hb.trans (absorb_two_nonnegative_errors (by positivity) (by positivity) hσ0 hg)
  have hLM : ‖LM-F‖ ≤ (readingTableErrorCoefficientGeneral (Fintype.card ι)*B^5)*η := by
    apply (modifiedSchur_LM_normalized_error_general hU hu a b hρ hdet hneg hA hx d i hI hD
      hB1 hd0 hd1 hσeq hJ.table).trans
    exact mul_le_mul_of_nonneg_left hση (by unfold readingTableErrorCoefficientGeneral; positivity)
  have hQ : Q = F-Sm := by
    dsimp only [Sm]
    simp only [add_div,Finset.sum_add_distrib]
    rw [sum_complement_eq_erase (fun s => weightedSquare G (V s)/μ s) i,
      sum_complement_eq_erase (fun s => weightedSquare G (H s)/μ s) i]
    dsimp [Q,F,contactFullQuadratic,contactQuadratic,V,H,μ]
    ring
  have hLQ : ‖L-Q‖ ≤
      ((n^2*B*(B+6*m*B^2/δ)+2*n^2*B^3)+
        readingTableErrorCoefficientGeneral (Fintype.card ι)*B^5+
        m*(14*n^2*B^3/δ+2*n^2*B^3/δ^2))*η := by
    rw [hQ,show L-(F-Sm) = (L-(LM-Sa))+(LM-F)-(Sa-Sm) by ring]
    exact (norm_sub_le _ _).trans ((add_le_add (norm_add_le _ _) le_rfl).trans
      ((add_le_add (add_le_add hP hLM) hS).trans_eq (by ring)))
  have hDi (p : ι) : ‖D p i-X p‖ ≤ 3*B*σ+B*g := by
    have hb := modifiedCompensated_first_column_defect_norm_general hU hu a b hneg hA hx i d hI hD hgp
      (hd0 i) hσ p hB (hJ.compensated p i) (hJ.third p i) (hJ.Afirst p i i)
    apply hb.trans
    apply add_le_add le_rfl
    apply mul_le_mul_of_nonneg_right _ hg
    linarith [hJ.directionA p,hJ.directionB p]
  have hFirst : ‖weightedSquare G X-weightedSquare G (fun p => D p i)‖ ≤ (8*n^2*B^3)*η := by
    rw [norm_sub_rev]
    have hb := weightedSquare_difference_norm_le_general G (fun p => D p i) X hB hB
      (by positivity : 0 ≤ 3*B*σ+B*g) hG (fun p => hJ.compensated p i) hJ.column hDi
    apply hb.trans
    have hab := absorb_two_nonnegative_errors (A := 6*n^2*B^3) (C := 2*n^2*B^3)
      (by positivity) (by positivity) hσ0 hg
    convert hab using 1 <;> (try dsimp only [n,η]) <;> first | rfl | ring
  let r := normalizedRankOneVector (powerWeight (u x)) (complexGradient a b u x)
  have hGr : G = rankOneWeight r := originalHessian_inverse_eq_normalized_rankOne a b (hneg x hx) hI (hA x hx)
  have hu3 : ContDiffAt ℝ 3 u x := (hu.contDiffAt (hU.mem_nhds hx)).of_le (by norm_num)
  have ht := skewThirdHessian_trace_zero hu3 a b (Filter.Eventually.mono (hU.mem_nhds hx) hdet) i
  change (∑ p, ∑ q, G q p*W p q)=0 at ht
  rw [hGr] at ht
  have hμne (s : ι) (hs : s ≠ i) : 1-(d s : ℂ)^2 ≠ 0 := by
    have h := hδ.trans_le (hμ ⟨s,hs⟩)
    have h' : (1-d s^2 : ℝ) ≠ 0 := ne_of_gt h
    exact_mod_cast h'
  have hQE := contactFullQuadratic_defect_exact_general W D (skewThirdHessian_conjTranspose hu3 a b i)
    r τ d i hμne ht
  rw [← hGr,← sum_complement_eq_erase (fun s => weightedSquare G (H s)/μ s) i] at hQE
  change Q=TH+weightedSquare G X-weightedSquare G (fun p => D p i) at hQE
  have hQTH : ‖Q-TH‖ ≤ (8*n^2*B^3)*η := by
    rw [hQE]
    rw [show TH+weightedSquare G X-weightedSquare G (fun p => D p i)-TH =
      weightedSquare G X-weightedSquare G (fun p => D p i) by ring]
    exact hFirst
  have hHterm (j : {j : ι // j ≠ i}) :
      ‖(weightedSquare G (C j)-weightedSquare G (H j))/μ j‖ ≤ 12*n^2*B^3*σ/δ := by
    have hb := weightedSquare_difference_norm_le_general G (C j) (H j) hB hB
      (by positivity : 0 ≤ 6*B*σ) hG (fun p => hJ.Mfirst p j i) (hJ.lower j) (hC j)
    have hN : ‖μ j‖ = 1-d j^2 := by
      dsimp [μ]
      rw [show (1 : ℂ)-(d j : ℂ)^2 = ((1-d j^2 : ℝ) : ℂ) by push_cast; rfl,
        Complex.norm_real,Real.norm_eq_abs,abs_of_pos (hδ.trans_le (hμ j))]
    rw [norm_div,hN]
    apply div_le_div₀ (by positivity) _ hδ (hμ j)
    exact hb.trans_eq (by dsimp [n]; ring)
  have hTHTC : ‖TH-TC‖ ≤ (24*m*n^2*B^3/δ)*η := by
    have he : TH-TC = 2*∑ j : {j : ι // j ≠ i},
        (weightedSquare G (C j)-weightedSquare G (H j))/μ j := by
      dsimp [TH,TC]
      simp only [sub_div,Finset.sum_sub_distrib]
      ring
    rw [he,norm_mul]
    norm_num only [Complex.norm_ofNat]
    calc
      _ ≤ 2*∑ j : {j : ι // j ≠ i}, ‖(weightedSquare G (C j)-weightedSquare G (H j))/μ j‖ :=
        mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by norm_num)
      _ ≤ 2*∑ _j : {j : ι // j ≠ i}, 12*n^2*B^3*σ/δ := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact Finset.sum_le_sum (fun j _ => hHterm j)
      _ = (24*m*n^2*B^3/δ)*σ := by simp [m]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hση (by positivity)
  have hTC : TC = normalizedFullQExpressionGeneral a b u x d i := by
    dsimp only [TC]
    rw [sum_complement_eq_erase (fun s => weightedSquare G (C s)/μ s) i]
    rfl
  change ‖L-normalizedFullQExpressionGeneral a b u x d i‖ ≤ _
  rw [← hTC]
  calc
    _ ≤ ‖L-Q‖+‖Q-TC‖ := norm_sub_le_norm_sub_add_norm_sub L Q TC
    _ ≤ ‖L-Q‖+(‖Q-TH‖+‖TH-TC‖) := add_le_add le_rfl (norm_sub_le_norm_sub_add_norm_sub Q TH TC)
    _ ≤ (((n^2*B*(B+6*m*B^2/δ)+2*n^2*B^3)+
        readingTableErrorCoefficientGeneral (Fintype.card ι)*B^5+
        m*(14*n^2*B^3/δ+2*n^2*B^3/δ^2))*η)+
        ((8*n^2*B^3)*η+(24*m*n^2*B^3/δ)*η) := add_le_add hLQ (add_le_add hQTH hTHTC)
    _ = _ := by dsimp [normalizedFullQErrorCoefficientGeneral,n,m,η,σ,g]; ring

end PowerConvexity
