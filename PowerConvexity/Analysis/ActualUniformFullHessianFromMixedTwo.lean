import PowerConvexity.Analysis.ActualUniformNormalDeterminantModulusTwo
import Mathlib.Analysis.InnerProductSpace.Basic

/-! # Full actual Hessian modulus from tangent covectors and the determinant

The real normal component is recovered from the same two by two complex
determinant. All remaining entries are estimated by the actual tangential
covector modulus; no full Hessian continuity is assumed in the conclusion.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
open Set Matrix
open scoped ComplexOrder InnerProductSpace
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
local notation "Bilin" => E →L[ℝ] E →L[ℝ] ℝ

theorem actual_tangent_projection_norm_four {N : E} (hN : ‖N‖=1) (v : E) :
    inner ℝ N (v-inner ℝ N v • N)=0 ∧ ‖v-inner ℝ N v • N‖ ≤ ‖v‖ := by
  constructor
  · rw [inner_sub_right,inner_smul_right,real_inner_self_eq_norm_sq,hN,one_pow,mul_one,sub_self]
  · have hh := norm_sub_sq_real v (inner ℝ N v • N)
    have hcomm : inner ℝ v N=inner ℝ N v := real_inner_comm _ _
    simp only [inner_smul_right,hcomm,norm_smul,Real.norm_eq_abs,hN,mul_one,sq_abs] at hh
    nlinarith [sq_nonneg (inner ℝ N v),norm_nonneg (v-inner ℝ N v • N),norm_nonneg v]

theorem actual_symmetric_bilinear_norm_from_tangent_and_normal_four
    {N : E} (hN : ‖N‖=1) (H : Bilin) (hsym : ∀ v w, H v w=H w v)
    {eps eta : ℝ} (heps : 0 ≤ eps) (heta : 0 ≤ eta)
    (hmixed : ∀ w : E, inner ℝ N w=0 → ‖H.flip w‖ ≤ eps*‖w‖)
    (hnormal : |H N N| ≤ eta) : ‖H‖ ≤ 2*eps+eta := by
  have hn (v : E) : |inner ℝ N v| ≤ ‖v‖ := by
    simpa only [hN,one_mul] using abs_real_inner_le_norm N v
  have hNv (v : E) : |H v N| ≤ (eps+eta)*‖v‖ := by
    let p := v-inner ℝ N v • N
    have hp := actual_tangent_projection_norm_four hN v
    have he : H v N=H N p+inner ℝ N v*H N N := by
      rw [hsym v N]
      dsimp only [p]
      simp only [map_sub,map_smul,smul_eq_mul]
      ring
    have hHp : |H N p| ≤ eps*‖p‖ := by
      have hh := (H.flip p).le_opNorm N
      change |H N p| ≤ _ at hh
      rw [hN,mul_one] at hh
      exact hh.trans (hmixed p hp.1)
    rw [he]
    calc
      _ ≤ |H N p|+|inner ℝ N v*H N N| := abs_add_le _ _
      _ = |H N p|+|inner ℝ N v| * |H N N| := by rw [abs_mul]
      _ ≤ eps*‖v‖+‖v‖*eta := add_le_add
        (hHp.trans (mul_le_mul_of_nonneg_left hp.2 heps))
        (mul_le_mul (hn v) hnormal (abs_nonneg _) (norm_nonneg _))
      _ = _ := by ring
  apply ContinuousLinearMap.opNorm_le_bound₂ _ (by positivity)
  intro v w
  let p := w-inner ℝ N w • N
  have hp := actual_tangent_projection_norm_four hN w
  have he : H v w=H v p+inner ℝ N w*H v N := by
    dsimp only [p]
    simp only [map_sub,map_smul,smul_eq_mul]
    ring
  have hHp : |H v p| ≤ (eps*‖w‖)*‖v‖ := by
    exact ((H.flip p).le_opNorm v).trans (mul_le_mul_of_nonneg_right
      ((hmixed p hp.1).trans (mul_le_mul_of_nonneg_left hp.2 heps)) (norm_nonneg _))
  change |H v w| ≤ _
  rw [he]
  calc
    _ ≤ |H v p|+|inner ℝ N w*H v N| := abs_add_le _ _
    _ = |H v p|+|inner ℝ N w| * |H v N| := by rw [abs_mul]
    _ ≤ (eps*‖w‖)*‖v‖+‖w‖*((eps+eta)*‖v‖) :=
      add_le_add hHp (mul_le_mul (hn w) (hNv v) (abs_nonneg _) (norm_nonneg _))
    _ = _ := by ring

theorem actual_jet_complex_entry_of_four_bounds_two
    (a b : Fin 2 → E) (H : Bilin) (i j : Fin 2) {M : ℝ}
    (h1 : |H (a i) (a j)| ≤ M) (h2 : |H (b i) (b j)| ≤ M)
    (h3 : |H (a i) (b j)| ≤ M) (h4 : |H (b i) (a j)| ≤ M) :
    ‖jetComplexHessian a b H i j‖ ≤ M := by
  have hsum : ‖((H (a i) (a j) : ℂ)+(H (b i) (b j) : ℂ))+
      Complex.I*((H (a i) (b j) : ℂ)-(H (b i) (a j) : ℂ))‖ ≤ 4*M := by
    apply (norm_add_le _ _).trans
    have hfirst : ‖(H (a i) (a j) : ℂ)+(H (b i) (b j) : ℂ)‖ ≤ M+M :=
      (norm_add_le _ _).trans (by simpa only [Complex.norm_real,Real.norm_eq_abs] using add_le_add h1 h2)
    have hsecond : ‖Complex.I*((H (a i) (b j) : ℂ)-(H (b i) (a j) : ℂ))‖ ≤ M+M := by
      rw [norm_mul,Complex.norm_I,one_mul]
      exact (norm_sub_le _ _).trans
        (by simpa only [Complex.norm_real,Real.norm_eq_abs] using add_le_add h3 h4)
    linarith
  unfold jetComplexHessian
  rw [norm_mul,show ‖(4 : ℂ)⁻¹‖=(1/4 : ℝ) by norm_num]
  nlinarith

theorem actual_jet_complex_hessian_sub_two (a b : Fin 2 → E) (H K : Bilin) :
    jetComplexHessian a b (H-K)=jetComplexHessian a b H-jetComplexHessian a b K := by
  ext i j
  simp only [jetComplexHessian,_root_.sub_apply,Matrix.sub_apply,Complex.ofReal_sub]
  ring

theorem actual_full_hessian_modulus_from_mixed_two
    (a b : Fin 2 → E) (H K : Bilin)
    (hHsym : ∀ v w, H v w=H w v) (hKsym : ∀ v w, K v w=K w v)
    (hN : ‖a 1‖=1) (ha : ∀ i, ‖a i‖ ≤ 1) (hb : ∀ i, ‖b i‖ ≤ 1)
    (ha0 : inner ℝ (a 1) (a 0)=0) (hb0 : inner ℝ (a 1) (b 0)=0)
    (hb1 : inner ℝ (a 1) (b 1)=0)
    {eps M delta ed : ℝ} (heps : 0 ≤ eps) (hM : 0 ≤ M) (hd : 0 < delta)
    (hH : ‖H‖ ≤ M) (hK : ‖K‖ ≤ M)
    (hmixed : ∀ w : E, inner ℝ (a 1) w=0 → ‖(H-K).flip w‖ ≤ eps*‖w‖)
    (hA : (jetComplexHessian a b H).PosDef) (hB : (jetComplexHessian a b K).PosDef)
    (h00 : delta ≤ (jetComplexHessian a b H 0 0).re)
    (hdet : |(jetComplexHessian a b H).det.re-(jetComplexHessian a b K).det.re| ≤ ed) :
    ‖H-K‖ ≤ 3*eps+4*(ed+3*M*eps)/delta := by
  let A := jetComplexHessian a b H
  let B := jetComplexHessian a b K
  let S := H-K
  have hSsym (v w : E) : S v w=S w v := by
    change H v w-K v w=H w v-K w v
    rw [hHsym v w,hKsym v w]
  have hentry (L : Bilin) (hL : ‖L‖ ≤ M) (i j : Fin 2) :
      ‖jetComplexHessian a b L i j‖ ≤ M := by
    have hv (v w : E) (hv : ‖v‖ ≤ 1) (hw : ‖w‖ ≤ 1) : |L v w| ≤ M := by
      apply (L.le_opNorm₂ v w).trans
      exact (mul_le_mul (mul_le_mul hL hv (norm_nonneg _) hM) hw (norm_nonneg _) (by positivity)).trans_eq
        (by ring)
    exact actual_jet_complex_entry_of_four_bounds_two a b L i j
      (hv _ _ (ha i) (ha j)) (hv _ _ (hb i) (hb j))
      (hv _ _ (ha i) (hb j)) (hv _ _ (hb i) (ha j))
  have hmixentry (v w : E) (hv : ‖v‖ ≤ 1) (hw : ‖w‖ ≤ 1)
      (ht : inner ℝ (a 1) v=0) : |S v w| ≤ eps := by
    rw [hSsym v w]
    apply ((S.flip v).le_opNorm w).trans
    have hvv : ‖S.flip v‖ ≤ eps := (hmixed v ht).trans
      (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hv heps)
    exact (mul_le_mul hvv hw (norm_nonneg _) heps).trans_eq (mul_one _)
  have hrow (j : Fin 2) : ‖A 0 j-B 0 j‖ ≤ eps := by
    have he := actual_jet_complex_entry_of_four_bounds_two a b S 0 j
      (hmixentry _ _ (ha 0) (ha j) ha0) (hmixentry _ _ (hb 0) (hb j) hb0)
      (hmixentry _ _ (ha 0) (hb j) ha0) (hmixentry _ _ (hb 0) (ha j) hb0)
    simpa only [S,actual_jet_complex_hessian_sub_two,Matrix.sub_apply] using he
  have hdiag : |(A 0 0).re-(B 0 0).re| ≤ eps := by
    simpa only [Complex.sub_re] using (Complex.abs_re_le_norm (A 0 0-B 0 0)).trans (hrow 0)
  have hnormal := actual_positive_hermitian_normal_modulus_two hA hB hd h00 hM hM hdet
    (hentry H hH 0 1) (hentry K hK 0 1) (hrow 1)
    ((Complex.abs_re_le_norm (B 1 1)).trans (hentry K hK 1 1)) hdiag
  have hnorm' : |(A 1 1).re-(B 1 1).re| ≤ (ed+3*M*eps)/delta := by
    convert hnormal using 1 <;> congr 1 <;> ring
  have hBT : |S (b 1) (b 1)| ≤ eps := hmixentry _ _ (hb 1) (hb 1) hb1
  have hnormalId : S (a 1) (a 1)=4*((A 1 1).re-(B 1 1).re)-S (b 1) (b 1) := by
    simp only [A,B,S,jetComplexHessian,_root_.sub_apply,Complex.mul_re,Complex.mul_im,
      Complex.add_re,Complex.add_im,Complex.sub_re,Complex.sub_im,Complex.ofReal_re,
      Complex.ofReal_im,Complex.I_re,Complex.I_im]
    norm_num
    <;> ring
  have heta : 0 ≤ 4*(ed+3*M*eps)/delta+eps := by
    have hed : 0 ≤ ed := (abs_nonneg _).trans hdet
    positivity
  have hnormalReal : |S (a 1) (a 1)| ≤ 4*(ed+3*M*eps)/delta+eps := by
    rw [hnormalId]
    calc
      _ ≤ |4*((A 1 1).re-(B 1 1).re)|+|S (b 1) (b 1)| := abs_sub _ _
      _ = 4*|(A 1 1).re-(B 1 1).re|+|S (b 1) (b 1)| := by rw [abs_mul]; norm_num
      _ ≤ 4*((ed+3*M*eps)/delta)+eps :=
        add_le_add (mul_le_mul_of_nonneg_left hnorm' (by norm_num)) hBT
      _ = _ := by ring
  exact (actual_symmetric_bilinear_norm_from_tangent_and_normal_four hN S hSsym heps heta hmixed hnormalReal).trans_eq
    (by ring)

end PowerConvexity
