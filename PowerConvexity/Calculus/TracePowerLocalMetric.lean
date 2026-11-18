import PowerConvexity.Calculus.TracePowerPhysicalUniform
import PowerConvexity.Calculus.UniformFrameJetsGeneral
import PowerConvexity.Calculus.UniformSimpleDiagonalGap

/-! # Automatic local uniform trace-power estimates in a positive metric

C2 entry regularity supplies both derivative bounds. The metric supplies
uniform conditioning of all pointwise diagonalizers. A simple positive top
root at the base point supplies the local positive top bound and common gap,
including algebraic multiplicity. No derivative of the chosen frames occurs.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Filter
open scoped BigOperators Topology ContDiff
namespace PowerConvexity
open CHS.Calculus
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem real_diagonal_hasEigenvalue_real (k : ι → ℝ) {z : ℂ}
    (hz : Module.End.HasEigenvalue (Matrix.diagonal (fun j => (k j : ℂ))).toLin' z) : z.im=0 := by
  have he := (Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).mp hz
  rw [Matrix.charpoly_toLin',Matrix.charpoly_diagonal] at he
  change Polynomial.eval z _ = 0 at he
  simp only [Polynomial.eval_prod,Polynomial.eval_sub,Polynomial.eval_X,Polynomial.eval_C] at he
  obtain ⟨j,_,hj⟩ := Finset.prod_eq_zero_iff.mp he
  rw [sub_eq_zero.mp hj]
  exact Complex.ofReal_im _

theorem largestRealEigenvalue_eq_diagonal_max (K Q : Matrix ι ι ℂ)
    (hQ : IsUnit Q.det) (k : ι → ℝ)
    (hdiag : Q*K*Q⁻¹ = Matrix.diagonal (fun j => (k j : ℂ)))
    (i : ι) (hmax : ∀ j, k j ≤ k i) : largestRealEigenvalue K = k i := by
  have heq (t : ℝ) : Module.End.HasEigenvalue K.toLin' (t : ℂ) ↔ ∃ j, k j=t := by
    rw [← hasEigenvalue_of_charpoly_eq (charpoly_complex_similarity Q K hQ) (t : ℂ),hdiag]
    exact real_diagonal_hasEigenvalue_iff k t
  apply IsGreatest.csSup_eq
  refine ⟨(heq (k i)).mpr ⟨i,rfl⟩,?_⟩
  intro t ht
  obtain ⟨j,rfl⟩ := (heq t).mp ht
  exact hmax j

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem tracePowerRoot_second_local_uniform_of_metric_diagonalization
    {K A : E → Matrix ι ι ℂ} {U : Set E} (hU : IsOpen U)
    (hK : ∀ l m, ContDiffOn ℝ 2 (fun y => K y l m) U) {x : E} (hx : x ∈ U)
    (hA : ∀ l m, ContDiffAt ℝ 2 (fun y => A y l m) x) (hAdet : (A x).det ≠ 0)
    (hfamily : ∀ y ∈ U, ∃ (Q : Matrix ι ι ℂ) (k : ι → ℝ), IsUnit Q.det ∧
      Q*A y*Q.conjTranspose=1 ∧ Q*K y*Q⁻¹=Matrix.diagonal (fun j => (k j : ℂ)) ∧ ∀ j, 0 ≤ k j)
    (i : ι) (k0 : ι → ℝ) (hdiag : K x=Matrix.diagonal (fun j => (k0 j : ℂ)))
    (hmax : ∀ j, j ≠ i → k0 j < k0 i) (htop : 0 < k0 i) (v w s t : E) :
    ∃ S : Set E, S ∈ 𝓝 x ∧ S ⊆ U ∧ ∃ C q : ℝ, 0 ≤ C ∧ 0 ≤ q ∧ q < 1 ∧
      (∀ n : ℕ, ∀ y ∈ S,
        ‖dz s t (dz v w (fun z => (tracePowerRoot K (n+2) z : ℂ))) y-
          dz s t (dz v w (fun z => (largestRealEigenvalue (K z) : ℂ))) y‖ ≤ C*((n : ℝ)+1)*q^n) ∧
      TendstoUniformlyOn
        (fun n y => dz s t (dz v w (fun z => (tracePowerRoot K (n+2) z : ℂ))) y)
        (fun y => dz s t (dz v w (fun z => (largestRealEigenvalue (K z) : ℂ))) y) atTop S := by
  classical
  letI : Nonempty ι := ⟨i⟩
  have hUnear : ∀ᶠ y in 𝓝 x, y ∈ U := hU.mem_nhds hx
  have hKx : ∀ l m, ContDiffAt ℝ 2 (fun y => K y l m) x :=
    fun l m => (hK l m).contDiffAt (hU.mem_nhds hx)
  have hspec : ∀ y ∈ U, ∀ z : ℂ, Module.End.HasEigenvalue (K y).toLin' z → z.im=0 := by
    intro y hy z hz
    obtain ⟨Q,k,hQ,_,hD,_⟩ := hfamily y hy
    have he := (hasEigenvalue_of_charpoly_eq (charpoly_complex_similarity Q (K y) hQ) z).mpr hz
    rw [hD] at he
    exact real_diagonal_hasEigenvalue_real k he
  have hreal : ∀ᶠ y in 𝓝 x, ∀ z : ℂ, Module.End.HasEigenvalue (K y).toLin' z → z.im=0 :=
    hUnear.mono (fun y hy => hspec y hy)
  have htrace : ∀ n : ℕ, ∀ y ∈ U, (K y^(n+2)).trace.im=0 := by
    intro n y hy
    obtain ⟨Q,k,hQ,_,hD,_⟩ := hfamily y hy
    rw [← matrix_similarity_trace_power Q _ hQ (n+2),hD,real_diagonal_trace_power,Complex.ofReal_im]
  obtain ⟨γ,hγ,hgap⟩ := simple_largest_eigenvalue_uniform_ordered_gap hKx i k0 hdiag hmax hreal
  have hj := largestRealEigenvalue_jet hKx i k0 hdiag hmax hreal
  have hbase : largestRealEigenvalue (K x)=k0 i := hj.2.1
  let δ := k0 i/2
  let L := k0 i+γ+1
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hL : 0 < L := by dsimp [L]; positivity
  have hγL : γ ≤ L := by dsimp [L]; linarith
  let q := 1-γ/L
  have hq0 : 0 ≤ q := by
    have h := (div_le_one hL).mpr hγL
    dsimp [q]; linarith
  have hq1 : q < 1 := by dsimp [q]; linarith [div_pos hγ hL]
  have hlo : ∀ᶠ y in 𝓝 x, δ ≤ largestRealEigenvalue (K y) :=
    (hj.1.continuousAt.eventually (lt_mem_nhds (by change δ < largestRealEigenvalue (K x); rw [hbase]; dsimp [δ]; linarith))).mono (fun _ hy => hy.le)
  have hhi : ∀ᶠ y in 𝓝 x, largestRealEigenvalue (K y) ≤ L :=
    (hj.1.continuousAt.eventually (gt_mem_nhds (by change largestRealEigenvalue (K x) < L; rw [hbase]; dsimp [L]; linarith))).mono (fun _ hy => hy.le)
  obtain ⟨B,hB,hframe⟩ := exists_eventually_normalizingFrame_bound_general hA hAdet
  obtain ⟨M1,M2,hM1,hM2,hjet⟩ := exists_eventually_matrix_second_jet_bounds_general hKx v w s t
  have hB0 : 0 ≤ B := by linarith
  have hM10 : 0 ≤ M1 := by linarith
  have hM20 : 0 ≤ M2 := by linarith
  have hall := hUnear.and (hframe.and (hjet.and (hgap.and (hlo.and hhi))))
  obtain ⟨S,hS,hhS⟩ := Filter.eventually_iff_exists_mem.mp hall
  have hSU : S ⊆ U := fun y hy => (hhS y hy).1
  let C := traceRootSecondErrorConstant (Fintype.card ι) q δ
    ((Fintype.card ι : ℝ)^2*B^2*M1) ((Fintype.card ι : ℝ)^2*B^2*M2)
  have hC : 0 ≤ C := by
    have hden : 0 < 1-q := by linarith
    dsimp [C,traceRootSecondErrorConstant,traceSecondUniformConstant]
    positivity
  have hest (n : ℕ) (y : E) (hy : y ∈ S) :
      ‖dz s t (dz v w (fun z => (tracePowerRoot K (n+2) z : ℂ))) y-
        dz s t (dz v w (fun z => (largestRealEigenvalue (K z) : ℂ))) y‖ ≤ C*((n : ℝ)+1)*q^n := by
    obtain ⟨hyU,hyF,hyJ,hyG,hyLo,hyHi⟩ := hhS y hy
    obtain ⟨Q,k,hQ,hN,hD,h0⟩ := hfamily y hyU
    obtain ⟨j,_,hj⟩ := Finset.exists_max_image Finset.univ k Finset.univ_nonempty
    have horder : ∀ l, k l ≤ k j := fun l => hj l (Finset.mem_univ l)
    have htopEq := largestRealEigenvalue_eq_diagonal_max (K y) Q hQ k hD j horder
    rw [htopEq] at hyLo hyHi
    have hGap := hyG Q hQ k hD j horder
    have hratio : ∀ l, l ≠ j → k l/k j ≤ q := by
      intro l hlj
      exact spectral_ratio_le_of_gap (hδ.trans_le hyLo) hyHi hγ (hGap l hlj)
    obtain ⟨hQB,hQiB⟩ := hyF Q hQ hN
    apply tracePowerRoot_second_uniform_error_frozen_frame hU hK hyU Q hQ k j hD h0
      hq0 hq1 hδ hyLo hB0 hM10 hM20 hQB hQiB hratio htrace _ v w s t
      hyJ.1 hyJ.2.1 hyJ.2.2 n
    filter_upwards [hU.mem_nhds hyU] with z hz
    exact hspec z hz
  refine ⟨S,hS,hSU,C,q,hC,hq0,hq1,hest,?_⟩
  have hr : Tendsto (fun n : ℕ => C*((n : ℝ)+1)*q^n) atTop (𝓝 0) := by
    have hh := (geometric_polynomial_uniform_rate hq0 hq1).const_mul C
    rw [mul_zero] at hh
    convert hh using 1
    funext n; ring
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [hr.eventually (gt_mem_nhds hε)] with n hn
  intro y hy
  rw [dist_eq_norm,norm_sub_rev]
  exact (hest n y hy).trans_lt hn

end PowerConvexity
