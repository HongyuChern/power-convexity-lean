# C108W2 — cumulative source corrections

The corrections below are from a historical checkpoint. The status of the former proof obligations is updated in the [release coverage audit](PAPER_COVERAGE.md).

Authority remains the unchanged frozen TeX, SHA-256 89e32a9da75cb1c422223c0962233bb791e13dace252f0424db7a1949aedd4f9.
The C107 list below is retained as the historical record; the following current changes supersede its coverage descriptions.

## New corrections and clarifications

* **747, 752–764, and the later inverse components at 923:** the existing row-first inverse correction must also be applied in the Q1 expansion. With `G=A^{-1}=I+r r*`, the coefficient of the `p,bar(q)` contraction is `G[q,p]=delta[q,p]+r_q conjugate(r_p)`. The other inverse factor in `typeIQuadratic` uses the corresponding conjugated order. The general exports `paper_Q1_split`, `paper_Q11_trace_square` and `paper_Q12_Q13_split` consistently retain this convention; they do not silently assert the differently indexed printed coefficients.
* **865--866, Q65:** change its leading minus sign to plus. Expanding -q_G(W+tau e-bD)/(1-b^2) gives +b(tau pair_G(e,D)+conj(tau) pair_G(D,e))/(1-b^2). `weightedSquare_three_term` and `paper_Q6_completed_square` prove this in every finite dimension. `paper_Q65_printed_sign_counterexample` evaluates the true coefficient at tau=D=i, b=1/2 as +4/3, whereas the printed sign gives -4/3. This is an algebraic error; no PDE realization of arbitrary jets is claimed. The corrected completed square has an actual downstream use in `contactQuadratic_eq` and `modifiedSigma_final_fullQ_contact`.
* **854–855, 859 and 866, second sums in Q64/Q65:** the printed second summation subscript is `s != 1, q`, but its summand uses p and contains no q. Replace that dummy q by p. Otherwise the explicit sum repeats an unused q and leaves the intended p summation unspecified (or introduces an unwanted dimension factor under an additional implicit-summation reading). The finite weighted-pair expansions in `paper_Q64_Q66_simplify` and `paper_Q6_completed_square` use the consistent bound indices.
* **875:** the named contributor Q23 should read Q423, the term actually defined immediately before the Q6 regrouping.
* **1535--1536:** the second product is generally non-Hermitian. Read its '<1' spectrally. `uniform_L2_shifted_matrices` now proves both shifted matrix estimates and an explicit real diagonal similarity with entries in [0,1), from the existing robustness hypotheses. No cited unformalized matrix lemma is used.
* **1173:** the sentence asserting strict convexity of u_s+q should refer to -sqrt(-u_s-q). Positive modified quotient controls the latter Hessian. Positivity of the Hessian of -sqrt(-u) does not imply positivity of D2u, since D2u=-2v D2v-2 Dv tensor Dv for v=-sqrt(-u). This is a correction to the inference, not a construction of the missing Dirichlet family.
* **1783–1792, scalar normalization:** a fixed nonunit complex rescaling that makes alpha=1 changes density one into a positive constant rho. The use at 1792 only needs the mixed Hessian to be constant, so replace the retained density-one wording there by constant density. All actual scalar exports allow this rho; no normalizing frame is differentiated. On the nonnegative-sigma branch, the upper inequality in 1785 must allow beta=1 at zero contact. Near that contact one may use 1/2<=beta<=1; beta<1 cannot be assumed to rule out the very zero under consideration.
* **1847, C3.1:** replace `h(u_barz-u_z)` by `h(u_z-u_barz)`. Indeed 1797 gives `alpha_z ~ h(u_barz+u_z)`, while conjugating 1802 gives `(conjugate beta)_z=2h alpha u_barz ~ 2h u_barz`. Their difference in 1843 has the corrected sign. `scalar_C31_normalized_gradient_remainder` gives the exact actual-derivative error identity, and `scalarCompensated_corrected_contact` proves equality at normalized zero critical contact. `scalar_C31_normalized_error_bound` controls the error by sigma and the actual derivative of sigma on beta>=1/2. The following squared-norm cancellation is unchanged by this sign correction.

## Current scope updates

The Q algebra and actual final_fullQ contact identity are now general finite-dimensional theorems. The general neighborhood remainder estimates remain separate. The actual positive-branch trace-root value, first-derivative and complete mixed second-derivative limits are directly proved, including repeated off-top eigenvalues and the dominant cancellation. Their identification with the actual largest-root derivative is also proved; the printed local uniform exponential estimate/interchange at 1690–1695 is not.

Both shifted robustness matrices now have direct general-dimensional exports with the uniform quantifier order. The valid strong-convexity limit at 1173 has an actual Minkowski-family downstream application; the classical family existence, its uniform C2 route, boundary layer and continuity of m(t) remain unproved. See `C108W2_REMAINING_INTERFACES.md` for the exact missing inputs.

The normalized Appendix C first/second residuals and the corrected C3.1 now have exact actual-derivative identities and explicit pointwise error coefficients. Normalization is only at the point of evaluation; it is never differentiated as a neighborhood identity. The actual mu/sigma product and quotient formulas are separately exported. These additions do not turn pointwise normalized calculations into a new unproved uniform moving-coordinate estimate. The existing unnormalized local scalar estimate and endpoint remain unchanged.

For **1694**, the missing second-jet dependence also fails when the stated
C1 quantities mean uniform bounds on a fixed neighborhood. The smooth
diagonal example `K_N(t)=diag(2+(1-cos(N t))/N,1)` has entries bounded by 4,
first derivative bounded by 1, and gap at least 1 for all real t and N>=1.
At zero, its dominant second derivative is N and the second trace-root
derivative error for fixed p>1 is
`N [1-(1+2^(-p))^((1-p)/p)]`. This is an elementary analytic counterexample
recorded in the manuscript audit; it is not included in the Lean theorem
counts. Adding controlled second derivatives is necessary for the claimed
uniform dependence.

All coverage statements in the historical C107 text below are dated descriptions of that checkpoint. They are superseded by the current scope above and `C108W2_TEX_DECLARATION_MAP.md`; the mathematical corrections remain in force.

---

# C107W2 — frozen-source corrections and proof replacements

Authority: `inputs/PowerConvexity_CHS.tex`, SHA-256
`89e32a9da75cb1c422223c0962233bb791e13dace252f0424db7a1949aedd4f9`.
The TeX is **unchanged**. All positions below are exact lines of that file.
Corrections to a false or ill-defined isolated statement are distinguished from
a different proof of the same valid conclusion. The new generic hypotheses
below are not added to either public Dirichlet endpoint.

## Statements and necessary hypotheses

### 1. Determinant lemma: 1181–1199, especially 1183 and 1197

The isolated wording “quadratic polynomial” must retain the real-valued
convention for u and specify `det A != 0`. The displayed formula uses both
`A^{-1}` and `bar(A)^{-1}` and divides by `(det A)^2`. A quadratic polynomial
does not imply this condition. For example, `u=Re(z^2)` in dimension one has
`A=0`, `B=1` and real Hessian determinant `-4`; the unrestricted formula is
not a legitimate inverse identity (and is false under totalized Lean division).

The proved statement is stronger in regularity: any actual real C2 function
at a point, in arbitrary finite dimension, with nonsingular mixed Hessian.
It proves exactly

`det(I - B bar(A)^{-1} bar(B) A^{-1}) = det(D)/(4^n (det A)^2)`.

The real coordinates are also exported in the manuscript's interleaved
order. The coefficient is checked through actual real/complex Hessian
congruence, including the factor in the coordinate transformation. As a
normalization check, `u=sum |z_i|^2` has `D=2 I_(2n)`, `A=I_n`, `B=0`, hence
`det D=4^n`. Positivity of A is not an assumption of the new identity.

At 1201 and 1237, normalizing A to I requires A positive definite, not just
nonsingular. The minimal fix to the identity is nonsingularity; the proof is
replaced by the block determinant/Schur calculation. At **1208 and 1211**, the
last `tilde A` must be `tilde A^{-1}`. C105W2's early note gave neighboring
line numbers 1207/1210; the present positions supersede that locator error.

Declarations: `actual_hessian_determinant_identity`,
`actual_hessian_determinant_identity_interleaved`.

### 2. Separation: 1300–1331; compactness at 1344 and 1128

Take a **positive** budget epsilon and, for the printed second eigenvalue,
`n >= 2`. The integration set is a compact body with nonempty interior, and
the measure is locally finite and positive on nonempty open sets. These
conditions are satisfied by the intended compact smooth body and a smooth
positive volume density. They make the L2 quantity a genuine norm on the
finite-dimensional polynomial space. Closedness and finite dimension alone,
as written at 1344 and 1128, do not imply compactness; boundedness in this
actual norm is needed and is proved.

Epsilon zero cannot give a general separation result: at a center where the
unperturbed pure Hessian and gradient vanish, the sole perturbation may leave
K=I with repeated minimum. The general theorem proves both attainment and
simplicity. Its full diagonal similarity retains eigenvalue multiplicities;
it does not mistake a gap between distinct spectral set elements for a
simple characteristic root. It retains actual negative values and strict
psh of `-sqrt(-u-q)` on the admissible ball. The printed additional real
convexity of every transform is not needed by this stronger proof.

Declarations: `exists_pluriharmonic_quadratic_minimizer_with_gap`,
`pluriharmonic_quadratic_minimizer_has_gap`,
`HasSimpleLeastSpectrum.charpoly_factors`.

### 3. General extremal eigenvalues: 1565–1580

A smooth complex matrix field, merely real diagonal at one point, need not
have ordered real eigenvalues nearby. For example,
`K(t)=diag(1+i t,0)` is real diagonal with a simple largest eigenvalue at
t=0, but has a nonreal eigenvalue for every real t != 0. Thus “maximum” and
“minimum” in the generic lemma require a local real-spectrum condition
(local Hermitian similarity is sufficient, but stronger than necessary).

The corrected general theorem assumes a neighborhood of real spectrum and
proves local C2 regularity of the actual maximum/minimum, its base value,
the first derivative, and both cross terms in the mixed second derivative.
It does not assume a differentiable eigenvalue branch. The actual modified
Hessian quotient satisfies the real-spectrum condition by proved Hermitian
similarity; `modifiedK_smallestRealEigenvalue_jet` is an actual downstream
application which discharges it from positive A and symmetric B.

The trace-power argument is replaced by a scalar Schur-complement implicit
function theorem, determinant/eigenvalue identification and Gershgorin
separation. Consequently the full `B1-1/B1-2/B2-1/B2-2` conclusions are
proved, while the particular trace-power limits in `B3-*` and expansions
in `B4-*` are not independently exported.

The manuscript **already shifts K by a scalar** at 1584 before using K inverse.
Missing invertibility is therefore not a separate defect in that later
inverse argument, once the real-spectrum setting has been supplied.

Declarations: `largestRealEigenvalue_jet`, `smallestRealEigenvalue_jet`,
`SimpleRealEigenvalueJet.real_derivatives`,
`modifiedK_smallestRealEigenvalue_jet`.

### 4. Strict convexity, Hessian positivity and perturbation stability

At **228, 248, 1084, 1090 and 1774**, the manuscript moves between convexity
and positive definite Hessians. For C2 functions, positive Hessian implies
strict chord convexity on an open convex domain; the converse is false
(`x^4` at zero). Semidefinite Hessian corresponds to nonstrict convexity.

For `prop:perturbation_stable` (1082–1100), the proof at 1151 uses positive
lowest Hessian eigenvalues at the starting potential and on the boundary.
The implemented corrected proposition states these positive actual Hessian
hypotheses explicitly. It proves both conclusions: actual StrictConvexOn
for every admissible perturbation on the convex inner domain and a uniform
strict positive real-Hessian lower bound. Its constant-density equation,
interior-subdomain regularity and dimension-two context remain explicit.

The quantitative constant-dependence content is separately expressed by
`uniform_L2_quadratic_robustness`: C is quantified **before** the potential
and center, with a fixed positive epsilon, bounded center set, compact
integration set/measure and negative lower bound for the potential. In the
paper's fixed unit-ball integration and bounded domain setting this supplies
the stated data dependence; no derivative bound of the selected u enters C.

At 1774 the precise scalar distinction is: on the positive-alpha branch,
positive real Hessian is equivalent to sigma>0; nonnegative real Hessian
corresponds to sigma>=0. The endpoint proof establishes positivity, then
uses the correct forward implication to StrictConvexOn.

None of these corrections strengthens geometric strict convexity of the
domain to positive boundary curvature in `mainTheorem` or the Appendix C
endpoint. The latter keep the original domain and actual-jet interfaces.

### 5. Robustness statement: 1503–1517

Line 1505 uses p0 while 1512–1514 estimate at z0. Identify the two points,
and make actual C2 regularity near the point and epsilon>0 explicit. The
lemma is proved under the weaker local nonstrict convexity assumption for
the full perturbation family. The measure dependence is **already stated**
at 1512 and is retained; it is not a missing condition in the source.

The direct centered holomorphic-square proof replaces the cited shifted
matrix route `cond:Alowerbound`/`cond:BABA`. Both the pointwise conclusion
and the uniform quantifier order are checked by independent problem types.

## Formula corrections

| Frozen location | Issue and minimal correction | Checked replacement/support |
| --- | --- | --- |
| 214, the factored line after `2_1_9` | The preceding line 212 contains `+B H^{-1} H_q H^{-1} H_p - B H^{-1} H_pq`. With the printed leading minus, the bracket must be `H_pq - H_q H^{-1} H_p`, not its negative. Here H=bar(A). | `compensatedField_dzbar`, `schurField_mixed_residual`; actual product differentiation. |
| 227, after `M_leq_0` | `M>=0` is called positive definite and used to infer M>0 inside. Nonnegative boundary values alone do not exclude a constant singular Schur matrix. Replace the boundary condition by the needed strict positivity/anchor. The quadratic `u=|z|^2+Re(z_1^2)` has A=I, B=diag(1,0,...), constant singular M and LM=0. | The actual displayed `LM<=0` is proved; the invalid stronger sentence is not exported. The endpoint uses a proved positive anchor and strong minimum principle. |
| 255 | `mathcal A > A` is too strong: the difference is the nonnegative rank-one matrix h g g*. Replace by `mathcal A >= A`; A>0 still gives mathcal A>0. | `modifiedA_eq_rankOne`, `modifiedA_posDef`. |
| 302, `pqM` | The last factor must be `(mathscr B^(q))*`, the adjoint of the compensated field. | `schurField_mixed_residual`, `schurField_contracted_residual`. |
| 320, `qsBp` | The last factor of the first parenthesis must be `partial_p bar(A)`, not `partial_p bar(A)^{-1}`. | `compensatedField_dzbar`. |
| 532, before `3.4.3` | Differentiation is by partial_barq, but the second term is printed with partial_p A. Replace that symbol by partial_barq A. | `modifiedSigmaTwo_mixed_normalized_exact`; the discarded term is retained in an exact remainder. |
| 923 and nearby inverse components | Under the stated row-first convention, `(I+r r*)[q,p] = delta_qp+r_q conjugate(r_p)`. Keep this order consistently. | `originalHessian_inverse_eq_normalized_rankOne`, `rankOneWeightTwo_trace_im`. |
| 941, first 2x2 weight display | The lower-left entry repeats the upper-right entry. Replace it by `r_2 conjugate(r_1)`. The expanded real matrix at 945–946 already has the appropriate conjugation. | Actual Hermitian matrix and trace-contraction calculations. |
| 1208, 1211 | The last tilde A needs inverse, as explained above. | Actual block determinant identity and quotient similarity. |
| 1446, `case3_K` | Whole-matrix strict decrease is false: splitting equal Takagi values b into b+t and b-t makes one quotient diagonal entry rise to first order. Replace by strict decrease of the minimum eigenvalue. | `quadraticFamily_repeated_positive_not_minimum_general`; two opposite Rayleigh-contact derivatives and an actual admissible curved L2 path. |
| 1664 | Dividing the numerator by k1^(p-1) removes that factor completely. The normalized denominator is `(k_l-k_m) W_p`, without the extra k1. | The full extremal-root lemma is proved by Schur/IFT; this malformed trace-power display is not asserted. |
| 1682, with W_p defined at 1654 | W_p=S^((p-1)/p). Thus the power of W_p in the denominator of F_p is `(2p-1)/(p-1)`, for p>1, not `(2p-1)/p`. | Same alternative proof of the complete derivative statement. |
| 1694–1695 | A uniform second-derivative error estimate cannot depend only on zeroth/first derivatives and gaps; second-derivative bounds are needed. Pointwise exponential convergence alone also does not establish local uniform convergence. | Local C2 eigenvalue regularity is obtained directly from the implicit function theorem, avoiding this interchange. |
| 1821, `C2.1.2` | Correct RHS: `2h+h^2(u_z^2+u_barz^2)`. The printed `2h+h^2(u_z^2+u_barz)^2` has an incorrect power and missing square. | `scalarAlpha_dzbar_dz`, `scalarBeta_dzbar`, and the exact `scalarSigma_equation_real`. |

The need for second-derivative data at 1694 can be seen even for the real
diagonal family `K_N(t)=diag(2+N t^2,1)`. At zero the value, first derivative
and gap are independent of N, while the difference between the second
derivatives of `(tr K_N^p)^(1/p)` and its largest eigenvalue is a nonzero
fixed-p multiple of N. Thus a bound uniform in N cannot use only the printed
zeroth/first-order data.

## Correct context and replacement arguments

- The nonnegative-sigma branch is explicitly assumed at **484**, before
  the definition of error notation at 488–493. It is a faithful hypothesis
  of the independent sigma estimate, not an invented PDE assumption. The
  frozen `SigmaProblem.lean` comment says “line 488”; this is a locator-only
  error in that comment. Its statement is correct, its compiled freeze is
  retained, and **484** is the authoritative location here.
- `prop:touch` at 1053 explicitly includes “unless sigma is identically
  zero”. The later contradiction at 1152 must retain that alternative.
  The formal proof establishes local zero propagation, then an open/closed
  zero-set argument and a positive boundary/anchor value. It does not infer
  contradiction from an isolated zero minimum alone.
- The `viscosity` remark at 1141–1149 itself notes the absence of an evident
  uniform constant. The formal envelope argument uses local touching
  branches; no unproved global viscosity constant is added as an assumption.
- The domain-varying Dirichlet solutions, uniform boundary layer and
  convergence in **1156–1175** are not constructed by this package. The
  actual dimension-two endpoint is proved instead by direct global
  nonstrict convexity, actual regularized trace-ratio estimates, the
  approximation strong minimum principle, and a proved positive anchor.
  The scalar endpoint similarly replaces the deformation reference at 1754.
- Fixed complex changes of frame change determinant one to a nonzero
  constant density. The source uses constant-density differential
  identities, and does not differentiate a pointwise normalizing frame.
- The two higher-dimensional remarks at 982–1043 concern an algebraic
  obstruction. The first actual skew-Hermitian matrix counterexample is
  separately checked for every n>2. No claim is made that arbitrary
  tensors chosen in the second remark are realized by a PDE solution.

## Coverage consequence

All nine theorem/lemma/proposition environments have checked implementations
of their stated conclusions, or the explicit corrected conclusions above.
The original two Dirichlet endpoints retain their intended assumptions and
actual StrictConvexOn conclusions. This is not a certificate for the false
intermediate displays, for every general-dimensional Q decomposition, for
the particular trace-power limiting proof, or for existence of the unused
moving-domain solution family. `C107W2_TEX_DECLARATION_MAP.json` classifies
all 123 labels and the unlabelled Appendix C theorem individually.
