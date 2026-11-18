# POWER-CONVEXITY-LEAN：原稿两项输入及最终组装

设 $\Omega\subset\mathbb C^2$ 为有界严格凸域，边界光滑，给定原稿正支经典解
$$
u\in C^4(\Omega)\cap C^2(\overline\Omega),\qquad
(u_{i\bar j})>0,\qquad \det(u_{i\bar j})=1,\qquad u|_{\partial\Omega}=0.
$$
闭包 $C^2$ 在源码中表示真实内部一、二阶 Fréchet 导数的连续延拓 `ClosureC2Jet`，不要求解跨边界延拓。经实际平移取 $0\in\Omega$，选共同内球及外界，令 $\Omega_t=t\Omega+(1-t)B_R$，$t\in[0,1]$；$R=1$ 对应原稿。构造所得是同一个实际族 $u_t$：每个成员严格 psh、行列式为一、真零边界、内部 $C^4$，并有实际 $J_t:\mathrm{ClosureC2Jet}(u_t,\Omega_t)$。端点满足 $u_1=u$ 的函数字面相等，$u_0=|z|^2-R^2$ 在真实闭球上成立。

在闭包上，导数连续性始终同时包含对内部导数的识别。球端点只需闭球上的函数等式，而指定终点保留整个环境空间上的函数等式；这一区别与后续比较和 exhaustion 的精确接口一致。

真实截断始终按 `DistanceInteriorTruncation.lean` 定义为
$$
\Omega_t^\varepsilon=\Omega_t\cap
\{x:\varepsilon<\operatorname{infDist}(x,\partial\Omega_t)\}.
$$
最终同族组装给出
$$
\exists\delta>0\quad\forall\,0<\varepsilon<\delta\quad
\forall t\in[0,1]\quad\forall x\in\partial\Omega_t^\varepsilon,
\qquad \operatorname{modifiedSigmaTwo}(u_t,x)>0.
$$
固定标准复标架参数在此省略；`modifiedSigmaTwo` 使用源码定义的 `lowerEigenvalueTwo (modifiedK …)`。共同厚度在全部截断和参数之前选取。将这同一个族、同一组 jets 和边界结论交给已有 exhaustion，得到每个完整 $\Omega_t$ 内的谱正性及 $-\sqrt{-u_t}$ 的严格凸性。以下说明两个实质输入如何得到，以及强凸逼近如何返回原域。

## 实际经典解族的构造

首先在真实物理坐标中完成线性边界输入。实际冻结归一化和单位图给出共同尺度；逆图的真实 Hessian 产生漂移项，系数、漂移和荷载的界随同尺度一起控制。`actualCommonDomainGraphPhysicalInputFour` 将这些数据及真零迹构造成 `ActualFlatDriftPhysicalInputFour`。这里的零迹由真实域边界经图映射传输，展开方程保留荷载和漂移，未用抽象平边界条件替代原问题。

该构造明确核对了图变换后的椭圆性。若原下、上界为 $\lambda,\Lambda$，图的一阶导数界给出 $L=1+D_0$，则变换后的界为 $\lambda/L^2,\Lambda L^2$；荷载 Hölder 界带相同的 $L^\alpha$ 因子。系数在半球外的可测延拓与真实半闭球上的原系数相等，因而弱解工具和实际经典方程使用的是同一个局部算子。

共同二次展开随后返回原坐标。`actual_uniform_original_domain_boundary_expansion_four` 产生实际 `ActualDomainBoundaryExpansionFour`，包括二次多项式、冻结方程、Hessian 界和余项；闭包 jet 由这些展开及真实内部导数的相容性构造。非线性闭性另需跨解族的边界 Hessian 模量：切向方程、边界零迹、粗系数估计及行列式关系给出该模量，再与已有内部估计粘合。这一步没有把内部 $C^4$ 紧性误用为边界紧性。

固定一个中间域后，先选共同 $\alpha\in(0,1)$，再处理连续性路径上的参数和实际解。荷载空间是完整的实际 $C^{0,\alpha}$ 空间：连续函数和它的有界 Hölder 差商满足闭线性相容关系。零边界 $C^{2,\alpha}$ 空间同时记录函数、真实一阶导数、真实二阶导数及其 Hölder 差商；边界零值和导数识别都是闭条件。完备性因此由闭子空间得到，不依赖把光滑荷载在大 Hölder 范数中稠密化。

这一空间选择也固定了解的含义：Banach 空间中的未知量有真实函数值，内部导数由相容条件识别，边界值在真实闭包上逐点为零。弱线性解须经正则性和迹识别进入这个空间；仅得到弱解存在或分布意义上的算子右逆，都不足以用于这里的非线性开放性。

对当前实际 jet，复 Hessian 的正性及 Hölder 控制实际产生 cofactor 系数。弱 Dirichlet 解、内部经典正则性和上述真实边界展开共同给出行列式映射 Fréchet 导数的有界双侧逆；一般复正交标架通过真实实线性等距变换与四维模型相容。这个逆由 `actual_isometric_holder_jet_determinant_bounded_inverse_two` 证明，最终存在定理没有继续把线性逆或边界模量留作假设。

更精确地，若 $D\mathcal F(p):X\to Y$ 是当前零迹 jet 上的行列式导数，证明构造连续线性映射 $S:Y\to X$，并同时证明 $D\mathcal F(p)\circ S=\mathrm{id}_Y$ 与 $S\circ D\mathcal F(p)=\mathrm{id}_X$。第二个恒等式排除零迹空间中的线性核，确保所得线性解的唯一性；等距传输同时处理荷载和 jet，未只在矩阵层面改变标架。

在同一完整荷载空间中，使用实际次解 $w$ 的路径 $(1-s)\det H_{\mathbb C}w+s$，$s\in[0,1]$。真实隐函数定理先给出同一物理函数的正支 $C^{2,\alpha}$ 解；实际差商弱线性化、第一及第二弱变分和 Schauder 提升再把这个函数升至内部 $C^4$。因此开放性没有先假设未知隐函数解已经 $C^4$。闭性使用实际边界 Hessian 模量、既有内部紧性及极限 jet 识别。起始解是 $w$，非空开闭参数集覆盖整个区间，终点密度为一。

这里的独立存在引理要求 $w$ 为全局 $C^6$、真实零边界、闭包上严格 psh 且行列式至少为一，并要求一个全局 $C^3$ 的实际定义函数，其边界梯度非零且负号侧正是域。它们用于统一先验界和线性边界理论。下述中间域构造实际给出这些数据，故它们没有成为原稿额外假设。连续性参数 $s$ 与移动域参数 $t$ 始终分开：先在每个固定域完成前者，再组装后者。

原中间域所需的全局光滑严格次解和真实定义函数，已由原端点解及 Minkowski 几何构造。接入上述存在定理后，`actual_classical_minkowski_intermediate_family_two` 精确给出每个 $0<t<1$ 的 `hex`；再插入原端点和实际球解，得到保留 $u_1=u$ 的 `ClassicalMinkowskiFamilyTwo`。所有后续论证都使用这个实际族。

## 共同截断与返回原域

一般严格凸光滑域不被加强为处处正实曲率。采用已形式化的外逼近：构造实际光滑强凸域 $V_n$，满足 $\overline\Omega\subset V_n\subset r_n\Omega$、$r_n>1$、$r_n\to1$，并用上述存在性产生其真实解 $v_n$。

对每个固定 $n$，在其整个 Minkowski 参数族上构造联合定义几何，包含球端点 $t=0$。实际增广法向映射保持所需非退化性，由联合紧致几何取得共同物理图和系数界；共同闭包 $C^2$ 界及边界分析给出 `strong_defining_minkowski_actual_boundary_holder_two`。其半径、指数和常数先于全部参数、实际解和 jets。与实际边界切向正性结合后，得到整段参数的共同真实截断 collar。此时的量词是每个 $n$ 各有共同厚度，而不是要求所有 $n$ 共用厚度。

具体而言，对固定逼近域先取 $\eta_n>0$、$\alpha_n\in(0,1)$、$C_n\ge0$；对每个 $t$、每个真实解及其 jet，在真实边界点 $c$ 附近都有 $\|J.H(x)-J.H(c)\|\le C_n\|x-c\|^{\alpha_n}$。这与实际解族的联合闭包 jet 连续性相接，再在紧致的移动闭包图上取得共同 collar。逐个解各自有连续 Hessian 本身不能替代这一步，也不能保证包含球端点的共同厚度。

在一个固定正截断上，已有 P119 接受这个实际边界正性输入，并通过共同扰动半径处理整个参数区间；扰动半径可以依赖截断厚度，仍先于参数和扰动势。零参数复用已有实际 P117。随后 exhaustion 得到每个强逼近族完整纤维上的结论，特别是指定端点 $v_n$ 的 power convexity。

这里的“全域”确实包括每个任意内部点，而不是某个固定截断：对给定内部点，取比其到真实边界的正距离及共同厚度都小的截断即可。截断可以随内部点缩小；共同厚度必须预先对全部参数成立。所用导数、方程和扰动势均属于先前选定的实际族。

返回原解不能直接传递严格凸性。实际 Dirichlet 比较和精确缩放给出，对 $x\in\Omega$，
$$
r_n^2u(r_n^{-1}x)\le v_n(x)\le u(x).
$$
两侧收敛于给定的同一个 $u(x)$，从而先得到 $-\sqrt{-u}$ 的普通凸性。之后在其非负 Schur 分支上应用已有局部 trace-ratio 估计和相应严格性准则，恢复原函数的正实 Hessian、`modifiedSigmaTwo > 0` 和严格凸性。这一步既不把严格凸性的极限自动称为严格凸，也不需要逼近序号上的共同严格性常数。

最后对同一实际原 Minkowski 族的每个成员应用上述原域结论。正截断的真实边界点属于完整原域，由 `distanceInteriorDomain_frontier_value` 识别，故先得到所有正截断的边界谱正性，再一次取 $\delta=\min\{\rho,1\}$，其中 $\overline B_\rho\subset\Omega$。`actual_paper_family_common_collar_exhaustion_two` 确实把这个同族边界结果再次交给已有 exhaustion，回填原稿的精确接口。

因此，直接跨参数的共同边界 Hölder 分析用在强凸逼近族上；原一般凸域的共同截断接口通过新证明返回同一个原解后得到。二者的范围没有混淆，也没有调用旧最终凸性定理反推缺口。实际平移最后消去原点归一化，原域结论覆盖任意位置。

## 关键源码与冻结题面的对应

以下文件路径均相对 `PowerConvexity/`。

| 结论 | 精确声明 | 文件 |
|---|---|---|
| 实际物理漂移输入 | `actualCommonDomainGraphPhysicalInputFour` | `Analysis/ActualCommonDomainGraphPhysicalInputFour.lean` |
| 原域边界二次展开 | `actual_uniform_original_domain_boundary_expansion_four` | `Analysis/ActualOriginalDomainBoundaryExpansionFour.lean` |
| 实际有界双侧逆 | `actual_isometric_holder_jet_determinant_bounded_inverse_two` | `Analysis/ActualIsometricHolderDeterminantInverseTwo.lean` |
| 实际非线性存在 | `actual_classical_dirichlet_exists_two` | `Analysis/ActualClassicalDirichletExistenceTwo.lean` |
| 精确中间域 `hex` 与完整同族 | `actual_classical_minkowski_intermediate_family_two`；`actual_classical_minkowski_family_exists_two` | `Calculus/ActualClassicalMinkowskiExistenceTwo.lean` |
| 强逼近族共同边界模量 | `strong_defining_minkowski_actual_boundary_holder_two` | `Calculus/MinkowskiStrongActualBoundaryHolderTwo.lean` |
| 强逼近族共同真实截断 | `minkowski_strong_defining_actual_common_truncation_sigma_two` | `Calculus/MinkowskiStrongActualCommonCollarTwo.lean` |
| 同一原族、jets、厚度及全域 exhaustion | `actual_paper_family_common_collar_exhaustion_two` | `Calculus/ActualPaperFamilyAssemblyTwo.lean` |
| 任意原域的正 Hessian、谱正性与严格凸性 | `actual_original_dirichlet_hessian_sigma_strictConvex_uncentered_two` | `Calculus/ActualUncenteredOriginalPowerConvexityTwo.lean` |
| 原稿主定理接口 | `actual_original_route_mainTheorem` | `Targets/ActualOriginalRouteMainTheorem.lean` |

独立适配文件 `evidence/C114/FrozenMainOriginalRouteCheck.lean` 自行把冻结题面的 `ClosedC2` 变成实际 jet，并核对真实 Wirtinger Hessian 的 $1/4$ 因子，给出 `PowerConvexityComparator.OriginalRoute.newMainAnswer : Problem.MainStatement`。它不导入旧 `Solution`；新证明的假设与冻结主定理逐项相接。

唯一底稿仍是冻结 arXiv v1 TeX。主定理在 84–88 行，正支语义见上下文。第 1173 行字面仍写 `u_s+q` 严格凸，原文件没有改写；按照既有 C108W2/C109 勘误，P119 所用对象为 `powerTransform (fun y => u t y + q y)`，即原稿记号下的 $-\sqrt{-u_s-q}$，Lean 中参数记作 $t$。

本报告提供数学内容和源码映射。完整项目闭包为 1714 个模块，其中新增 291 个；显式公开审计根为 602 个 theorem、71 个 def 和 1 个 abbrev，另有两个私有辅助的专门覆盖检查。最终干净构建、构建后审计和交付状态，以最终实际验收回执为准，不能由本报告推定。外部 Comparator 未运行；本地冻结题面检查与它分别报告。
