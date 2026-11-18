# C109 — 原式、障碍和修正后的证明范围

The corrections below are from a historical checkpoint. The status of the former proof obligations is updated in the [release coverage audit](PAPER_COVERAGE.md).

冻结 `inputs/PowerConvexity_CHS.tex` 未作修改。
原有勘误 `C108W2_SOURCE_CORRECTIONS.md` 原样保留；本文件更新本轮涉及的状态。

## 1. TeX 1690–1695：指数估计常数遗漏二阶导数

**原式。** 对 H^(p) 的混合二阶导数误差给出 C1 exp(-C2 p)，
并在 1694 声称 C1、C2 只依赖 K 的零/一阶数据及谱隙。

**反例。** 令 N≥1，`K_N(t)=diag(2+(1-cos(Nt))/N,1)`。
整条实线上矩阵条目绝对值≤4，一阶导数绝对值≤1，顶根与次根间隙≥1。
在 t=0，顶根二阶导数为 N，且固定 p>1 的二阶误差绝对值为

\[
N\left[1-(1+2^{-p})^{(1-p)/p}\right].
\]

括号严格为正，故该误差随 N 无界。这排除了把原文的一阶数据解释成固定邻域上的统一 C1 界后保留原结论。
若只需基点反例，可用 `diag(2+Nt²,1)`，相应系数为 2N。
此反例是明确的解析核验，不计入新增 Lean 声明数。

**修正后形式。** 加入实际二阶导数上界 M2、统一谱比 q<1、顶根正下界 delta，
并控制规范化矩阵。`traceRootMixedJet_uniform_error_le` 的常数为

`d*(d+1)*M2 + d^2*(d+(d+1)/(1-q)+2)*M1^2/delta`。

由此得到 C(n+1)q^n，再由 `uniform_geometric_error_exponential` 得到印刷的指数形式。
`tracePowerRoot_second_local_uniform_of_metric_diagonalization` 与
`modifiedPositiveProduct_tracePower_second_local_uniform` 证明实际二阶导数的局部一致收敛与实际极限识别。

## 2. 附录 B 的通用矩阵场范围

**原式。** 开头以任意光滑 `T_(1,0) ⊗ T*_(1,0)` 场描述 K，后续使用实的最大/最小特征值、
正迹根及局部简单根。

**缺失条件。** 一般复矩阵场未必有实谱或可排序的实极值；一个点的对角化不能代替邻域结构。
相似变换若无控制，原坐标导数界不能直接作为规范化坐标导数界。

**修正后形式。** 本轮的一致版本采用可验证的正度量对角化接口：
K C2，非退化度量 A 在基点 C2，每点存在 Q 使 Q A Q*=I、Q K Q^(-1)=diag(k)，k≥0，
基点具有正简单顶根。实际 `I-modifiedK` 的这一结构由 Takagi 定理导出。
该结构给出邻域实谱、规范化矩阵界和共同谱隙；不假设光滑选取 Q。
不把修正后的结果扩大到没有这些结构的任意复矩阵场。

## 3. §3.1 的按点规范化与余项

**原有需补推导。** 在每个物理点选取规范化坐标，再以 sigma 与 Dsigma 记误差。
仅零临界接触点的恒等式不足以证明邻域线性误差界。

**必须保留的条件。** 简单根、正度量、实际有限阶导数及规范化矩阵界；求导时坐标矩阵固定。
不将 A(y)=I 当成邻域恒等式求导，不将高维恒等式升级为高维符号结论。

**已证明形式。** `modifiedSigma_local_fullQ_error_general` 在规范化简单基点周围导出
统一 B、delta，控制完整实际 Q 余项。常数对 B、delta 的依赖见 `C109_FINAL_REPORT.md`。
原有 n>2 反例不受影响。

## 4. TeX 1156–1173 的未补条件不计为勘误后的定理

经典解族存在性和全参数二阶控制仍是缺失的证明步骤。
几何严格凸性不等于正曲率；加球不授权把原域条件替换成正曲率。
t=1 的给定 C4/闭包 C2 解不自动具有闭包 C∞ 正则性。
本轮只列出这些调用条件，没有把它们附加到已经验收的公开端点。

TeX 1173 的 `u_s+q` 严格凸应为 `-sqrt(-u_s-q)` 严格凸；该勘误已在 C108W2 记录。
固定正强凸模的极限传递已经形式化，但构造这个统一模仍属于第 2 项。
