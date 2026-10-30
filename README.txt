Thomson 问题 N=7,8：解析与几何部分的 Lean 形式化
2026-10-30

本项目对应当前七点、八点合稿。计算机辅助证书作为显式定理参数输入；
解析下界、参数唯一性、等号条件及构型分类由 Lean 证明。
语言版本：Lean 4.35.0；依赖：Mathlib v4.35.0。

建议阅读顺序

1. Thomson78/CoordinateCertificate.lean
   最直接的有限证书入口：Coordinates.seven_minimum 与 eight_minimum。
   同一组有限多项式和标量在任意构型之前固定。输入是多项式恒等式

     E_h - τ = μ₁ C₁ + μ₃ C₃ + Σ q_k² + Σ λ_i (Σ_a X_ia² - 1),
     μ₁ > 0, μ₃ ≥ 0。

   其中 E_h、C₁、C₃ 均在源码中由坐标变量明确构造，分别评价为辅助
   多项式能量、重心范数平方和三阶 Legendre 总和。Lean 证明代入单位
   向量后球面约束项为零，并推出 Coulomb 能量下界和等号构型。

   这是矩证书经因子与特征展开后的坐标平方和接口。具体数值证书的
   导入、系数核验与因子数据属于本次约定接受的计算机辅助部分；当前
   源码把该有限恒等式保留为命名参数 hid。这里的主定理是“给定
   上述有限证书”的形式化结论；具体计算数据在实例化 hid 时接入。

2. Thomson78/FiniteCertificate.lean 与 Certificate.lean
   保留五点矩的系数接口及其评价规则。FiniteCertificate 中的 hm、hA、
   hc、hv₁、hv₃、hB 是数学实现等式，和有限证书恒等式 hid 明确分开。
   一般加权 Gram 表示的正半定性由 Moments.lean 推出。

3. Thomson78/Main.lean
   展示已求值证书如何依次推出严格接触条件、零重心和几何刚性。
   七点目标固定为候选能量后有 seven_candidate_minimum；根式下界
   见 seven_radical_lower_bound。八点见 eight_certificate_rigidity。

4. Thomson78.lean
   全项目汇总入口。Thomson78/Audit.lean 审计项目定理的公理依赖。

解析与几何证明

• AnalysisRolle、AnalysisHermite、AnalysisCoulomb：带重数的 Rolle
  定理、Hermite 余项及 Coulomb 核任意阶导数的正性和单调性。
• AnalysisInterpolationUnique：四节点双插值的构造、次数和唯一性。
• SevenMinorant*：h₇、端点增强 H₇ 的严格下界、接触集、唯一性，
  以及增强系数 γ 的最大性。
• SevenConfiguration、SevenPentagon、SevenRigidity、SevenDimension：
  从接触和重心条件恢复五边形双锥，并证明张成空间维数等于三。
• SevenEnergy：标准坐标、接触重数 (1,10,5,5) 与精确根式能量。
• EightParameter：t_* 的存在、唯一性、39/125<t_*<8/25，
  以及 Φ 在 (0,1) 上的唯一极小性。
• EightGeometry*、EightCandidate：行重数、八循环、循环 Gram 矩阵、
  线性等距映射与三维性。
• EightMatrixRigidity：从任意满足正文条件的八阶正半定矩阵出发，
  构造其 Gram 实现，恢复循环矩阵并证明矩阵秩恰为三。
• EightEnergy：标准反棱柱坐标、重数 (8,4,8,8)、E(A(t))=Φ(t)。
• AnalysisEightMinorant：h₈ 的次数八、严格下界、精确接触与切线条件。
• AnalysisEightRecovery、PolynomialRecovery：沿反棱柱族的值与导数
  匹配，半正定迹的极值步骤，以及两项剩余系数的消去。
• Moments、GramRelations、Harmonics：加权矩正性、四点 Gram 行列式
  为零、三阶球谐总和的显式平方和。
• AnalysisLegendreKernel、AnalysisLegendrePositivity：0 至 8 阶的
  归一化 Legendre 多项式、三项递推、显式实特征加法公式、核矩阵
  正性，以及固定三点后构造的全部 F_ℓ 的正性。
• FivePoint：注入平均、重标号不变性、边际一致性，以及把剩余点
  双和转换成五点矩的有限总体公式，系数为 N−3 与 (N−3)(N−4)。

与原稿的证明路线对应

八点行重数在 multiplicities_from_interval 中直接由参数区间与整数
计数得到。这使后续刚性证明对整个 39/125<t<8/25 区间成立，并取代
原稿为了分离行和系数而使用的 t_*∉Q(√2) 步骤。

Residue.lean 另提供一般整闭环约化引理与模 23 无根核验。这一模块
作为原稿数论路线的辅助材料：其中一般环论引理没有被实例化成原稿
特定二次域及局部环的完整证明，也不参与本项目主结论的依赖链。

七点最大增强系数的必要性使用九阶余项在端点邻域的统一上界，得到
与原稿端点展开相同的最大系数结论。

定义域

Admissible x 表示所有点位于单位球面且两两不同。所有 Coulomb
最优化结论都在这个有限能量定义域上陈述。coulombEnergy 使用实数
距离的倒数；其在 Admissible 域外的代数值不用于最优化结论。

构建与复核

推荐在已配置 Lean/Lake 的环境执行：

  lake update
  lake exe cache get
  lake build Thomson78
  lake env lean Thomson78/Audit.lean

当前电脑还提供使用已有 Mathlib 缓存的只读构建路径：

  D:\Python\python.exe -X utf8 compile.py --rebuild-own --report verification/final_build.json Thomson78/Audit.lean
  D:\Python\python.exe -X utf8 audit_project.py

compile.py 默认读取：
  F:\Lean\.elan\toolchains\leanprover--lean4---v4.35.0\bin\lean.exe
  F:\Smale5Formalization-v16\.lake\packages

可用 THOMSON_LEAN、THOMSON_MATHLIB_PACKAGES 环境变量调整。依赖缓存
复制到本项目 .lake 后使用；外部工程的源码和构建目录保持只读。
本次实际执行的构建路径是 compile.py；标准 Lake 命令作为复现入口。

verification 目录保存最终编译日志、公理审计及源码散列。
Audit.lean 对项目命名空间内所有定理依赖逐项检查，仅允许 Lean/
Mathlib 的标准公理 propext、Classical.choice、Quot.sound。
audit_project.py 进一步核对源码、最终模块日志及审计结果。

阅读这些记录时，应同时看定理陈述和公理审计：公理审计确认没有
占位证明或新增公理；证书参数的范围由上述接口及定理类型明确给出。
