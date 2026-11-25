# Lean 形式化路线图

用 Lean 4 + Mathlib 把三篇论文的主定理做成机器可检查的证明，由 `lake build` 自动核对。

| 论文 | Zenodo | 状态 |
|---|---|---|
| A Seven-Point Sphere of the Tetrahedron | 10.5281/zenodo.23572917 | **主定理已完整证明**（阶段 1、2 完成；阶段 3 推论未做） |
| Five Theorems on the Orthocentric Tetrahedron | 10.5281/zenodo.23579462 | **完成**：16 条陈述全部证明（2026-11-25） |
| Eleven Theorems on the Tetrahedron with a Midsphere | zenodo.org/records/24478275 | 未开始 |

## 目录结构

整个 `lean/` 是**一个** Lake 项目，三篇论文共用一份 Mathlib（缓存约 5 GB，三个项目就是 15 GB，而且 Mathlib 版本可能各不相同）。

```
lean/
├── ROADMAP.md               本文件
├── lakefile.toml
├── lean-toolchain
├── GeometryResearch/
│   ├── Common/              三篇共用的基础引理（外心、反演、第二交点的展开公式等）
│   ├── SevenPoint/          七点球
│   ├── Orthocentric/        垂心四面体
│   └── Midsphere/           棱切球四面体
└── .lake/                   Mathlib 缓存和编译产物，不进仓库
```

## 规矩

- 只在 `lean/` 下新建和修改文件，不动仓库里其他文件。
- 不 commit、不 push、不删除文件，除非作者另行同意。
- `.lake/` 不进仓库。`lake new` 会把它写进项目自己的 `.gitignore`，先确认。
- 不写 `axiom`，不改 Mathlib。
- 定义里不允许 `sorry`。在写陈述的阶段，只有定理和引理的**证明**可以是 `sorry`。
- Mathlib 的 API 名字随版本变化。用到的名字一律先在当前 Mathlib 源码里 grep 确认，不存在或签名不同就如实记录，不要猜。
- 每个阶段做完写汇报，**停下来等作者审过**再进入下一阶段。

## 七点球（试点）

### 论文定理（Theorem 1）

四面体 V₀V₁V₂V₃，外心 O，外接球半径 R，重心 G；O′、H′ 分别是对面 V₁V₂V₃ 的外心和垂心。设 G ≠ O、O′ ≠ O。那么下列七个点在同一个与球 S(O, 2R) 正交的 Möbius 球（球或平面）上。若 O、G、O′、V₀ 不共面，这是唯一的一个真正的球；若共面，七点落在一个过 O 的平面上。

| # | 点 | 论文定义 | 建议的 Lean 定义 |
|---|---|---|---|
| 1 | A | 直线 V₀G 与外接球的第二个交点 | `Sphere.secondInter` |
| 2 | B | 面 V₁V₂V₃ 所在平面关于外接球的极点 | `inversion O R O′`（配极点引理） |
| 3 | C | 4G − 3V₀ | `AffineMap.homothety G (-3) V₀` |
| 4 | H′ | 面 V₁V₂V₃ 的垂心 | 面三角形的 `orthocenter` |
| 5 | E | G 关于外接球的反演点 | `EuclideanGeometry.inversion O R G` |
| 6 | D | 4G − 3O | `AffineMap.homothety O 4 G` |
| 7 | F | 4O′ − 3O | `AffineMap.homothety O 4 O′` |

### 阶段 1：搭环境 + 写形式陈述（证明用 `sorry`）　✅ 2026-11-24 完成

**1A. 环境**

1. 先查磁盘剩余空间（Mathlib 缓存约 5 GB）。
2. 安装 elan，`elan --version` 能出版本号。
3. 在 `lean/` 用 Mathlib 模板建项目，`lake exe cache get` 下载预编译的 Mathlib（不要从源码编译），`lake build` 通过。
4. 冒烟测试 `GeometryResearch/Smoke.lean`：证明 ‖x + y‖² = ‖x‖² + 2⟪x, y⟫ + ‖y‖²，确认 `lake build` 真的在检查证明。
5. 记录 Lean 版本、Mathlib commit、实际执行的命令、耗时、磁盘占用。

**1B. 形式陈述**

- 空间：`EuclideanSpace ℝ (Fin 3)`。试点越具体越好，出了问题容易查；推广到一般三维欧氏空间留到以后。
- 四面体：`Affine.Simplex ℝ P 3`。外心、半径、重心、对面、面的外心、面的垂心、反演、第二交点都用 Mathlib 已有的定义。
- 七个点各写一个 `def`，名字与论文一致（`pointA` …），每个附一行注释，对应论文表格的哪一行。

要写出的陈述：

1. **A 的忠实性引理**：A 在外接球上，在直线 V₀G 上，且 A ≠ V₀。
2. **B 的忠实性引理（极点引理）**：若 O′ ≠ O，则面 V₁V₂V₃ 所在平面上任一点 X 都满足 ⟪X − O, B − O⟫ = R²。
3. **主定理，Möbius 形式**：若 G ≠ O、O′ ≠ O，则存在不全为零的 (α, c) ∈ ℝ × V，使七个点 X 都满足 α‖X − O‖² − 2⟪c, X − O⟫ + 4αR² = 0。
   - α ≠ 0 时，这是以 O + c/α 为心、与 S(O, 2R) 正交的球。
   - α = 0 时，这是一个过 O 的平面。
4. **主定理，非退化形式**：若 `AffineIndependent ℝ ![O, G, O′, V₀]`（它已经推出 G ≠ O、O′ ≠ O），则存在**唯一**的球 s，满足：
   - 七个点都在 s 上；
   - s 与 S(O, 2R) 正交，即 dist(s.center, O)² = s.radius² + (2R)²。
   - 唯一性写成：任何经过这七个点的球都等于 s。
5. **平面形式**（可选）：若 O、G、O′、V₀ 共面，七个点在一个过 O 的平面上。

**1C. 汇报**（写进 `GeometryResearch/SevenPoint/汇报_阶段1.md`，然后停下）

1. 环境：版本、命令、耗时、磁盘占用；冒烟测试是否通过。
2. 完整的形式陈述原文（所有 `def` 和定理）。
3. 对照表：每个 Lean 定义对应论文的哪个对象，用了哪些 Mathlib 定义（名字和所在文件）。
4. 与论文有出入的地方，以及所做的选择和理由。尤其要写清：
   - `faceOpposite`（或 `face`）取出的是哪三个顶点、顺序如何，O′ 是不是那个面自己的外心；
   - H′ 用的是哪个垂心定义；
   - B 为什么用反演 O′ 来定义；
   - 「不共面」怎么表达。
5. `lake build` 的输出：只应有 `sorry` 警告，没有错误。
6. 对阶段 2 的预估：哪些引理 Mathlib 已有，哪些要自己证，哪一步最难。

### 阶段 2：证明主定理　✅ 2026-11-24 完成，见 `GeometryResearch/SevenPoint/汇报_阶段2.md`

按论文第 2 节的证明翻译，分三层：

1. **代数核心**：平移使 O 为原点，记 vᵢ = Vᵢ − O。只用内积和向量，假设 ‖vᵢ‖ = R、⟪vᵢ − o′, o′⟫ = 0，证明「(α, c) 满足论文的三个线性方程 (G)、(O′)、(V₀)，则七个点都在 Σ(α, c) 上」。每个点展开内积后用 `linear_combination` 给出系数。
2. **解的存在**：三个方程、四个未知数，必有非零解。用 Mathlib 里线性映射 ℝ⁴ → ℝ³ 的核非零的引理。
3. **几何包装**：证明 Mathlib 的标准定义等于代数核心里用的向量表达式：
   - 面的外心 O′ 是 O 在面所在平面上的正交投影；
   - 面的垂心 H′ = O′ + Σᵢ₌₁³(Vᵢ − O′)（Sylvester 关系，对应 Mathlib 里 Monge 点的公式）；
   - `secondInter`、`inversion` 的显式公式。

预计第 3 层最费力：这几条引理 Mathlib 不一定都有现成的，可能要自己证，适合放进 `Common/` 供另外两篇复用。

### 阶段 3：退化情形与推论

- 非退化情形的唯一性（若阶段 2 未完成）。
- 平面形式。
- 推论：四个七点球都与 S(O, 2R) 正交、都过 D 和 E、球心共面、直线 OG 上的点对四个球等幂。

## 之后

试点跑通后，再评估另外两篇：

- **垂心四面体**：✅ 2026-11-25 完成，16 条陈述全部证明，见 `GeometryResearch/Orthocentric/汇报_阶段1.md`。定理 5 没有用论文的稠密性论证，而是用 Singular 生成、Lean 验证的代数证书覆盖全部情形。
- **棱切球四面体**：🟡 2026-11-25 进行中：19 条陈述中已证 15 条（论文 11 条定理中的定理 1、2、3、4、5、8、9、10，以及 8 条辅助陈述中的 7 条），4 条仍是 `sorry`，见 `GeometryResearch/Midsphere/汇报.md`。原计划：定理 1、2、3、9、10 是手算证明，适合先做。定理 4–8 和 10 的符号计算部分需要评估 `ring`、`field_simp` 能不能处理。定理 11 依赖 Gröbner 基证书，可以考虑在 Lean 里直接核对证书中的多项式恒等式（`ring` 或 `linear_combination`）。
