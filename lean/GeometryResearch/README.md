# 四面体定理的 Lean 形式化

这个目录用 Lean 4 + Mathlib 证明了三篇论文中关于四面体的 **17 条主定理**。证明全部由 Lean 的内核逐步检查，不依赖任何未经证明的假设。

| 部分 | 论文 | 主定理 | 形式陈述 | 状态 |
|---|---|---|---|---|
| [`SevenPoint/`](SevenPoint/) | *A Seven-Point Sphere of the Tetrahedron*（[Zenodo](https://doi.org/10.5281/zenodo.23572917)） | 1 | 8 | 全部证完 |
| [`Orthocentric/`](Orthocentric/) | *Five Theorems on the Orthocentric Tetrahedron*（[Zenodo](https://doi.org/10.5281/zenodo.23579462)） | 5 | 16 | 全部证完 |
| [`Midsphere/`](Midsphere/) | *Eleven Theorems on the Tetrahedron with a Midsphere*（[Zenodo](https://zenodo.org/records/24478275)） | 11 | 20 | 全部证完 |
| 合计 | | **17** | **44** | 零 `sorry` |

「形式陈述」比主定理多，多出来的是**忠实性引理**和**存在性引理**。忠实性引理检查我们自己写的定义确实是论文里的概念，例如「`S2 i` 确实是第 i 个面面积的平方」「`X11` 确实同时在面的九点圆和内切圆上」。存在性引理检查定理的假设能被满足，例如 Soddy 球存在、Fermat 点存在，防止定理因为假设互相矛盾而空真。

## 证明了什么

**七点球**（`SevenPoint/Statement.lean`）
- 一般四面体中，七个点共球，这个球与 S(O, 2R) 正交，并且唯一（`seven_point_sphere`）。
- 另有 Möbius 形式（`mobius_sphere`），以及退化时七点共面的平面形式（`seven_point_plane`）。

**垂心四面体**（`Orthocentric/Statement.lean`）
1. 十三点球（`thirteen_point_sphere`）
2. 欧拉线共轭平面（`euler_line_conjugate_plane`）
3. 第二欧拉线上的共轭共线（`second_euler_line_collinear`）
4. 七线共点（`seven_lines_chord`、`seven_lines_midpoint`）
5. Fermat 共线（`fermat_collinear`）

**棱切球四面体**（`Midsphere/Statement.lean`）
1. 中心平面（`central_plane`）
2. GM 共轭平面（`gm_conjugate_plane`）
3. 八点球（`eight_point_sphere`）
4. 中心平面上的四点共圆（`concyclic_four`）
5. 三个五点球（`five_point_5`、`five_point_6`、`five_point_7`），分别是定理 5、6、7
8. 位似引理（`homothety_lemma`）
9. 正交球引理（`orthogonal_sphere`）
10. Soddy 五点球（`soddy_five_point`）
11. Fermat 线（`fermat_line`）

每条陈述的确切假设和结论，以 `Statement.lean` 里的 Lean 代码为准，文档注释写了与论文的对应关系。

## 怎么做的

- **定义贴近 Mathlib**：四面体是 Mathlib 的 `Affine.Simplex ℝ E3 3`。外心、外接球、内心、九点圆、高、反演等尽量直接用 Mathlib 已有的定义，不自己重新定义，减少「定义写错」的空间。
- **重心坐标模型**：大部分证明把点写成重心坐标，距离用 |XY|² = −½ΣΣuₐu_b e_ab 计算，把几何命题化成切长或棱长的有理恒等式，再用 `field_simp`、`ring`、`linear_combination` 完成。
- **「共球或共面」的统一判据**：论文按 Möbius 约定把平面也算作球。Lean 里写成 `Cospherical S ∨ Coplanar ℝ S`，证明时找一个广义球方程 α|X|² + ℓ(X) = 0：α ≠ 0 是球，α = 0 是平面。
- **代数证书**：垂心四面体定理 5 和棱切球定理 11 需要理想成员关系，证书由 Singular 计算（脚本见 `Orthocentric/fermat_cert.sing`）。证书本身是 Lean 代码，由 `linear_combination` 重新检查，Lean 不信任 Singular 的输出。
- **与论文证明不同的地方**：棱切球定理 3、10 论文用反演，这里改成纯代数证明。定理 11 没有用论文的伪逆引理和连续性论证，改成直接计算。这些改动只涉及证明，不改变陈述。

各部分的详细做法、遇到的问题和审查记录见：
- [`SevenPoint/汇报_阶段1.md`](SevenPoint/汇报_阶段1.md)、[`SevenPoint/汇报_阶段2.md`](SevenPoint/汇报_阶段2.md)
- [`Orthocentric/汇报_阶段1.md`](Orthocentric/汇报_阶段1.md)
- [`Midsphere/汇报.md`](Midsphere/汇报.md)

## 定义从哪里来

Lean 只保证「从定义推出结论」，保证不了定义就是论文里的那个对象。所以读 `Statement.lean` 之前，最好先知道每个对象是怎么定义的。三个 `Defs.lean` 里的定义分成三类。

**一、直接用 Mathlib 的定义。** 这些不是我们写的，出错的余地最小。

| 对象 | Mathlib 定义 |
|---|---|
| 四面体、面 | `Affine.Simplex ℝ E3 3`、`faceOpposite` |
| 外心、外接球半径、外接球 | `circumcenter`、`circumradius`、`circumsphere` |
| 重心、面的重心 | `Finset.centroid`、`faceOppositeCentroid` |
| 垂心四面体的垂心 H | `mongePoint`（另有 `H_mem_altitude` 证明它在四条高上） |
| 高的垂足、面三角形的垂心 | `altitudeFoot`、`Affine.Triangle.orthocenter` |
| 面的内心、内切圆半径、九点圆 | `incenter`、`inradius`、`ninePointCircle` |
| 反演、直线与球的第二交点、平面的极点 | `inversion`、`Sphere.secondInter`、`Sphere.pole` |
| 位似、中点、正交投影 | `AffineMap.homothety`、`midpoint`、`orthogonalProjection` |
| 共球、共面、共线 | `Cospherical`、`Coplanar`、`Collinear` |

**二、自己定义，但按几何性质定义。** 定义本身就是论文里的几何描述，不是公式。

| 对象 | 定义 |
|---|---|
| 垂心四面体 | 三对对棱都互相垂直 |
| Fermat 点 | 到四个顶点距离之和**最小**的点（不是「单位向量之和为零」，后者在 Lean 里是证出来的） |
| 四球四面体 | 四个球两两外切：rᵢ > 0，\|VᵢVⱼ\| = rᵢ + rⱼ |
| 切点 Tᵢⱼ | 棱 VᵢVⱼ 上距 Vᵢ 为 rᵢ 的点（`T_spec` 证明它在线段上，到两端距离为 rᵢ、rⱼ） |
| Soddy 球 | 与四个球都相切的球：\|SVᵢ\|² = (ρₛ + rᵢ)²，ρₛ ≠ 0。`exists_soddy` 证明存在两个，`soddy_curvature` 证明曲率恰为 s/2 ± 3√D，没有别的 |
| Soddy 球的切点、Nᵢⱼ\|ₖₗ、棱切球半径 | 直线上的点、两点中点、\|MT₀₁\| |
| 「共球」 | `Cospherical S ∨ Coplanar ℝ S`，即论文的 Möbius 约定（平面也算球） |

**三、自己定义，用公式。** 每一个都配了一条忠实性引理，证明公式确实给出论文的几何对象。

| 对象 | 公式 | 忠实性引理 |
|---|---|---|
| 面积的平方 Sᵢ² | Gram 行列式 (\|u\|²\|w\|² − ⟪u, w⟫²)/4 | `S2_eq`：等于 (½·\|PQ\|·\|PR\|·sin∠QPR)² |
| Zeeman 点 Z | 重心坐标 (1/rᵢ) | `Z_mem_chord`：Z 在三条对棱切点连线上 |
| 棱切球心 M | 重心坐标 (s/(2rᵢ) − 1/rᵢ²) | `M_tangent`：球 (M, ρ) 过六个切点，并在那里与棱相切 |
| 类似重心 K | 重心坐标 (Sᵢ²) | `K_spec`：K 是 G 的等角共轭 |
| Feuerbach 点 X₁₁ | 论文 (5.1) 的重心坐标 rᵢ(rₖ − rₘ)² | `X11_faithful`：X₁₁ 同时在面的九点圆和内切圆上。两圆相切（Feuerbach 定理），公共点只有一个，所以这就刻画了 Feuerbach 点 |
| 外位似中心 Eₖₗ | (rₗVₖ − rₖVₗ)/(rₗ − rₖ) | `Eext_spec`：以它为中心、比 rₗ/rₖ > 0 的位似把 Σₖ 映成 Σₗ |
| 中点球、参数 p 和 aᵢ | 论文第 2 节的定义原样照抄 | `inner_eq_p`、`a_eq`、`dist_mid_G` |
| 极反演 ψ | ψ(X) = H + p(X − H)/\|X − H\|² | `ψ_point`：ψ 把顶点映到高的垂足 |

**需要特别说明的一处：等角共轭和等截共轭。** 两者按重心坐标定义：P* = (Sᵢ²/xᵢ)，Pᵗ = (1/xᵢ)。两篇论文的第 2 节都是这样定义的，所以与论文一致。论文接着说明了它们的几何意义：把过一条棱和 P 的平面，关于这条棱处二面角的平分面作反射，得到过 P* 的平面。这条几何刻画**没有**形式化。如果读者心目中的等角共轭是这个几何定义，二者的等价需要另外证明。

## 怎样确认它们都通过了检测

在 `lean/` 目录下运行：

```sh
./check.sh
```

脚本做三件事，任何一步不通过都会报错退出：

1. **编译**：`lake build` 必须零错误、零警告。Lean 的内核在这一步检查每一个证明。
2. **搜索后门**：源码里不能有自定义 `axiom`、`unsafe` 或 `@[implemented_by]`。
3. **`#print axioms`**：对三个 `Statement.lean` 里的全部 44 条定理逐一检查，每条都只能依赖 Lean 的三条标准公理 `propext`、`Classical.choice`、`Quot.sound`。
   - 用了 `sorry` 的证明会在这里显示 `sorryAx`。
   - 用了 `native_decide` 的证明会显示 `Lean.ofReduceBool`。
   - 所以这一步能抓住所有「没真正证完」的情况。

当前（提交 9b96836 之后）的输出：

```
== 1. 编译（不许有错误和警告）
通过
== 2. 搜索自定义公理、unsafe、implemented_by
没有发现
== 3. #print axioms
44 条定理，全部只依赖 propext、Classical.choice、Quot.sound
== 全部通过
```

第一次运行需要先按 [`../README.md`](../README.md) 安装 Lean 和下载 Mathlib 缓存。

### 机器检查之外的两道检查

Lean 能保证「证明是对的」，不能保证「陈述写的就是论文的意思」。所以另外做了两件事：

- **数值核对**：`Orthocentric/numeric_check.py`、`Midsphere/numeric_check.py` 在笛卡儿坐标里严格按 Lean 的定义计算，随机取四面体检验每条陈述，误差在 10⁻³⁹ 量级。故意写错一个定义，误差就变成 10⁻³ 到 10⁻¹ 量级，说明这个核对确实能发现错误。数值核对还确认了「共球或共面」的点在一般位置下不共面，所以结论不是平凡成立的。
- **独立审查**：陈述和证明都交给 Codex 独立审查过。审查的内容包括：陈述是否忠实于论文，假设是否会互相矛盾，「或共面」会不会让定理变平凡。审查发现的问题都已修正：例如七点球的唯一性原先写得比论文弱，已补强为「经过这七个点的球只有一个」；垂心四面体去掉了两个多余的假设。最后一轮审查确认当时的 43 条陈述无需再改（之后只新增了一条忠实性引理 `Eext_spec`，见下一节）。审查记录在各部分的汇报里。

## 没有形式化的部分

- 七点球论文的推论：四个七点球都与 S(O, 2R) 正交、都过 D 和 E、球心共面、直线 OG 上的点对四个球等幂。
- 棱切球论文中 Soddy 球退化为平面的情形（定理 3、9、10 的陈述要求 Soddy 球半径不为 0）。
- 棱切球定理 8 之后的推论。

## 目录

```
SevenPoint/      七点球：Defs（定义）、Algebra（代数核心）、Geometry（Mathlib 定义展开）、Statement
Orthocentric/    垂心四面体：Defs、Model（代数模型）、Thirteen、Conj、Seven、Fermat、Statement
Midsphere/       棱切球四面体：Defs、Model、各定理的证明文件、Statement
Smoke.lean       冒烟测试
Basic.lean       模板自带的空文件
```

每个部分都从 `Statement.lean` 读起：它列出全部陈述，每条证明只是一行对主引理的引用，主引理在同目录的其他文件里。
