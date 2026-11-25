# 四面体定理的 Lean 形式化

这个目录用 Lean 4 + Mathlib 证明了三篇论文中关于四面体的 **17 条主定理**。证明全部由 Lean 的内核逐步检查，不依赖任何未经证明的假设。

| 部分 | 论文 | 主定理 | 形式陈述 | 状态 |
|---|---|---|---|---|
| [`SevenPoint/`](SevenPoint/) | *A Seven-Point Sphere of the Tetrahedron*（[Zenodo](https://doi.org/10.5281/zenodo.23572917)） | 1 | 8 | 全部证完 |
| [`Orthocentric/`](Orthocentric/) | *Five Theorems on the Orthocentric Tetrahedron*（[Zenodo](https://doi.org/10.5281/zenodo.23579462)） | 5 | 16 | 全部证完 |
| [`Midsphere/`](Midsphere/) | *Eleven Theorems on the Tetrahedron with a Midsphere*（[Zenodo](https://zenodo.org/records/24478275)） | 11 | 19 | 全部证完 |
| 合计 | | **17** | **43** | 零 `sorry` |

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

## 怎样确认它们都通过了检测

在 `lean/` 目录下运行：

```sh
./check.sh
```

脚本做三件事，任何一步不通过都会报错退出：

1. **编译**：`lake build` 必须零错误、零警告。Lean 的内核在这一步检查每一个证明。
2. **搜索后门**：源码里不能有自定义 `axiom`、`unsafe` 或 `@[implemented_by]`。
3. **`#print axioms`**：对三个 `Statement.lean` 里的全部 43 条定理逐一检查，每条都只能依赖 Lean 的三条标准公理 `propext`、`Classical.choice`、`Quot.sound`。
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
43 条定理，全部只依赖 propext、Classical.choice、Quot.sound
== 全部通过
```

第一次运行需要先按 [`../README.md`](../README.md) 安装 Lean 和下载 Mathlib 缓存。

### 机器检查之外的两道检查

Lean 能保证「证明是对的」，不能保证「陈述写的就是论文的意思」。所以另外做了两件事：

- **数值核对**：`Orthocentric/numeric_check.py`、`Midsphere/numeric_check.py` 在笛卡儿坐标里严格按 Lean 的定义计算，随机取四面体检验每条陈述，误差在 10⁻³⁹ 量级。故意写错一个定义，误差就变成 10⁻³ 到 10⁻¹ 量级，说明这个核对确实能发现错误。数值核对还确认了「共球或共面」的点在一般位置下不共面，所以结论不是平凡成立的。
- **独立审查**：陈述和证明都交给 Codex 独立审查过。审查的内容包括：陈述是否忠实于论文，假设是否会互相矛盾，「或共面」会不会让定理变平凡。审查发现的问题都已修正：例如七点球的唯一性原先写得比论文弱，已补强为「经过这七个点的球只有一个」；垂心四面体去掉了两个多余的假设。最后一轮审查确认 43 条陈述无需再改。审查记录在各部分的汇报里。

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
