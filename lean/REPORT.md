# 新几何定理的形式化：第一阶段成果

**七点球定理已在 Lean 4 + Mathlib 中完整证明**

2026 年 11 月 24 日

---

## 概要

过去几个月，我在 AI 辅助下发现了一批立体几何的新定理，分三篇论文发表在 Zenodo 上。从现在开始，我把这些定理逐一做成**形式化证明**：用证明助手 [Lean 4](https://lean-lang.org/) 和数学库 [Mathlib](https://github.com/leanprover-community/mathlib4) 写下定理和证明，由计算机逐步核对每一个推理步骤。

第一篇论文《A Seven-Point Sphere of the Tetrahedron》的主定理已经完成：

- 定理的全部结论都已证明，没有遗留任何未完成的步骤（Lean 里称为 `sorry`）；
- 证明只依赖 Lean 的三条标准公理，没有额外假设；
- 任何人都可以下载代码，在自己的电脑上重新检查。

代码：<https://github.com/dongzhang84/geometry-research/tree/main/lean>
本阶段的固定版本：<https://github.com/dongzhang84/geometry-research/tree/c73497f/lean>

## 形式化了什么

**七点球定理**（论文 Theorem 1）：任给一个四面体 V₀V₁V₂V₃，设外心为 O、外接球半径为 R、重心为 G，对面 V₁V₂V₃ 的外心和垂心分别为 O′、H′。下面七个点在同一个球上：

| 点 | 定义 |
|---|---|
| A | 直线 V₀G 与外接球的第二个交点 |
| B | 平面 V₁V₂V₃ 关于外接球的极点 |
| C | 4G − 3V₀（反补四面体的顶点） |
| H′ | 三角形 V₁V₂V₃ 的垂心 |
| E | G 关于外接球的反演点 |
| D | 4G − 3O |
| F | 4O′ − 3O |

这个球还与以 O 为心、2R 为半径的球正交。当 O、G、O′、V₀ 不共面时，经过这七点的球是唯一的；共面时，七点落在一个过 O 的平面上。

Lean 里写成三个定理，加上四条检查定义的引理：

| Lean 定理 | 内容 |
|---|---|
| `mobius_sphere` | 七点在同一个与 S(O, 2R) 正交的「广义球」（球或平面）上 |
| `seven_point_sphere` | 不共面时：七点在一个真正的球上，它与 S(O, 2R) 正交，且是经过七点的唯一的球 |
| `seven_point_plane` | 共面时：七点在一个过 O 的平面上 |
| `pointA_mem_circumsphere` 等 4 条 | 检查 A、B 的定义确实是论文里的点 |

定理陈述见 [`Statement.lean`](https://github.com/dongzhang84/geometry-research/blob/c73497f/lean/GeometryResearch/SevenPoint/Statement.lean)，七个点的定义见 [`Defs.lean`](https://github.com/dongzhang84/geometry-research/blob/c73497f/lean/GeometryResearch/SevenPoint/Defs.lean)。

## 怎样保证它是对的

形式化证明有两个层面要检查：**证明对不对**，以及**陈述是不是论文的意思**。

**证明**由 Lean 检查。`lake build` 零错误、零警告；用 `#print axioms` 查看，每个定理都只依赖 `propext`、`Classical.choice`、`Quot.sound` 三条标准公理，这也是 Mathlib 里几乎所有数学证明所依赖的公理。

**陈述**只能由人核对：Lean 只保证「从这些定义推出了这些结论」，不保证定义就是论文说的东西。这一步做了两轮：

1. 在 Python 里按 Mathlib 源码中的定义逐字算出七个点，用 50 位精度在具体四面体上检验每个定理；又故意把四个定义各改错一处，四处都被检验抓了出来。
2. 由另一个 AI 模型（Codex）独立审查定义和陈述是否忠实于论文。它确认七个点的定义都对，同时指出唯一性那一条比论文写得弱。这一处已经补强为「经过七点的任何球都唯一」，并重新证明。

## 规模

| 项目 | 数据 |
|---|---|
| Lean 代码 | 约 700 行，四个文件 |
| 用时 | 从安装工具到完成证明约 1 小时 |
| 工具 | Lean `v4.37.0-rc1`，Mathlib `v4.37.0-rc1` |
| 辅助 | Claude Code 编写形式化和证明，Codex 独立审查陈述 |

证明结构与论文第 2 节一致：七个点的「在球上」条件都化为三个线性方程，用 Lean 的 `linear_combination` 一行一个点地验证；Mathlib 里外心、垂心、反演、极点等定义，都展开成论文里用的向量公式。

## 自己验证

```sh
git clone https://github.com/dongzhang84/geometry-research.git
cd geometry-research/lean
curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain none
export PATH=$HOME/.elan/bin:$PATH
lake exe cache get     # 下载预编译的 Mathlib，约 8 GB
lake build             # 检查全部证明，应当零错误、零警告
```

## 下一步

| 论文 | 状态 |
|---|---|
| A Seven-Point Sphere of the Tetrahedron（[10.5281/zenodo.23572917](https://doi.org/10.5281/zenodo.23572917)） | **主定理已完成** |
| Five Theorems on the Orthocentric Tetrahedron（[10.5281/zenodo.23579462](https://doi.org/10.5281/zenodo.23579462)） | 下一步 |
| Eleven Theorems on the Tetrahedron with a Midsphere（[zenodo.org/records/24478275](https://zenodo.org/records/24478275)） | 之后 |

七点球论文里的推论（四个顶点的七点球都经过 D、E 等）和退化情形的完整刻画，留作下一阶段。

详细的路线图见 [`ROADMAP.md`](https://github.com/dongzhang84/geometry-research/blob/main/lean/ROADMAP.md)。
