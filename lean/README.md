# Lean 形式化

用 Lean 4 + Mathlib 形式化三篇论文的主定理。路线图见 [ROADMAP.md](ROADMAP.md)。

## 环境

| 项目 | 版本 |
|---|---|
| elan | 4.4.0 |
| Lean | `leanprover/lean4:v4.37.0-rc1`（见 `lean-toolchain`） |
| Mathlib | tag `v4.37.0-rc1`，commit `31ce06eaadf4a200c0e1407c5f10953cf606b8f8`（见 `lake-manifest.json`） |

## 从零搭建（2026-11-24 实际执行的命令）

```sh
# 1. 安装 elan（Lean 版本管理器），不预装工具链
curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -o elan-init.sh
sh elan-init.sh -y --default-toolchain none
export PATH=$HOME/.elan/bin:$PATH

# 2. 在 lean/ 里用 Mathlib 模板初始化项目（lean/ 已存在，所以用 init 而不是 new）
cd lean
lake +leanprover-community/mathlib4:lean-toolchain init GeometryResearch math
#    这一步会自动下载 Mathlib 的预编译缓存（9133 个文件）

# 3. 编译
lake build
```

| 步骤 | 耗时 | 磁盘 |
|---|---|---|
| 安装 elan | 约 1 秒 | |
| 初始化项目 + 下载 Mathlib 缓存 | 约 80 秒 | `.lake/` 7.8 GB |
| Lean 工具链 | | `~/.elan/` 3.3 GB |
| 第一次 `lake build`（模板） | 约 2 秒 | |
| 编译一个 `import Mathlib` 的文件 | 约 30–40 秒 | |

`.lake/` 已写在项目的 `.gitignore` 里，不进仓库。

## 结构

```
GeometryResearch.lean              库入口，import 下面各文件
GeometryResearch/Smoke.lean        冒烟测试：‖x + y‖² = ‖x‖² + 2⟪x, y⟫ + ‖y‖²
GeometryResearch/SevenPoint/
  Defs.lean                        定义：四面体的基本对象和七个点
  Algebra.lean                     代数核心（只用内积和向量）
  Geometry.lean                    Mathlib 定义到向量公式的展开
  Statement.lean                   七个定理的陈述和证明
  汇报_阶段1.md、汇报_阶段2.md       阶段汇报
GeometryResearch/Orthocentric/
  Defs.lean                        定义：垂心四面体、H、p、aᵢ、ψ、共轭、Fermat 点等
  Model.lean                       代数模型（以 O、H 为原点）和核心关系 Σvᵢ/aᵢ = 0
  Thirteen.lean                    定理 1（十三点球）
  Conj.lean                        定理 2、3（两条欧拉线上的共轭）
  Seven.lean                       定理 4（七线共点）
  Fermat.lean                      定理 5（Fermat 共线），含 Singular 生成的代数证书
  Statement.lean                   16 条陈述及其证明
  fermat_cert.sing                 生成定理 5 证书的 Singular 脚本
  numeric_check.py                 陈述的数值核对
  汇报_阶段1.md                     汇报（陈述、审查、三批证明）
GeometryResearch/Midsphere/        棱切球四面体（进行中，见 Midsphere/汇报.md）
  Defs.lean、Statement.lean        定义与 19 条陈述
  Model.lean、Faith.lean、Central.lean、Tangent.lean、GMPlane.lean、Soddy.lean、Orth.lean、
  Homothety.lean                   已证部分的证明
  numeric_check.py                 陈述的数值核对（笛卡儿坐标）
GeometryResearch/Basic.lean        模板自带的空文件
```

## 检查

```sh
lake build
```

应当零错误、零警告、零 `sorry`。七点球的七个定理、垂心四面体的 16 条陈述都已证明，`#print axioms` 只显示 `propext`、`Classical.choice`、`Quot.sound` 三条标准公理。

## 配置说明

`lakefile.toml` 里关掉了 `linter.style.header`：这是 Mathlib 对自身源文件版权头格式的检查，不适用于本项目。其余 Mathlib 风格检查保持开启。
