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
  Statement.lean                   七点球定理的形式陈述（证明待完成）
  汇报_阶段1.md                     阶段 1 汇报
GeometryResearch/Basic.lean        模板自带的空文件
```

## 检查

```sh
lake build
```

当前应输出 7 条 `declaration uses 'sorry'` 警告（七点球的 7 个待证定理），没有错误。

## 配置说明

`lakefile.toml` 里关掉了 `linter.style.header`：这是 Mathlib 对自身源文件版权头格式的检查，不适用于本项目。其余 Mathlib 风格检查保持开启。
