#!/bin/sh
# 一键检测：编译、搜索自定义公理、对三个 Statement.lean 的全部定理运行 #print axioms。
# sorry 和 native_decide 会在 #print axioms 里分别显示为 sorryAx、Lean.ofReduceBool，所以第 3 步也能抓到它们。
# 用法：在 lean/ 目录下运行 ./check.sh
set -e
cd "$(dirname "$0")"
export PATH="$HOME/.elan/bin:$PATH"

echo "== 1. 编译（不许有错误和警告）"
log=$(lake build 2>&1) || { printf '%s\n' "$log"; exit 1; }
if printf '%s\n' "$log" | grep -E "warning|sorry"; then
  echo "失败：编译有警告或 sorry" >&2
  exit 1
fi
echo "通过"

echo "== 2. 搜索自定义公理、unsafe、implemented_by"
if grep -rnE "^[[:space:]]*(axiom|unsafe|@\[implemented_by)" GeometryResearch --include=*.lean; then
  echo "失败：发现上面这些行" >&2
  exit 1
fi
echo "没有发现"

echo "== 3. #print axioms"
tmp=$(mktemp -d)
f="$tmp/Axioms.lean"
echo "import GeometryResearch" > "$f"
for d in SevenPoint Orthocentric Midsphere; do
  grep -oE "^theorem [^ ]+" "GeometryResearch/$d/Statement.lean" |
    awk -v d="$d" '{print "#print axioms GeometryResearch." d "." $2}' >> "$f"
done
out=$(lake env lean "$f" 2>&1)
rm -rf "$tmp"
n=$(printf '%s\n' "$out" | grep -c "depends on axioms" || true)
bad=$(printf '%s\n' "$out" | grep -v "depends on axioms: \[propext, Classical.choice, Quot.sound\]" || true)
if [ -n "$bad" ]; then
  printf '%s\n' "$bad" >&2
  echo "失败：上面这些定理用到了标准公理以外的东西" >&2
  exit 1
fi
echo "$n 条定理，全部只依赖 propext、Classical.choice、Quot.sound"
echo "== 全部通过"
