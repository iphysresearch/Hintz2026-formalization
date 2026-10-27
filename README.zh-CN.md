# Hintz2026 Lean 形式化证明

[English](README.md)

本仓库独立保存 `Hintz2026.main` 的 Lean 证明。定理位于
[`Hintz2026/MainTheorem.lean`](Hintz2026/MainTheorem.lean)，证明组合了
`main_pos` 与 `main_neg`。仓库包含主定理传递导入闭包中的 27 个模块、审计入口、
锁定配置和复现文档。

## 定理内容与范围

参数 `p : Hintz2026.SubextremalKN` 满足 `M > 0`、`Q ≠ 0`、`a² + Q² < M²`。令

```text
Δ(r) = r² − 2Mr + a² + Q²
r₊ = M + sqrt(M² − a² − Q²)
U = {(r, θ) : r > r₊, 0 < θ < π}。
```

对任意实频率 `ω`、实方位参数 `m` 及在 `U` 上光滑的复值场，主定理证明：
原系统 (1) 在任意 `x ∈ U` 成立，当且仅当显式变换后的场满足系统 (7)。
正、负两种自旋分别证明，再合并为 `Hintz2026.main`；证明经过系统 (4)、
手征变量变换和矩阵积分因子。方程编号对应 Lean 源文件引用的
[Hintz, arXiv:2609.33661v1](https://arxiv.org/abs/2609.33661v1)。

形式化范围是上述局部等价。它不包含从 Einstein–Maxwell 方程推导原系统、完整的
变量分离与谱论证或模稳定性证明。数学原文和本形式化软件应分别引用。

对应的任务页面是 Prove2Me 的
[Exact Vacuum Atlas III: Matrix Integrating Factors and Local Equivalence of Kerr–Newman Perturbation Systems](https://prove2.me/missions/Exact_Vacuum_Atlas_III%3A_Matrix_Integrating_Factors_and_Local_Equivalence_of_Kerr%E2%80%93Newman_Perturbation_Systems)。
该页面提供形式化任务及其背景；本仓库具体证明的陈述和适用范围以
`Hintz2026.main` 及上文说明为准。

## 固定环境

- Lean：`v4.33.1`，见 [`lean-toolchain`](lean-toolchain)。
- Mathlib：`0df444a360eaa60ab8c11dca51a86af692955474`。
- Lean 选项：`autoImplicit = false`。
- 命令行工具：Bash、Python 3.9 或更新版本、Git、ripgrep（`rg`）。

如尚无指定 Lean 版本，请通过 elan 安装该版本。复现时保留
[`lake-manifest.json`](lake-manifest.json)，不要运行 `lake update`。
初次下载固定依赖需要网络；压缩包包含源码和锁文件，依赖与构建产物在本地获取。
详见 [`docs/REPRODUCIBILITY.md`](docs/REPRODUCIBILITY.md)。

## 复现命令

在仓库根目录执行。每条 Lean/Lake 命令均经过隔离脚本并记录退出码：

```bash
python3 -I scripts/check_source_boundary.py
bash scripts/check_no_placeholders.sh
python3 -I scripts/run_logged.py logs/build.log \
  ./scripts/build_isolated.sh lake build Hintz2026
python3 -I scripts/run_logged.py logs/main-audit.log \
  ./scripts/build_isolated.sh lake build MainAudit
```

日志脚本把命令输出写入文件。检查结果：

```bash
tail -n 3 logs/build.log
rg "'Hintz2026.main' depends on axioms" logs/main-audit.log
tail -n 3 logs/main-audit.log
```

主定理的公理闭包应只有 `[propext, Classical.choice, Quot.sound]`；打印结果可能带
宇宙参数标注。审计还打印 `main_pos`、`main_neg` 及其 `*_on_U` 版本的陈述和公理闭包。
源码扫描检查保留的 Lean 文件中没有 `sorry`、`admit`、`native_decide` 或
`Lean.ofReduceBool`。

## Comparator 核验

Lean Comparator 将提交的解答与指定挑战及其允许公理进行核验。
**本包尚未声称通过 Comparator 核验。** 固定环境是否支持该命令，以及实际核验状态，
记录在 [`docs/VERIFICATION.md`](docs/VERIFICATION.md)。

附带的 `scripts/check_source_boundary.py` 检查 27 个模块的导入闭包、
`Hintz2026.*`/`Mathlib` 导入边界、入口、主定理声明锚点和证明占位符。
这个 Python 源码检查并非 Lean Comparator，也不能替代 Lean 构建、内核检查或公理审计。

## 使用定理

```lean
import Hintz2026.MainTheorem

#check Hintz2026.main
```

## 引用与 Zenodo

作者：**He Wang**（ORCID：[0000-0002-1353-391X](https://orcid.org/0000-0002-1353-391X)）。版本：**0.1.0**。

- DOI：[10.5281/zenodo.23684720](https://doi.org/10.5281/zenodo.23684720)
- [Zenodo 存档记录](https://zenodo.org/records/23684720)

版本 0.1.0 已于 2026-10-27 在 Zenodo 正式发布，许可证为 Apache-2.0。
引用本软件可使用 [`CITATION.bib`](CITATION.bib) 中的条目：

```bibtex
@misc{hintz2026_lean_formalization,
  author       = {Wang, He},
  title        = {{Hintz2026: A Lean 4 Formalization of the Local Equivalence of Kerr--Newman Perturbation Systems (1) and (7)}},
  year         = {2026},
  version      = {0.1.0},
  publisher    = {Zenodo},
  doi          = {10.5281/zenodo.23684720},
  url          = {https://doi.org/10.5281/zenodo.23684720},
  howpublished = {Lean 4 source code},
  note         = {Author ORCID: 0000-0002-1353-391X. Proof of Hintz2026.main. Lean v4.33.1; Mathlib 0df444a360eaa60ab8c11dca51a86af692955474. Licensed under Apache-2.0.}
}
```

## 生成上传压缩包

```bash
python3 -I scripts/make_release.py
```

脚本只打包 [`RELEASE_FILES.txt`](RELEASE_FILES.txt) 明确列出的文件，并生成 SHA-256
校验清单。Git 历史、`.lake`、本地日志、父项目无关材料和 Zenodo 页面快照均不收录。
发布后维护和后续版本核对 [`docs/PUBLISHING_CHECKLIST.md`](docs/PUBLISHING_CHECKLIST.md)，来源说明见
[`docs/PROVENANCE.md`](docs/PROVENANCE.md)。

## 许可证

本仓库使用 [Apache License 2.0](LICENSE)。已发布的 Zenodo 记录使用相同许可证。
