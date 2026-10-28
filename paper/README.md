# 论文 PDF 草稿

- [阅读 PDF](hintz_formalization.pdf)
- [LaTeX 源稿](hintz_formalization.tex)
- [数学证明与源码对应索引](PROOF_MAP.md)

英文稿面向物理学家和数学家，用通常的微分算子、矩阵恒等式及
自然语言证明，完整展开正负自旋的局部等价
system (1) ⇔ system (4) ⇔ system (7)。
附录给出一个逐项演算的例子，以及同时覆盖全部八个残差分量的统一证明。
正文不解释 Lean 语法或证明策略。

稿件区分局部等价与变量分离、谱论、模稳定性；后几项不是本仓库主定理
的结论。原方程及变换归于 Peter Hintz 的 arXiv:2609.33661v1。
He Wang 的作者信息沿用仓库的 CITATION.bib；作者栏另列 GPT-6.1 Sol
和 Claude Code Opus 5.5，并以脚注注明 AI 贡献者身份。
本稿尚未经独立同行评阅或投稿。

在仓库根目录编译：

~~~sh
tectonic --keep-logs --outdir paper paper/hintz_formalization.tex
~~~

也可使用 pdfLaTeX，运行两次以解析交叉引用：

~~~sh
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=paper paper/hintz_formalization.tex
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=paper paper/hintz_formalization.tex
~~~

本次使用 Tectonic 0.17.0 生成 PDF；具体数学核对及仓库构建审计记录见
[PROOF_MAP.md](PROOF_MAP.md)。最终 PDF 另经交叉引用、字体、页面边界和
公式版面检查。
