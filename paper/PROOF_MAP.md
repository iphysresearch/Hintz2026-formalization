# Mathematical proof map

The [paper](hintz_formalization.pdf) gives a mathematical exposition of the
local equivalence proved by this repository. This separate index connects
its argument to all 27 modules in the main theorem's local import closure.
Module links refer to the checked working tree; the source revision is
0beae5d183d73d0847f4ea2e163063c47d853a17.

| Paper location and mathematical step | Source modules and principal declarations |
| --- | --- |
| Sections 1–2: subextremal parameters, exterior domain, nonzero denominators | [Domain.lean](../Hintz2026/Domain.lean); [Derivatives.lean](../Hintz2026/Derivatives.lean) |
| Section 2.2: the physical dictionary for Weyl scalars and spin coefficients | Background conventions from [Hintz, arXiv:2609.33661v1](https://arxiv.org/abs/2609.33661v1); the local proof starts with system (1) |
| Section 2: Fourier mode operators and the eight original residuals | [System1Defs.lean](../Hintz2026/System1Defs.lean) |
| Section 2: the derivatives \(D_\pm\) and derivatives of \(\rho,\rho^*\) | [Eq6.lean](../Hintz2026/Eq6.lean) |
| Section 3: positive prefactors and their derivatives | [Prefactors.lean](../Hintz2026/Prefactors.lean) |
| Section 3: positive- and negative-spin chiral fields | [Chiral.lean](../Hintz2026/Chiral.lean); [ChiralSmooth.lean](../Hintz2026/ChiralSmooth.lean) |
| Section 3: \(b,c,B\) and the intermediate equations | [System4Defs.lean](../Hintz2026/System4Defs.lean) |
| Proposition 3.1 and Appendix A: scalar product rules and normalized fields | [Eq1to4Identity.lean](../Hintz2026/Eq1to4Identity.lean) |
| Proposition 3.1 and Appendix A: all positive-spin residual identities | [Eq1to4Pos.lean](../Hintz2026/Eq1to4Pos.lean), ident_m0, ident_m1, ident_p0, ident_p1 |
| Proposition 3.1 and Appendix A: all negative-spin residual identities | [Eq1to4Neg.lean](../Hintz2026/Eq1to4Neg.lean), identN_m0, identN_m1, identN_p0, identN_p1 |
| Proposition 3.1: invertible elimination of original residuals | [Equivalence1to4.lean](../Hintz2026/Equivalence1to4.lean), sys1_iff_sys4_pos, sys1_iff_sys4_neg |
| Remark 3.2: equivalence at zeros of \(F_-\) | Consequence of the displayed residual identities and an elementary example; no division by \(F_\pm\) occurs |
| Section 4.1: \(X,A\), constant determinant, Hermiticity, inverses | [IntegratingFactor.lean](../Hintz2026/IntegratingFactor.lean), det_X, A_conjTranspose |
| Section 4.2: scalar entries and entrywise derivatives of \(X\) | [XEntries.lean](../Hintz2026/XEntries.lean); [XDerivatives.lean](../Hintz2026/XDerivatives.lean); [XDiagDeriv.lean](../Hintz2026/XDiagDeriv.lean) |
| Section 4.2: \(D_-X=AX\), inverse and conjugate-transpose inverse identities | [Assembly.lean](../Hintz2026/Assembly.lean), Dminus_X_eq_AX, Dm_Xinv_matrix, Dplus_XstarInv_eq |
| Proposition 4.2: matrix-vector product rules and residual transport | [Residual.lean](../Hintz2026/Residual.lean) |
| Corollary 4.3: homogeneous solution correspondence | [SolutionCorr.lean](../Hintz2026/SolutionCorr.lean) |
| Sections 4–6: smooth coefficients, multiplication and local differentiation | [Smooth.lean](../Hintz2026/Smooth.lean); [FieldInterface.lean](../Hintz2026/FieldInterface.lean) |
| Section 5: \(D_-\operatorname{adj}(X)\), \(D_+X^\dagger\) | [AdjDeriv.lean](../Hintz2026/AdjDeriv.lean), Dm_adj_matrix, Dp_Xstar_matrix |
| Section 5: \(C\) and the reverse implication | [Transform7.lean](../Hintz2026/Transform7.lean) |
| Section 5: the formula for \(\operatorname{adj}(C)\) | [CAdjugate.lean](../Hintz2026/CAdjugate.lean), adjugate_Cmat_eq |
| Propositions 5.1–5.2 and Corollary 5.3: both directions between systems (4) and (7) | [Equivalence4to7.lean](../Hintz2026/Equivalence4to7.lean), system4_iff_system7 |
| Theorem 1.1 and Section 6: final positive/negative-spin equivalences and inverse chiral maps | [MainTheorem.lean](../Hintz2026/MainTheorem.lean), main, main_pos, main_neg, invPos, invNeg and round-trip theorems |
| Section 6.1: deleting the angular derivative gives a nonzero residual | [XDerivatives.lean](../Hintz2026/XDerivatives.lean); [FieldInterface.lean](../Hintz2026/FieldInterface.lean), neg_control_witness |
| Section 7: candidate separated coefficients, with no proved decomposition of \(C\) | [CSeparation.lean](../Hintz2026/CSeparation.lean): definitions Rmat, Thmat, Csep only |

Appendix A.2 reorganizes the eight checked component identities into one
calculation using two independent signs. Its uniform notation is an
expository device; the source proves the components separately.
The elementary adjugate algebra and smoothness consequences in the paper
are written out using conventional matrix calculus.

The manuscript does not claim the derivation of system (1) from
Einstein–Maxwell theory, separation of variables, endpoint regularity,
spectral completeness, or mode stability. Those conclusions do not follow
from the local equivalence theorem.

Checks repeated on 28 October 2026:

- Source boundary: all 27 retained modules, permitted imports only.
- Placeholder scan: passed.
- Isolated build and theorem audit: lake build Hintz2026 MainAudit, exit 0;
  local record [paper-build-audit.log](../logs/paper-build-audit.log)
  (ignored by Git).
- The audited main theorems have axiom closure
  [propext, Classical.choice, Quot.sound].
- Independent manuscript arithmetic check: all eight normalized residual
  identities reduce exactly to zero for arbitrary field values and first
  derivatives, using rational symbolic algebra.

See [VERIFICATION.md](../docs/VERIFICATION.md) and
[REPRODUCIBILITY.md](../docs/REPRODUCIBILITY.md) for the pinned environment and
commands for rebuilding the proof archive. These checks establish the
stated proof boundary; they are separate from independent review of the
article's mathematical presentation.
