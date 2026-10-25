# Title

feat(Analysis/SpecialFunctions/Gamma): Gamma integral with a complex rate

# Body

Mathlib has `Complex.integral_cpow_mul_exp_neg_mul_Ioi`, which evaluates
`∫ t in Ioi 0, t ^ (a - 1) * exp (-(r * t)) = (1 / r) ^ a * Gamma a` for `0 < a.re` and a
**real** rate `0 < r`. This PR extends it to a **complex** rate with `0 < r.re`:

* `Complex.integral_cpow_mul_exp_neg_mul_Ioi_of_re_pos` — the formula above for `a r : ℂ` with
  `0 < a.re` and `0 < r.re`.
* `Complex.integrableOn_cpow_mul_exp_neg_mul_Ioi` — the integrand is integrable on `Ioi 0` under
  the same hypotheses.
* `Complex.differentiableAt_integral_cpow_mul_exp_neg_mul_Ioi` — the integral is
  complex-differentiable in `r` on the half-plane `0 < r.re`.

Proof: the integral is holomorphic in `r` on `{r | 0 < r.re}` (differentiation under the integral
sign, `hasDerivAt_integral_of_dominated_loc_of_deriv_le`, with dominating function
`t ^ a.re * exp (-(r₀.re / 2) * t)`); so is `(1 / r) ^ a * Gamma a`; the two agree on the positive
real axis by the existing lemma; the half-plane is connected, so the identity theorem
(`AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq`) gives equality everywhere.

The declarations are added at the end of `Mathlib/Analysis/SpecialFunctions/Gamma/Beta.lean`,
which already imports `Mathlib.Analysis.Complex.CauchyIntegral` (needed for
`DifferentiableOn.analyticOnNhd`), so no new imports are introduced; the main theorem is also
listed in the file's module docstring. A typical use is computing
oscillatory integrals such as `∫ t ^ (a - 1) * exp (-(δ ± i k) t) dt`, e.g. Bogoliubov
coefficients in physics.

Prior art: I could not find a complex-rate version in Mathlib (checked
`Analysis/SpecialFunctions/Gamma/*`, `Analysis/MellinTransform`, `Analysis/SpecialFunctions/Gaussian/*`,
and a search of open PRs).

<!-- 下面這段 AI 聲明請用你自己的話改寫或確認後再貼；之前兩個 PR 的做法是你寫中文原意、附英文翻譯並註明翻譯由 Claude 協助。 -->
AI disclosure: the proof was developed with substantial assistance from an AI coding agent
(Claude). It was checked by `lake build --wfail`, `lake exe runLinter` and `lake exe lint-style`
on `master` (`280e9fcd6`), and the axioms of all three new declarations are
`[propext, Classical.choice, Quot.sound]`.

---

🤖 Generated with [Claude Code](https://claude.com/claude-code)
