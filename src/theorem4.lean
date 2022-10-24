import analysis.special_functions.pow
import analysis.special_functions.complex.log

import approach_one_symbol

open real fintype

open_locale big_operators

noncomputable theory

variables {ι : Type} [fintype ι] [decidable_eq ι]
(q₁ q₂ : ι → ℝ) [rnd_var_1 q₁] [rnd_var_1 q₂]
(r T : ℝ) [T = err_exp_1 q₁ q₂ r - r]

def M (q₁ q₂ : ι → ℝ) (k : ι) (r s : ℝ) : ℝ :=
((q₁ k / q₂ k) * exp(r - (err_exp_1 q₁ q₂ r) ))^(s/(1+s))

/-- Thm. 4 in Blahut74 -/
theorem err_exp_of_s :
∃ s, err_exp_1 q₁ q₂ r = -s*r - (1+s)*log(∑ k, ((q₂ k) * (q₁ k)^s)^(s/(1+s)) ) := sorry

/-- Thm. 4 in Blahut74 rewrite -/
theorem exp_err_exp_of_s (r T : ℝ) :
∃ s, exp(-err_exp_1 q₁ q₂ r) = ∑ k, (q₂ k) * (M q₁ q₂ k r s) := sorry