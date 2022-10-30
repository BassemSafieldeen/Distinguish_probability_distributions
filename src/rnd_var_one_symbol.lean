import algebra.big_operators
import analysis.special_functions.pow
import analysis.special_functions.complex.log

open real finset

open_locale big_operators

noncomputable theory

variables {ι : Type} [fintype ι] [decidable_eq ι]

/-- prob of symbol -/
class rnd_var_1 (q : ι → ℝ) :=
(probs_pos  : ∀ k, q k > 0) -- "we will assume for later convenience strictly positive components"
(sum_probs_one : ∑ k, q k = 1)

/-- relative entropy -/
def discrimination_1 (q₁ q₂ : ι → ℝ) : ℝ :=
∑ k, (q₁ k) * (log(q₁ k) - log(q₂ k))

def err_exp_1 (q₁ q₂ : ι → ℝ) (ε : ℝ) :=
Inf { b : ℝ | ∃ q, b = discrimination_1 q q₂ ∧ discrimination_1 q₁ q ≤ ε }