import algebra.big_operators
import analysis.special_functions.pow
import analysis.special_functions.complex.log

import rnd_var

open_locale big_operators

open real

noncomputable theory

variables {ι : Type}
[fintype ι] [decidable_eq ι]

/-- prob of a sequence of n symbols -/
class n_rnd_var (qₙ : (ℕ → ι) → ℝ) :=
(probs_nonneg  : ∀ s, qₙ s ≥ 0)
(sum_probs_one : ∑ᶠ s, qₙ s = 1)

/-- qₙ kₙ = q(kₙ 1) * q(kₙ 2) * ...  -/
def iid (qₙ : (ℕ → ι) → ℝ) [n_rnd_var qₙ] (q : ι → ℝ) [rnd_var q] :=
∀ kₙ, qₙ kₙ = ∏ᶠ n, q (kₙ n)

variables {kₙ : ℕ → ι}
{qₙ : (ℕ → ι) → ℝ} [n_rnd_var qₙ]
{q : ι → ℝ} [rnd_var q]

lemma log_iid_rw [iid qₙ q] :
log(qₙ kₙ) = ∑ᶠ n, log(q (kₙ n)) := sorry

/-- relative entropy -/
def discrimination (q₁ q₂ : ι → ℝ) : ℝ :=
∑ k, (q₁ k) * (log(q₁ k) - log(q₂ k))

def n_discrimination (qₙ₁ qₙ₂ : (ℕ → ι) → ℝ) : ℝ :=
∑ᶠ kₙ, (qₙ₁ kₙ) * (log(qₙ₁ kₙ) - log(qₙ₂ kₙ))

/-- How close to q₂ can we get if we stay ε-close to q₁? -/
def err_exp (q₁ q₂ : ι → ℝ) [rnd_var q₁] [rnd_var q₂] (ε : ℝ) :=
Inf { b : ℝ | ∀ {q : ι → ℝ} [rnd_var q], (b = discrimination q q₂) ∧ (discrimination q₁ q ≤ ε) }

def n_err_exp (qₙ₁ qₙ₂ : (ℕ → ι) → ℝ) [n_rnd_var qₙ₁] [n_rnd_var qₙ₂] (ε : ℝ) :=
Inf { b : ℝ | ∀ {qₙ : (ℕ → ι) → ℝ} [n_rnd_var qₙ], (b = n_discrimination qₙ qₙ₂) ∧ (n_discrimination qₙ₁ qₙ ≤ ε) }

variables (q₁ q₂ : ι → ℝ) [rnd_var q₁] [rnd_var q₂] (ε : ℝ)

/-- can get δ-close to q₂ when ε-close to q₁ -/
def achieves_err_exp (q : ι → ℝ) [rnd_var q] (δ : ℝ) :=
discrimination q₁ q ≤ ε
→ discrimination q q₂ ≥ δ

variables (qₙ₁ qₙ₂ : (ℕ → ι) → ℝ)
[n_rnd_var qₙ₁] [n_rnd_var qₙ₂]

lemma n_err_exp_of_iid {n : ℕ} [iid qₙ₂ q₂] [iid qₙ₁ q₁] :
n_err_exp qₙ₁ qₙ₂ ε = n * err_exp q₁ q₂ (ε/n) :=
begin
  -- calc n_err_exp qₙ₁ qₙ₂ ε = min { discrimination qₙ qₙ₂ | discrimination qₙ₁ qₙ ≤ ε } : by sorry
  --           ... = min { n * discrimination q q₂ | n * discrimination q₁ q ≤ ε } : by rw discrimination_additive_of_iid
  --           ... = min { n * discrimination q q₂ | discrimination q₁ q ≤ ε/n } : by sorry
  --           ... = n *  min { discrimination q q₂ | discrimination q₁ q ≤ ε/n } : by sorry
  --           ... = n * err_exp q₁ q₂ (ε/n) : by sorry,
  sorry,
end

/-- if output symbol is one of these, then guess q₁ -/
def U (q₁ q₂ : ι → ℝ) (T : ℝ) :=
{ k : ι | (q₁ k) ≥ (q₂ k) * exp T }

/--  Prob. of error: guess q₁ when actually q₂ -/
def α (q₁ q₂ : ι → ℝ) (T : ℝ) : ℝ :=
∑ᶠ k ∈ (U q₁ q₂ T), (q₂ k)

/-- Prob. of error: guess q₂ when actually q₁ -/
def β (q₁ q₂ : ι → ℝ) (T : ℝ) : ℝ :=
∑ᶠ k ∉ (U q₁ q₂ T), (q₁ k)