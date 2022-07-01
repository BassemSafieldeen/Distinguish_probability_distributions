import algebra.big_operators
import analysis.special_functions.pow
import analysis.special_functions.complex.log

open real finset

open_locale big_operators

noncomputable theory

variables {ι : Type} [fintype ι]
[fintype (ℕ → ι)] [decidable_eq ι]

/-- prob of a sequence of n symbols -/
class rnd_var (qₙ : (ℕ → ι) → ℝ) :=
(probs_nonneg  : ∀ sₙ, qₙ sₙ ≥ 0)
(sum_probs_one : ∑ sₙ, qₙ sₙ = 1)

/-- prob of symbol -/
class rnd_var_1 (q : ι → ℝ) :=
(probs_nonneg  : ∀ k, q k ≥ 0)
(sum_probs_one : ∑ k, q k = 1)

/- if we lift from ι → ℝ to (ℕ → ι) → ℝ then no need for redundant classes  -/

/-- independently and indentically distributed  -/
def iid (n : ℕ) (qₙ : (ℕ → ι) → ℝ) [rnd_var qₙ] (q : ι → ℝ) [rnd_var_1 q] :=
∀ kₙ, qₙ kₙ = ∏ i in range n, q (kₙ i)

variables {n : ℕ} {kₙ : ℕ → ι}
(qₙ : (ℕ → ι) → ℝ) [rnd_var qₙ]
{q : ι → ℝ} [rnd_var_1 q]

lemma log_iid [iid n qₙ q] :
log(qₙ kₙ) = ∑ i in range n, log(q (kₙ i)) := sorry

/-- relative entropy -/
def discrimination (qₙ₁ qₙ₂ : (ℕ → ι) → ℝ) : ℝ :=
∑ kₙ, (qₙ₁ kₙ) * (log(qₙ₁ kₙ) - log(qₙ₂ kₙ))

def discrimination_1 (q₁ q₂ : ι → ℝ) : ℝ :=
∑ k, (q₁ k) * (log(q₁ k) - log(q₂ k))

variables (qₙ₁ qₙ₂ : (ℕ → ι) → ℝ) [rnd_var qₙ₁] [rnd_var qₙ₂]
(q₁ q₂ : ι → ℝ) [rnd_var_1 q₁] [rnd_var_1 q₂]

lemma discrimination_additive_of_iid [iid n qₙ₁ q₁] [iid n qₙ₂ q₂] :
discrimination qₙ₁ qₙ₂ = n * discrimination_1 q₁ q₂ :=
begin
  -- calc discrimination q₁ₙ q₂ₙ = ∑ kₙ, (qₙ₁ kₙ) * (log(qₙ₁ kₙ) - log(qₙ₂ kₙ)) : by rw discrimination
  --                        ... = ∑ kₙ, (∏ i in range n, (q₁ (kₙ n))) * ∑ i in range n, (log(q₁ (kₙ n)) - log(q₂ (kₙ n))) : by rw log_iid_rw
  --                        ... = n * discrimination_1 q₁ q₂ : by sorry,
  sorry,
end

/-- How close to q₂ can we get if we stay ε-close to q₁? -/
def err_exp (qₙ₁ qₙ₂ : (ℕ → ι) → ℝ) [rnd_var qₙ₁] [rnd_var qₙ₂] (ε : ℝ) :=
Inf { b : ℝ | ∃ qₙ, discrimination qₙ₁ qₙ ≤ ε ∧ discrimination qₙ qₙ₂ = b }

def err_exp_1 (q₁ q₂ : ι → ℝ) (ε : ℝ) :=
Inf { b : ℝ | ∃ q, discrimination_1 q₁ q ≤ ε ∧ discrimination_1 q q₂ = b }

/-- can get δ-close to q₂ when ε-close to q₁ -/
def achieves_err_exp (qₙ qₙ₁ qₙ₂ : (ℕ → ι) → ℝ) [rnd_var qₙ] [rnd_var qₙ₁] [rnd_var qₙ₂] (ε δ : ℝ) :=
discrimination qₙ₁ qₙ ≤ ε
→ discrimination qₙ qₙ₂ ≥ δ

lemma err_exp_of_iid {ε} [iid n qₙ₁ q₁] [iid n qₙ₂ q₂] :
err_exp qₙ₁ qₙ₂ ε = n * err_exp_1 q₁ q₂ (ε/n) :=
begin
  -- calc err_exp qₙ₁ qₙ₂ ε = min { discrimination qₙ qₙ₂ | discrimination qₙ₁ qₙ ≤ ε } : by rw err_exp
  --           ... = min { n * discrimination_1 q q₂ | n * discrimination_1 q₁ q ≤ ε } : by rw discrimination_additive_of_iid
  --           ... = min { n * discrimination_1 q q₂ | discrimination_1 q₁ q ≤ ε/n } : by simp
  --           ... = n *  min { discrimination_1 q q₂ | discrimination_1 q₁ q ≤ ε/n } : by simp
  --           ... = n * err_exp_1 q₁ q₂ (ε/n) : by rw err_exp_1,
  sorry,
end