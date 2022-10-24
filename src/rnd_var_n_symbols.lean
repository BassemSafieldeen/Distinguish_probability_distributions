import algebra.big_operators
import analysis.special_functions.pow
import analysis.special_functions.complex.log

import rnd_var_one_symbol

open real finset

open_locale big_operators

noncomputable theory

variables {ι : Type} [fintype ι] [decidable_eq ι] [fintype (ℕ → ι)]

/-- prob of sequence of symbols -/
class rnd_var (qₙ : (ℕ → ι) → ℝ) :=
(probs_nonneg  : ∀ sₙ, qₙ sₙ ≥ 0)
(sum_probs_one : ∑ sₙ, qₙ sₙ = 1)

/- if we lift from ι to (ℕ → ι) then no need for redundant classes -/

/-- independently and identically distributed  -/
def iid (n : ℕ) (qₙ : (ℕ → ι) → ℝ) [rnd_var qₙ] (q : ι → ℝ) [rnd_var_1 q] :=
∀ kₙ, qₙ kₙ = ∏ i in range n, q (kₙ i)

variables {n : ℕ} {kₙ : ℕ → ι}
(qₙ : (ℕ → ι) → ℝ) [rnd_var qₙ]
{q : ι → ℝ} [rnd_var_1 q]

lemma log_iid [H : iid n qₙ q] [H2: ∀ i ∈ range n, q (kₙ i) ≠ 0] :
log(qₙ kₙ) = ∑ i in range n, log(q (kₙ i)) :=
begin
  calc log(qₙ kₙ) = log(∏ i in range n, q (kₙ i)) : by rw H
             ... = ∑ i in range n, log(q (kₙ i)) : log_prod _ _ H2,
end

/-- relative entropy -/
def discrimination (qₙ₁ qₙ₂ : (ℕ → ι) → ℝ) : ℝ :=
∑ kₙ, (qₙ₁ kₙ) * (log(qₙ₁ kₙ) - log(qₙ₂ kₙ))

variables
(qₙ₁ qₙ₂ : (ℕ → ι) → ℝ) [rnd_var qₙ₁] [rnd_var qₙ₂]
(q₁ q₂ : ι → ℝ) [rnd_var_1 q₁] [rnd_var_1 q₂]

lemma discrimination_additive_of_iid [iid n qₙ₁ q₁] [iid n qₙ₂ q₂]
[H2: ∀ kₙ : (ℕ → ι), ∀ i ∈ range n, q₁ (kₙ i) ≠ 0] [H3: ∀ kₙ : (ℕ → ι), ∀ i ∈ range n, q₂ (kₙ i) ≠ 0] :
discrimination qₙ₁ qₙ₂ = n * discrimination_1 q₁ q₂ :=
begin
  have log_diff : ∀ kₙ, log(qₙ₁ kₙ) - log(qₙ₂ kₙ) = (∑ i in range n, log(q₁ (kₙ i))) - (∑ i in range n, log(q₂ (kₙ i))), {
    intro kₙ, rw [log_iid qₙ₁, log_iid qₙ₂], exact _inst_9, exact _inst_11, exact H3 kₙ, exact _inst_8, exact _inst_10, exact H2 kₙ,
  },
  have hg : ∀ i, ∑ kₙ, (qₙ₁ kₙ) * (log(q₁ (kₙ i)) - log(q₂ (kₙ i))) = discrimination_1 q₁ q₂, {
    sorry,
  },
  calc discrimination qₙ₁ qₙ₂ = ∑ kₙ, (qₙ₁ kₙ) * (log(qₙ₁ kₙ) - log(qₙ₂ kₙ)) : by rw discrimination
                         ... = ∑ kₙ, (qₙ₁ kₙ) * ∑ i in range n, (log(q₁ (kₙ i)) - log(q₂ (kₙ i))) : by simp only [log_diff, sum_sub_distrib]
                         ... = ∑ kₙ, ∑ i in range n, (qₙ₁ kₙ) * (log(q₁ (kₙ i)) - log(q₂ (kₙ i))) : by simp only [mul_sum]
                         ... = ∑ i in range n, discrimination_1 q₁ q₂ : by simp only [sum_comm, hg]
                         ... = n * discrimination_1 q₁ q₂ : by {rw sum_const, simp},
end

/-- How close to q₂ can we get if we stay ε-close to q₁? -/
def err_exp (qₙ₁ qₙ₂ : (ℕ → ι) → ℝ) [rnd_var qₙ₁] [rnd_var qₙ₂] (ε : ℝ) :=
Inf { b : ℝ | ∃ qₙ, b = discrimination qₙ qₙ₂ ∧ discrimination qₙ₁ qₙ ≤ ε }

/-- can get δ-close to q₂ when ε-close to q₁ -/
def achieves_err_exp (qₙ qₙ₁ qₙ₂ : (ℕ → ι) → ℝ) [rnd_var qₙ] [rnd_var qₙ₁] [rnd_var qₙ₂] (ε δ : ℝ) :=
discrimination qₙ₁ qₙ ≤ ε
→ discrimination qₙ qₙ₂ ≥ δ

lemma err_exp_of_iid {ε} [iid n qₙ₁ q₁] [iid n qₙ₂ q₂] :
err_exp qₙ₁ qₙ₂ ε = n * err_exp_1 q₁ q₂ (ε/n) :=
begin
  calc err_exp qₙ₁ qₙ₂ ε = Inf { b : ℝ | ∃ qₙ, b = discrimination qₙ qₙ₂ ∧ discrimination qₙ₁ qₙ ≤ ε } : by rw err_exp
            ... = Inf { b : ℝ | ∃ q, b = n * discrimination_1 q q₂ ∧ (n:ℝ) * discrimination_1 q₁ q ≤ ε } : by sorry -- rw discrimination_additive_of_iid
            ... = n * Inf { b : ℝ | ∃ q, b = discrimination_1 q q₂ ∧ discrimination_1 q₁ q ≤ ε/n } : by sorry -- simp
            ... = n * err_exp_1 q₁ q₂ (ε/n) : by rw err_exp_1,
end