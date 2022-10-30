import algebra.indicator_function
import analysis.special_functions.pow
import analysis.special_functions.complex.log

import rnd_var_one_symbol

open real set

open_locale big_operators

lemma le_div_of_pos {a b c d : ℝ} :
  b * exp(d - c) ≤ a → 0 < b → exp(d - c) ≤ a / b :=
λ H G, by {rw mul_comm at H, exact (le_div_iff G).mpr H}

lemma exp_tmp_lemma {a b c d : ℝ} :
  a ≥ b * exp(d - c) → 0 < b → 1 ≤ a / b * exp(c - d) :=
begin
  intros H G,
  have h3 : a/b ≥ exp(d - c) → a/b * exp(c - d) ≥ exp(d - c) * exp(c - d), {
    intro H, apply mul_le_mul_of_nonneg_right, exact H, apply le_of_lt, exact exp_pos (c - d),
  },
  have h4 : a/b * exp(c - d) ≥ exp(d - c) * exp(c - d) → a/b * exp(c - d) ≥ 1, {
    intro H,
    rw ← exp_add (d-c) (c-d) at H,
    norm_num at H,
    exact H,
  },
  apply h4,
  apply h3,
  exact le_div_of_pos H G,
end

lemma a_le_c {b : ℝ → ℝ} {a c : ℝ} :
  (∀ s, a ≤ b s) → (∃ s, c = b s) → (a ≤ c) :=
by finish

lemma mul_add_ge_of_ge {a b c d : ℝ} :
  a ≥ d → a * b + c ≥ d * b + c :=
begin
  intro H,
  norm_num at *,
  rw mul_le_mul_right, exact H,
  sorry
end

lemma zero_le_div_exp_pow {a b c d : ℝ} :
  0 ≤ a → 0 ≤ b → 0 ≤ (a / b * exp(c))^d :=
begin
  intros ha hb,
  apply rpow_nonneg_of_nonneg,
  apply mul_nonneg, apply div_nonneg,
  exact ha, exact hb,
  apply le_of_lt, apply exp_pos,
end

noncomputable theory

/-- indicator function: if k ∈ S then 1 else 0 -/
def Φ {ι : Type} (S : set ι) (k : ι) : ℝ :=
indicator S 1 k

lemma indicator_zero_of_not_one {ι : Type} {S : set ι} {k} :
  ¬ (Φ S k = 1) → (Φ S k = 0) :=
λ H, by {rw [Φ, indicator] at *, by_contradiction H1, finish}

variables {ι : Type} [fintype ι]

/-- if A ⊆ B then ∑ k ∈ A, f k < ∑ k ∈ B, f k-/
lemma sum_le_of_subset {A B : set ι} {f : ι → ℝ} :
  A ⊆ B → ∑ k, f k * (Φ A k) ≤ ∑ k, f k * (Φ B k) :=
sorry

lemma add_ge_sum_union {A B : set ι} {f : ι → ℝ} :
  ∑ k, f k * (Φ A k) + ∑ k, f k * (Φ B k) ≥ ∑ k, f k * (Φ (A∪B) k) :=
sorry

lemma in_self_or_in_compl {ι : Type} [fintype ι] [decidable_eq ι] {q : ι → ℝ} [rnd_var_1 q] {S : set ι} :
  ∑ k, q k * Φ S k = 1 - ∑ k, q k * Φ Sᶜ k :=
sorry

lemma gt_compl_le {ι : Type} {f g : ι → ℝ} :
  {k | f k > g k}ᶜ = {k | f k ≤ g k} :=
by {rw compl_def, simp}

lemma subset_abs {ι : Type} {f : ι → ℝ} {a : ℝ} :
  { k:ι | f k ≥ a } ⊆ { k:ι | abs(f k) ≥ a } :=
sorry

/--
the smallest a equal to b. Multiplied by n.
is the smallest number equal to n * b.
-/
lemma mul_inf_eq_inf_mul {a b n : ℝ} : 
  n * Inf { a | a = b } = Inf { a | a = n * b } :=
sorry

lemma mul_inf_eq_inf_mul_ex {ι : Type} [fintype ι] {a b n : ℝ} {f : ι → ℝ} : 
  n * Inf { a | a = b } = Inf { a | a = n * b } :=
sorry

variables [decidable_eq ι] 

/-- expectation value of a function of a random variable -/
def μ (q : ι → ℝ) [rnd_var_1 q] (f : ι → ℝ) :=
∑ k, q k * f k

/-- variance of a function of a random variable -/
def Var (q : ι → ℝ) [rnd_var_1 q] (f : ι → ℝ) :=
(∑ k, q k * (f k)^2) - (∑ k, q k * f k)^2

/-- Pr(|f X - 𝔼[f X]| ≥ ε) ≤ Var(f X)/ε² -/
theorem Chebyshevs_ineq {X : ι → ℝ} [rnd_var_1 X] {f : ι → ℝ} {ε : ℝ} :
  ∑ k, X k * (Φ {k | abs(f k - μ X f) ≥ ε} k) ≤ Var X f/ε^2 :=
begin
  -- Pr(|f X - 𝔼[f X]| ≥ ε)
  -- = Pr(k ∈ {k | |f k - μ X f| ≥ ε})
  -- = ∑ k, X k * (Φ {k | |f k - μ X f| ≥ ε} k)
  sorry,
end