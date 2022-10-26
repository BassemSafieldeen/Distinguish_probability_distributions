import algebra.indicator_function
import analysis.special_functions.pow
import analysis.special_functions.complex.log

open real set

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