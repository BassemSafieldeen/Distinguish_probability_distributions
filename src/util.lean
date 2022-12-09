import algebra.indicator_function
import analysis.special_functions.pow
import analysis.special_functions.complex.log

import rnd_var_one_symbol

open real set finset

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
    intro H, rw ← exp_add (d-c) (c-d) at H,
    norm_num at H, exact H,
  },
  apply h4, apply h3,
  exact le_div_of_pos H G,
end

lemma a_le_c {b : ℝ → ℝ} {a c : ℝ} :
  (∀ s, a ≤ b s) → (∃ s, c = b s) → (a ≤ c) :=
by finish

lemma mul_add_ge_of_ge {a b c d : ℝ} :
  b > 0 → a ≥ d → a * b + c ≥ d * b + c :=
begin
  intros G H,
  norm_num at *,
  rw mul_le_mul_right, exact H, exact G,
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
lemma sum_le_of_subset {A B : set ι} {f : ι → ℝ} (f_pos : ∀ k, 0 < f k) :
  A ⊆ B → ∑ k, f k * (Φ A k) ≤ ∑ k, f k * (Φ B k) :=
begin
  intro H,
  have h_indicator : ∀ k, Φ A k ≤ Φ B k, {
    apply indicator_le_indicator_of_subset H, simp,
  },
  apply sum_le_sum,
  intros k hk,
  exact (mul_le_mul_left (f_pos k)).mpr (h_indicator k),
end

lemma add_ge_sum_union {A B : set ι} {f : ι → ℝ} (f_pos : ∀ k, 0 < f k) :
  ∑ k, f k * (Φ (A∪B) k) ≤ ∑ k, f k * (Φ A k) + ∑ k, f k * (Φ B k) :=
begin
  rw ← sum_add_distrib,
  apply sum_le_sum,
  intros k hk,
  rw [← mul_add, mul_le_mul_left],
  swap,
  exact (f_pos k),
  rw Φ, rw Φ, rw Φ,
  apply indicator_le',
  intros a ha,
  simp,
  have : a ∈ A ∨ a ∈ B, by {apply ha,},
  by_cases a ∈ A,
  rw indicator, simp only [h], simp,
  by_cases a ∈ B,
  rw indicator, simp only [h], simp,
  rw indicator, simp only [h], simp,
  rw indicator, simp only [h], simp,
  have : a ∈ B, by finish,
  rw indicator, simp only [this], simp,
  intros,
  simp at H, rw or_iff_not_and_not at H, rw not_not at H,
  rw indicator, simp only [H.1], simp,
  rw indicator, simp only [H.2], simp,
end

lemma in_self_or_in_compl {ι : Type} [fintype ι] [decidable_eq ι] {q : ι → ℝ} [rnd_var_1 q] {S : set ι} :
  ∑ k, q k * Φ S k = 1 - ∑ k, q k * Φ Sᶜ k :=
begin
  rw [eq_sub_iff_add_eq, ← sum_add_distrib],
  have hq : ∑ k, q k = 1, by exact rnd_var_1.sum_probs_one,
  rw [← hq, sum_eq_sum_iff_of_le],
  intros k hk,
  rw [← mul_add, add_comm, Φ, Φ],
  rw indicator_compl_add_self_apply S 1 k, simp,
  intros k hk,
  rw [← mul_add, add_comm, Φ, Φ],
  rw indicator_compl_add_self_apply S 1 k, simp,
end

lemma gt_compl_le {ι : Type} {f g : ι → ℝ} :
  {k | f k > g k}ᶜ = {k | f k ≤ g k} :=
by {rw compl_def, simp}

lemma subset_abs {ι : Type} {f : ι → ℝ} {a : ℝ} :
  { k:ι | f k ≥ a } ⊆ { k:ι | abs(f k) ≥ a } :=
by {norm_num, intros x hx, rw le_abs, left, exact hx}

variables [decidable_eq ι] 

/-- expected value of a function of a random variable -/
def μ (q : ι → ℝ) [rnd_var_1 q] (f : ι → ℝ) :=
∑ k, q k * f k

/-- variance of a function of a random variable -/
def Var (q : ι → ℝ) [rnd_var_1 q] (f : ι → ℝ) :=
(∑ k, q k * (f k)^2) - (∑ k, q k * f k)^2

lemma helper1 {q f : ι → ℝ} {a : ℝ} :
  ∑ k, (q k) * 2 * (f k) * a = 2 * a * ∑ k, (q k) * (f k) :=
begin
  rw mul_sum,
  apply sum_congr, refl,
  intros k hk,
  rw ← mul_assoc,
  rw mul_comm (q k),
  rw mul_assoc 2 (q k),
  rw mul_assoc 2 (q k * f k) (a),
  rw mul_comm (q k * f k),
  rw ← mul_assoc,
  rw ← mul_assoc,
end

lemma Var_rw {q : ι → ℝ} [rnd_var_1 q] {f : ι → ℝ} :
  ∑ k, (q k) * (f k - μ q f)^2 = Var q f :=
begin
  calc ∑ k, (q k) * (f k - μ q f)^2 = ∑ k, (q k) * ((f k)^2 - 2 * (f k) * (μ q f) + (μ q f)^2) : by {apply sum_congr, refl, intros k hk, linarith}
            ... = ∑ k, ((q k) * (f k)^2 - (q k) * 2 * (f k) * (μ q f) + (q k) * (μ q f)^2) : by {apply sum_congr, refl, intros k hk, rw mul_add, rw mul_sub, linarith}
            ... = ∑ k, (q k) * (f k)^2 - ∑ k, (q k) * 2 * (f k) * (μ q f) + ∑ k, (q k) * (μ q f)^2 : by {rw sum_add_distrib, rw sum_sub_distrib}
            ... = ∑ k, (q k) * (f k)^2 - ∑ k, (q k) * 2 * (f k) * (μ q f) + ∑ k, (μ q f)^2 * (q k) : by simp only [mul_comm]
            ... = ∑ k, (q k) * (f k)^2 - ∑ k, (q k) * 2 * (f k) * (μ q f) + (μ q f)^2 * ∑ k, q k : by simp only [mul_sum]
            ... = ∑ k, (q k) * (f k)^2 - ∑ k, (q k) * 2 * (f k) * (μ q f) + (μ q f)^2 * 1 : by simp only [rnd_var_1.sum_probs_one]
            ... = ∑ k, (q k) * (f k)^2 - ∑ k, (q k) * 2 * (f k) * (μ q f) + (μ q f)^2 : by simp
            ... = ∑ k, (q k) * (f k)^2 - 2 * (μ q f) * ∑ k, (q k) * (f k) + (μ q f)^2 : by simp only [helper1]
            ... = ∑ k, (q k) * (f k)^2 - 2 * (μ q f) * (μ q f) + (μ q f)^2 : by rw μ
            ... = ∑ k, (q k) * (f k)^2 - 2 * (μ q f)^2 + (μ q f)^2 : by ring
            ... = ∑ k, (q k) * (f k)^2 - (μ q f)^2 : by linarith
            ... = ∑ k, (q k) * (f k)^2 - (∑ k, q k * f k)^2 : by rw μ
            ... = Var q f : by rw Var,
end

lemma helper2 {ι : Type} {k : ι} {S : set ι} :
  (Φ S k) + (Φ Sᶜ k) = 1 :=
begin
  rw [Φ, Φ, indicator, indicator],
  simp, by_cases p : k ∈ S,
  simp only [p], simp, intro H, contradiction,
  simp only [p], simp, intro H, contradiction,
end

lemma helper3 {ι : Type} [fintype ι] [decidable_eq ι] {a : ℝ} {f : ι → ℝ} :
  (∀ k, |f k| ≥ a) → (∑ k, |f k| ≥ ∑ k : ι, a) :=
λ H, fintype.sum_mono H

lemma helper4 {ι : Type} {k : ι} {f : ι → ℝ} {ε : ℝ} :
  {k | f k ≥ ε}ᶜ = {k | f k < ε} :=
by {ext, split; simp}

lemma helper5 {a b : ℝ} :
  a ≥ 0 → b ≥ 0 → a + b ≥ a :=
by {intros Ha Hb, linarith}

lemma helper6 {X : ι → ℝ} [rnd_var_1 X] {f g : ι → ℝ} {ε : ℝ} : 
∑ k, (X k) * (g k)^2 * (Φ {x | |g x| ≥ ε} k)
                   + ∑ k, (X k) * (g k)^2 * (Φ {x | |g x| < ε} k)
            ≥ (∑ k, (X k) * (g k)^2 * (Φ {x | |g x| ≥ ε} k)) :=
begin
  apply helper5,
  apply sum_nonneg',
  intro i,
  apply mul_nonneg,
  apply mul_nonneg,
  apply le_of_lt,
  exact rnd_var_1.probs_pos i,
  apply sq_nonneg,
  rw Φ, rw indicator,
  by_cases p : i ∈ {x : ι | |g x| ≥ ε},
  simp only [p], simp,
  simp only [p], simp,
  apply sum_nonneg',
  intro i,
  apply mul_nonneg,
  apply mul_nonneg,
  apply le_of_lt,
  exact rnd_var_1.probs_pos i,
  apply sq_nonneg,
  rw Φ, rw indicator,
  by_cases p : i ∈ {x : ι | |g x| < ε},
  simp only [p], simp,
  simp only [p], simp,
end

lemma helper7 {X : ι → ℝ} [rnd_var_1 X] {f g : ι → ℝ} {ε > (0:ℝ)} : 
  ∑ k, (X k) * (f k - μ X f)^2 * (Φ {x | |f x - μ X f| ≥ ε} k)
            ≥ ∑ k, (X k) * ε^2 * (Φ {x | |f x - μ X f| ≥ ε} k) :=
begin
  -- intro hε,
  apply sum_le_sum,
  intros i hi,
  rw Φ, rw indicator,
  by_cases p : i ∈ {x : ι | |f x - μ X f| ≥ ε},
  simp only [p], simp,
  have : |f i - μ X f| ≥ ε, { finish },
  have : ε^2 ≤ (f i - μ X f)^2, {
    rw [sq_le_sq, abs_of_pos],
    exact this, assumption,
  },
  have : (f i - μ X f)^2 ≥ ε^2, { exact this },
  apply mul_le_mul_of_nonneg_left,
  exact this,
  apply le_of_lt,
  exact rnd_var_1.probs_pos i,
  simp only [p], simp,
end

lemma Chebyshevs_ineq' (X : ι → ℝ) [rnd_var_1 X] (f : ι → ℝ) {ε > (0:ℝ)} :
  Var X f ≥ ε^2 * (∑ k, (X k) * (Φ {x | |f x - μ X f| ≥ ε} k)) :=
begin
  have : 0 < ε, { assumption, },
  calc Var X f  = ∑ k, (X k) * (f k - μ X f)^2 : by rw Var_rw
      ... = ∑ k, (X k) * (f k - μ X f)^2 * 1 : by simp
      ... = ∑ k, (X k) * (f k - μ X f)^2 * ((Φ {x | |f x - μ X f| ≥ ε} k) + (Φ {x | |f x - μ X f| ≥ ε}ᶜ k)) : by simp only [helper2]
      ... = ∑ k, (X k) * (f k - μ X f)^2 * ((Φ {x | |f x - μ X f| ≥ ε} k) + (Φ {x | |f x - μ X f| < ε} k)) : by {apply sum_congr, refl, intros x hx, rwa helper4}
      ... = ∑ k, ( (X k) * (f k - μ X f)^2 * (Φ {x | |f x - μ X f| ≥ ε} k)
              + (X k) * (f k - μ X f)^2 * (Φ {x | |f x - μ X f| < ε} k) ) : by simp only [mul_add]
      ... = ∑ k, (X k) * (f k - μ X f)^2 * (Φ {x | |f x - μ X f| ≥ ε} k)
              + ∑ k, (X k) * (f k - μ X f)^2 * (Φ {x | |f x - μ X f| < ε} k) : by exact sum_add_distrib
      ... ≥ ∑ k, (X k) * (f k - μ X f)^2 * (Φ {x | |f x - μ X f| ≥ ε} k) : by {apply helper6, exact f}
      ... ≥ ∑ k, (X k) * ε^2 * (Φ {x | |f x - μ X f| ≥ ε} k) : by {apply helper7, exact f, exact this,}
      ... = ∑ k, ε^2 * ((X k) * (Φ {x | |f x - μ X f| ≥ ε} k)) : by {apply sum_congr, refl, intros k hk, rw [mul_comm (X k) (ε^2), mul_assoc]}
      ... = ε^2 * ∑ k, (X k) * (Φ {x | |f x - μ X f| ≥ ε} k) : by simp only [mul_sum],
end

theorem Chebyshevs_ineq {X : ι → ℝ} [rnd_var_1 X] {f : ι → ℝ} {ε > (0:ℝ)} :
  ∑ k, X k * (Φ {k | |f k - μ X f| ≥ ε} k) ≤ Var X f/ε^2 :=
begin
  have ε_pos : ε > 0, { assumption },
  have ε_sq_pos : ε^2 > 0, { exact pow_pos ε_pos 2 },
  have : Var X f / ε^2 ≥ (∑ k, (X k) * (Φ {k | |f k - μ X f| ≥ ε} k)), {
    apply (le_div_iff' ε_sq_pos).mpr,
    apply (Chebyshevs_ineq' X f),
    assumption,
  },
  exact this,
end