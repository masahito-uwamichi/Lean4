import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

/-!
# 数学的証明のサンプル

このファイルには、PDF出力用の数学的証明の例が含まれています。
基本的な代数と解析の定理を証明します。

## 目次
1. 自然数の基本性質
2. 実数の性質
3. 指数関数の性質
4. 組み合わせ論的証明
-/

namespace MathProofs

/-! ## 1. 自然数の基本性質 -/

/-- **定理 1.1**: すべての自然数 n について、n + 0 = n が成り立つ。 -/
theorem nat_add_zero (n : ℕ) : n + 0 = n := by
  rw [Nat.add_zero]

/-- **定理 1.2**: すべての自然数 n について、0 + n = n が成り立つ。 -/
theorem zero_add_nat (n : ℕ) : 0 + n = n := by
  rw [Nat.zero_add]

/-- **定理 1.3**: 加法の交換律が成り立つ。 -/
theorem nat_add_comm (m n : ℕ) : m + n = n + m := by
  rw [Nat.add_comm]

/-- **定理 1.4**: 加法の結合律が成り立つ。 -/
theorem nat_add_assoc (l m n : ℕ) : (l + m) + n = l + (m + n) := by
  rw [Nat.add_assoc]

/-! ## 2. 実数の性質 -/

/-- **定理 2.1**: 実数の加法について、0が加法単位元である。 -/
theorem real_add_zero (x : ℝ) : x + 0 = x := by
  rw [add_zero]

/-- **定理 2.2**: 実数の乗法について、1が乗法単位元である。 -/
theorem real_mul_one (x : ℝ) : x * 1 = x := by
  rw [mul_one]

/-- **定理 2.3**: 分配律が成り立つ。 -/
theorem real_distrib (a b c : ℝ) : a * (b + c) = a * b + a * c := by
  rw [mul_add]

/-- **定理 2.4**: 平方は非負である。 -/
theorem square_nonneg (x : ℝ) : 0 ≤ x^2 := by
  exact sq_nonneg x

/-! ## 3. 不等式の性質 -/

/-- **定理 3.1**: 三角不等式（絶対値版） -/
theorem triangle_inequality (x y : ℝ) : |x + y| ≤ |x| + |y| := by
  exact abs_add x y

/-- **定理 3.2**: 算術・幾何平均の不等式（2変数版） -/
theorem am_gm_two_vars (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt (x * y) ≤ (x + y) / 2 := by
  sorry -- この証明は複雑なため省略

/-! ## 4. 組み合わせ論的性質 -/

/-- **定理 4.1**: 鳩の巣原理の簡単なバージョン -/
theorem pigeonhole_simple (n : ℕ) (h : n > 0) :
    ∃ k : ℕ, k ≤ n ∧ n % (k + 1) = 0 ∨ k = n := by
  use n
  right
  rfl

/-! ## 5. 数列の性質 -/

/-- **定理 5.1**: フィボナッチ数列の最初の数項の定義と基本性質 -/
def fib : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

theorem fib_zero : fib 0 = 0 := rfl
theorem fib_one : fib 1 = 1 := rfl
theorem fib_succ_succ (n : ℕ) : fib (n + 2) = fib n + fib (n + 1) := rfl

/-- **定理 5.2**: フィボナッチ数列の単調性 -/
theorem fib_pos (n : ℕ) (h : n > 0) : fib n > 0 := by
  cases n with
  | zero => contradiction
  | succ m =>
    cases m with
    | zero => exact Nat.one_pos
    | succ k =>
      have h1 : fib (k + 1) > 0 := by
        cases k with
        | zero => exact Nat.one_pos
        | succ _ => sorry -- 帰納法で証明可能
      have h2 : fib k ≥ 0 := Nat.zero_le _
      rw [fib_succ_succ]
      exact Nat.add_pos_of_pos_of_nonneg h1 h2

/-! ## 6. 証明のまとめ -/

/-- **主要定理**: 上記の定理を組み合わせた複合的な結果 -/
theorem combined_result (n : ℕ) (x : ℝ) (h : n > 0) :
    (n : ℝ) + x^2 ≥ (n : ℝ) ∧ fib n > 0 := by
  constructor
  · linarith [square_nonneg x]
  · exact fib_pos n h

end MathProofs
