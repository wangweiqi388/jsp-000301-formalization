/-
JSP-000301 / Erdős problem #365 — 形式化证否（Lean 4 + Mathlib，纯 Lean，无穷族）
==============================================================================

原命题（是非题）：
  "If two consecutive positive integers are powerful, must at least one be a perfect square?"

答案：否（Golomb 1970 证否）。本文件给出其否定命题的 Lean 形式化（即"存在至少一个反例"）：

  ∃ m : ℕ, IsPowerful m ∧ IsPowerful (m + 1) ∧ ¬IsSquare m ∧ ¬IsSquare (m + 1)

更强的结论：我们构造了一族无穷多个反例 (m_n, m_n+1)，其中
  m_n   = 23³ · X_n² = 12167 · X_n²
  m_n+1 = 2³  · Y_n² = 8     · Y_n²
且 (X_n, Y_n) 由基本 Pell 单位生成，满足 Pell 不变量 8·Y_n² − 12167·X_n² = 1。
每个 n 都给出连续、双侧 powerful、双侧非平方的一对，因此都是有效反例。

诚实边界（必须在申领中披露）：
  · 这一族只覆盖 (23,2) 单立方 Pell 族的一条无穷轨道；
  · 不包含 (7,2)、(79,23)、(3,7) 等其他已知单立方族；
  · 不包含双立方结构（如 A227297 的 a(6)、a(7)）；
  · 更不声称穷尽所有连续 powerful 非平方对。
  因此本形式化只证明"存在反例"（即完整证否），不声称给出全部反例。

设计要点（稳健性 / 一次编译友好）：
  · 全部计算由 Lean 内核完成（norm_num / ring / linarith / omega / positivity / linear_combination），
    无外部断言、无 Python、无 #eval 外部程序。
  · powerful 用素因子指数 ≥ 2 判定；非平方用一个素因子指数为奇数判定。
  · 无任何 sorry / admit（奖项硬性要求零 sorry）。

⚠ 编译提示：本文件依赖 Mathlib（import Mathlib）。在配好 Mathlib 的 Lean 4 项目里用
  `lake build` 编译即可，无需任何手动调整。
-/

import Mathlib

namespace JSP000301

/- ----------------------------- 基本定义 ----------------------------- -/

/-- n 是 powerful：每个整除 n 的素数 p 都满足 p² | n（即 n.factorization p ≥ 2） -/
def IsPowerful (n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ n → 2 ≤ n.factorization p

/-- n 是完全平方数：存在自然数 k 使 n = k² -/
def IsSquare (n : ℕ) : Prop := ∃ k : ℕ, n = k ^ 2

/- --------------------- 第 2 层：Pell 序列（用对避免互相递归） --------------------- -/

/-- (X_n, Y_n) 由基本 Pell 单位生成：(X_0,Y_0)=(1,39)，递推由 ε=1184384449+3796260√97336 给出 -/
def XY : ℕ → ℕ × ℕ
  | 0 => (1, 39)
  | n + 1 =>
    let x := (XY n).1
    let y := (XY n).2
    (1184384449 * x + 30370080 * y,
     46189095420 * x + 1184384449 * y)

def X (n : ℕ) : ℕ := (XY n).1
def Y (n : ℕ) : ℕ := (XY n).2

lemma X_succ (n : ℕ) :
    X (n + 1) = 1184384449 * X n + 30370080 * Y n := by
  simp [X, Y, XY]

lemma Y_succ (n : ℕ) :
    Y (n + 1) = 46189095420 * X n + 1184384449 * Y n := by
  simp [X, Y, XY]

/-- 序列恒为正 -/
lemma XY_pos (n : ℕ) : 0 < X n ∧ 0 < Y n := by
  induction n with
  | zero => simp [X, Y, XY]
  | succ n ih =>
    obtain ⟨hx, hy⟩ := ih
    constructor
    · rw [X_succ]; positivity
    · rw [Y_succ]; positivity

/- --------------------- 第 3 层：Pell 不变量 --------------------- -/

/-- 关键代数恒等式：变换保持二次型 8y² − 12167x²（由 Pell 单位 ε 决定） -/
lemma transform_preserves (x y : ℤ) :
    8 * (12167 * 3796260 * x + 1184384449 * y) ^ 2
    - 12167 * (1184384449 * x + 8 * 3796260 * y) ^ 2
    = 8 * y ^ 2 - 12167 * x ^ 2 := by
  have h1 : (1184384449 : ℤ) ^ 2 - 97336 * 3796260 ^ 2 = 1 := by norm_num
  linear_combination (8 * y ^ 2 - 12167 * x ^ 2) * h1

lemma pell_inv (n : ℕ) :
    8 * (Y n : ℤ) ^ 2 - 12167 * (X n : ℤ) ^ 2 = 1 := by
  induction n with
  | zero => simp [X, Y, XY]
  | succ n ih =>
    have hX : (X (n + 1) : ℤ) = 1184384449 * X n + 8 * 3796260 * Y n := by
      rw [X_succ]; push_cast; ring
    have hY : (Y (n + 1) : ℤ) = 12167 * 3796260 * X n + 1184384449 * Y n := by
      rw [Y_succ]; push_cast; ring
    rw [hX, hY, transform_preserves]
    exact ih

/- --------------------- 反例主定义 --------------------- -/

def m (n : ℕ) : ℕ := 12167 * X n ^ 2

lemma m_eq (n : ℕ) : m n = 23 ^ 3 * X n ^ 2 := by
  unfold m; norm_num

lemma m_succ_eq (n : ℕ) : m n + 1 = 2 ^ 3 * Y n ^ 2 := by
  have h := pell_inv n
  have : (2 ^ 3 * Y n ^ 2 : ℤ) = 12167 * X n ^ 2 + 1 := by
    norm_num; linarith
  have : 2 ^ 3 * Y n ^ 2 = 12167 * X n ^ 2 + 1 := by exact_mod_cast this
  unfold m; omega

/- --------------------- 第 4 层：辅助引理 --------------------- -/

lemma odd_three_add_two_mul (v : ℕ) : Odd (3 + 2 * v) := by
  use v + 1; omega

lemma not_odd_two_mul (v : ℕ) : ¬ Odd (2 * v) := by
  intro ⟨j, hj⟩; omega

lemma not_square_of_odd_factorization {n p : ℕ} (_hp : p.Prime)
    (hodd : Odd (n.factorization p)) : ¬ IsSquare n := by
  intro ⟨k, hk⟩
  have : n.factorization p = 2 * k.factorization p := by
    rw [hk]
    rw [Nat.factorization_pow]
    simp
  rw [this] at hodd
  exact not_odd_two_mul _ hodd

/- --------------------- 指数计算 --------------------- -/

lemma m_factor_23 (n : ℕ) :
    (m n).factorization 23 = 3 + 2 * (X n).factorization 23 := by
  rw [m_eq]
  rw [Nat.factorization_mul (by norm_num)
        (pow_ne_zero 2 (Nat.pos_iff_ne_zero.mp (XY_pos n).1))]
  rw [Finsupp.add_apply]
  rw [Nat.factorization_pow_self (by norm_num : Nat.Prime 23), Nat.factorization_pow]
  simp

lemma m_succ_factor_2 (n : ℕ) :
    (m n + 1).factorization 2 = 3 + 2 * (Y n).factorization 2 := by
  rw [m_succ_eq]
  rw [Nat.factorization_mul (by norm_num)
        (pow_ne_zero 2 (Nat.pos_iff_ne_zero.mp (XY_pos n).2))]
  rw [Finsupp.add_apply]
  rw [Nat.factorization_pow_self (by norm_num : Nat.Prime 2), Nat.factorization_pow]
  simp

/- --------------------- 主定理：一族无穷反例 --------------------- -/

theorem counterexample_family (n : ℕ) :
    IsPowerful (m n) ∧ IsPowerful (m n + 1) ∧
    ¬ IsSquare (m n) ∧ ¬ IsSquare (m n + 1) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- m n = 23³ · X² 是 powerful
    intro p hp hdiv
    by_cases hp23 : p = 23
    · subst hp23
      rw [m_factor_23]
      omega
    · have hXdiv : p ∣ X n := by
        rcases hp.dvd_mul.mp (m_eq n ▸ hdiv) with h2 | h2
        · have : p = 23 :=
            (Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 23)).mp
              (hp.dvd_of_dvd_pow h2)
          exact absurd this hp23
        · exact hp.dvd_of_dvd_pow h2
      have : (m n).factorization p = 2 * (X n).factorization p := by
        rw [m_eq, Nat.factorization_mul (by norm_num)
              (pow_ne_zero 2 (Nat.pos_iff_ne_zero.mp (XY_pos n).1))]
        rw [Finsupp.add_apply]
        rw [Nat.factorization_eq_zero_of_not_dvd
              (fun h ↦ hp23
                ((Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 23)).mp
                  (hp.dvd_of_dvd_pow h)))]
        rw [Nat.factorization_pow]
        simp
      rw [this]
      have hpos : 0 < (X n).factorization p :=
        hp.factorization_pos_of_dvd (Nat.pos_iff_ne_zero.mp (XY_pos n).1) hXdiv
      have : 1 ≤ (X n).factorization p := Nat.succ_le_of_lt hpos
      omega
  · -- m n + 1 = 2³ · Y² 是 powerful
    intro p hp hdiv
    by_cases hp2 : p = 2
    · subst hp2
      rw [m_succ_factor_2]
      omega
    · have hYdiv : p ∣ Y n := by
        rcases hp.dvd_mul.mp (m_succ_eq n ▸ hdiv) with h2 | h2
        · have : p = 2 :=
            (Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 2)).mp
              (hp.dvd_of_dvd_pow h2)
          exact absurd this hp2
        · exact hp.dvd_of_dvd_pow h2
      have : (m n + 1).factorization p = 2 * (Y n).factorization p := by
        rw [m_succ_eq, Nat.factorization_mul (by norm_num)
              (pow_ne_zero 2 (Nat.pos_iff_ne_zero.mp (XY_pos n).2))]
        rw [Finsupp.add_apply]
        rw [Nat.factorization_eq_zero_of_not_dvd
              (fun h ↦ hp2
                ((Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 2)).mp
                  (hp.dvd_of_dvd_pow h)))]
        rw [Nat.factorization_pow]
        simp
      rw [this]
      have hpos : 0 < (Y n).factorization p :=
        hp.factorization_pos_of_dvd (Nat.pos_iff_ne_zero.mp (XY_pos n).2) hYdiv
      have : 1 ≤ (Y n).factorization p := Nat.succ_le_of_lt hpos
      omega
  · -- m n 非平方：23 的指数是奇数
    apply not_square_of_odd_factorization (p := 23) (by norm_num)
    rw [m_factor_23]
    exact odd_three_add_two_mul _
  · -- m n + 1 非平方：2 的指数是奇数
    apply not_square_of_odd_factorization (p := 2) (by norm_num)
    rw [m_succ_factor_2]
    exact odd_three_add_two_mul _

/- --------------------- 证否（存在性）：这是奖项要的否定命题 --------------------- -/

/-- Erdős #365 / JSP-000301 的否定命题：存在连续 powerful 且双侧非平方的一对。
    取 n = 0，则 m_0 = 12167 = 23³，经典反例。整段代码仍为纯 Lean。 -/
theorem erdos_365_witness :
    ∃ m : ℕ, IsPowerful m ∧ IsPowerful (m + 1) ∧
      ¬ IsSquare m ∧ ¬ IsSquare (m + 1) :=
  ⟨m 0, counterexample_family 0⟩

end JSP000301
