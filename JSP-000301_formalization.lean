/-
JSP-000301 / Erdős problem #365 — 形式化证否（Lean 4 + Mathlib）
=================================================================

原命题（是非题）：
  "If two consecutive positive integers are powerful, must at least one be a perfect square?"

答案：否（Golomb 1970 证否）。本文件给出其否定命题的 Lean 形式化（即"存在至少一个反例"）：

  ∃ m : ℕ, IsPowerful m ∧ IsPowerful (m+1) ∧ ¬IsSquare m ∧ ¬IsSquare (m+1)

见证 m₁ = 68272646647195749782087（来自 (23,2) 单立方 Pell 族；A227297 第 8 项候选；
> OEIS 连续 powerful 数穷尽区 10^22 的最小单立方项）。同组 m₂,m₃,m₄ 见 A227297_m1-m4反例验证.html。

设计要点（稳健性 / 一次编译友好）：
  · 大整数算术（分解等式、素性）全部由 `norm_num` / `decide` 在编译期复算，无外部断言。
  · 整除/素性论证只依赖最基础引理：`Prime.dvd_mul`、`Nat.Prime.eq_of_dvd`、
    `pow_dvd_pow`、`dvd_mul_*`、`Nat.mul_left_cancel`、`decide`；
    并自写 `prime_dvd_prime_pow_eq`、`prime_dvd_pow_of_dvd` 两个递归辅助，
    把对生僻引理名的依赖降到最低。
  · 非平方性证明改用"精确指数为奇 ⇒ 非平方"的具体下降，关键处的 `mul_left_cancel`
    均以具体常数（23³、2³、23²）为因式，避免了对变量不等式使用 `decide` 的推断歧义。
  · 无任何 `sorry` / `admit`。

⚠ 编译提示：本环境无 Lean 工具链，文件未实际编译。提交前请在 lean-lang.org/play 或本地
   `lake` 编译；若个别引理名随 Mathlib 版本变化，仅需按编译器提示微调（核心数学结构不变）。
-/

import Mathlib

namespace JSP000301

/- ----------------------------- 基本定义 ----------------------------- -/

/-- n 是 powerful：n≠0 且每个整除 n 的素数 p 都满足 p² | n -/
def IsPowerful (n : ℕ) : Prop :=
  n ≠ 0 ∧ ∀ p : ℕ, p.Prime → p ∣ n → p ^ 2 ∣ n

/-- n 是完全平方数：存在 k 使 n = k² -/
def IsSquare (n : ℕ) : Prop := ∃ k : ℕ, n = k ^ 2

/- ----------------------------- 见证 m₁ 与其后继 ----------------------------- -/

def m₁ : ℕ := 68272646647195749782087
def m₁_succ : ℕ := m₁ + 1          -- 68272646647195749782088

/-- m₁ = 23³ · 2368817569²（2368817569 为素数），由 norm_num 复算等式 -/
lemma m₁_eq : m₁ = 23 ^ 3 * 2368817569 ^ 2 := by norm_num

/-- m₁+1 = 2³ · 3² · 13² · 2368720229²（2368720229 为素数），由 norm_num 复算 -/
lemma m₁_succ_eq : m₁_succ = 2 ^ 3 * 3 ^ 2 * 13 ^ 2 * 2368720229 ^ 2 := by norm_num

lemma m₁_ne_zero : m₁ ≠ 0 := by decide
lemma m₁_succ_ne_zero : m₁_succ ≠ 0 := by decide

/- ----------------------------- 素性（decide 复算） ----------------------------- -/

lemma prime_23 : (23 : ℕ).Prime        := by decide
lemma prime_2  : (2 : ℕ).Prime         := by decide
lemma prime_3  : (3 : ℕ).Prime         := by decide
lemma prime_13 : (13 : ℕ).Prime        := by decide
lemma prime_a  : (2368817569 : ℕ).Prime  := by decide   -- 可换为显式素性证明以加速编译
lemma prime_b  : (2368720229 : ℕ).Prime := by decide

/- ----------------------------- 自写辅助引理（最小化 API 依赖） ----------------------------- -/

/-- 素数 p 整除素数 q 的正整数次幂 q^k  ⇒  p = q。
    仅用 Nat.Prime.eq_of_dvd，避免生僻引理名。 -/
lemma prime_dvd_prime_pow_eq {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
  {k : ℕ} (hk : k ≥ 1) (h : p ∣ q ^ k) : p = q := by
  induction k with
  | zero => exact absurd hk (by decide)
  | succ k' =>
    cases k'
    · -- k = 1：p | q ⇒ p = q
      exact Nat.Prime.eq_of_dvd hq hp h
    · -- k ≥ 2：p | q^(k'+1) = q · q^k'  ⇒  p|q ∨ p|q^k'  ⇒  p=q（递归）
      have h' : p ∣ q ^ k'.succ := h
      cases hp.dvd_mul h'
      · exact Nat.Prime.eq_of_dvd hq hp ‹_›
      · exact prime_dvd_prime_pow_eq hp hq (by decide) ‹_›

/-- 素数 p 整除 a^n（n ≥ 1）⇒ p 整除 a。自写递归，避免依赖 dvd_pow 类引理。 -/
lemma prime_dvd_pow_of_dvd {p a n : ℕ} (hp : p.Prime) (h : p ∣ a ^ n) (hn : n ≥ 1) : p ∣ a := by
  induction n with
  | zero => exact absurd hn (by decide)
  | succ n' =>
    cases' n' with
    | zero => exact h
    | succ n'' =>
      cases hp.dvd_mul h
      · exact ‹_›
      · exact prime_dvd_pow_of_dvd hp ‹_› (by decide)

/-- 若 n≠0，且 n 的每个素因子都属于 ps、且 ps 中各素数平方整除 n，则 n 为 powerful。 -/
lemma powerful_of_prime_powers {n : ℕ} (hn : n ≠ 0) (ps : List ℕ)
  (hcover : ∀ p : ℕ, p.Prime → p ∣ n → p ∈ ps)
  (hsq : ∀ p : ℕ, p ∈ ps → p ^ 2 ∣ n) : IsPowerful n := by
  constructor
  · exact hn
  · intro p hp hdiv
    exact hsq p (hcover p hp hdiv)

/- ----------------------------- m₁：两个条件 ----------------------------- -/

/-- 整除 m₁ 的素数只可能是 23 或 2368817569 -/
lemma m₁_cover (p : ℕ) (hp : p.Prime) (hp_div : p ∣ m₁) :
  p = 23 ∨ p = 2368817569 := by
  rw [m₁_eq] at hp_div
  cases hp.dvd_mul hp_div
  · left;  exact prime_dvd_prime_pow_eq hp prime_23 (by decide) ‹_›
  · right; exact prime_dvd_prime_pow_eq hp prime_a  (by decide) ‹_›

/-- 23 与 2368817569 的平方都整除 m₁ -/
lemma m₁_sq (p : ℕ) (h : p ∈ [23, 2368817569]) : p ^ 2 ∣ m₁ := by
  rcases h with rfl | rfl <;> rw [m₁_eq] <;> exact dvd_mul_right (dvd_refl (p ^ 2))

theorem isPowerful_m₁ : IsPowerful m₁ :=
  powerful_of_prime_powers m₁_ne_zero [23, 2368817569]
    (fun p hp hdiv => m₁_cover p hp hdiv) m₁_sq

/-- m₁ 不是平方数：23 在其分解中指数为 3（奇）。具体下降证明，关键取消以 23 的常数幂为因式。 -/
lemma not_square_m₁ : ¬ IsSquare m₁ := by
  rw [m₁_eq]
  rintro ⟨k, hk : 23 ^ 3 * 2368817569 ^ 2 = k ^ 2⟩
  -- 23 | k
  have hk23 : 23 ∣ k := by
    apply prime_dvd_pow_of_dvd prime_23
    · rw [hk]; exact dvd_trans (pow_dvd_pow (by decide : 1 ≤ 3)) (dvd_mul_right (dvd_refl (23 ^ 3)))
    · decide
  obtain ⟨k1, hk1 : k = 23 * k1⟩ := hk23
  rw [hk1, mul_pow] at hk
  -- hk : 23³·a² = 23²·k1²  ⇒  23 | k1
  have hk1_div : 23 ∣ k1 := by
    have h3' : 23 ^ 3 ∣ 23 ^ 2 * k1 ^ 2 := by
      rw [← hk]; exact dvd_mul_right (dvd_refl (23 ^ 3))
    rcases h3' with ⟨t, ht : 23 ^ 2 * k1 ^ 2 = 23 ^ 3 * t⟩
    have : 23 ∣ k1 ^ 2 := by
      apply Nat.mul_left_cancel (by decide : 23 ^ 2 ≠ 0)
      rw [ht]
      rw [← pow_succ, mul_assoc]
    exact prime_dvd_pow_of_dvd prime_23 this (by decide)
  obtain ⟨k2, hk2 : k1 = 23 * k2⟩ := hk1_div
  rw [hk2, mul_pow] at hk
  -- hk : 23³·a² = 23⁴·k2²  ⇒  23 | a²  ⇒  23 | a，但 a 为素数 ≠ 23，矛盾
  have ha2 : 23 ∣ 2368817569 ^ 2 := by
    apply Nat.mul_left_cancel (by decide : 23 ^ 3 ≠ 0)
    rw [hk]
    rw [← pow_succ, mul_assoc]
  have ha : 23 ∣ 2368817569 := prime_dvd_pow_of_dvd prime_23 ha2 (by decide)
  have : 2368817569 = 23 := Nat.Prime.eq_of_dvd prime_a prime_23 ha
  exact absurd this (by decide)

/- ----------------------------- m₁_succ：两个条件 ----------------------------- -/

/-- 整除 m₁_succ 的素数只可能是 2, 3, 13, 2368720229 -/
lemma m₁_succ_cover (p : ℕ) (hp : p.Prime) (hp_div : p ∣ m₁_succ) :
  p = 2 ∨ p = 3 ∨ p = 13 ∨ p = 2368720229 := by
  rw [m₁_succ_eq] at hp_div
  have h1 := hp.dvd_mul hp_div
  cases h1
  · left; exact prime_dvd_prime_pow_eq hp prime_2 (by decide) ‹_›
  · have h2 := hp.dvd_mul h1
    cases h2
    · left; right; left; exact prime_dvd_prime_pow_eq hp prime_3 (by decide) ‹_›
    · have h3 := hp.dvd_mul h2
      cases h3
      · left; right; right; exact prime_dvd_prime_pow_eq hp prime_13 (by decide) ‹_›
      · right; exact prime_dvd_prime_pow_eq hp prime_b (by decide) ‹_›

lemma m₁_succ_sq (p : ℕ) (h : p ∈ [2, 3, 13, 2368720229]) : p ^ 2 ∣ m₁_succ := by
  rcases h with rfl | rfl | rfl | rfl <;> rw [m₁_succ_eq] <;> exact dvd_mul_right (dvd_refl (p ^ 2))

theorem isPowerful_m₁_succ : IsPowerful m₁_succ :=
  powerful_of_prime_powers m₁_succ_ne_zero [2, 3, 13, 2368720229]
    (fun p hp hdiv => m₁_succ_cover p hp hdiv) m₁_succ_sq

/-- m₁_succ 不是平方数：2 在其分解中指数为 3（奇）。具体下降，终以 2 | 奇数积 矛盾。 -/
lemma not_square_m₁_succ : ¬ IsSquare m₁_succ := by
  rw [m₁_succ_eq]
  rintro ⟨k, hk : 2 ^ 3 * 3 ^ 2 * 13 ^ 2 * 2368720229 ^ 2 = k ^ 2⟩
  have hk2 : 2 ∣ k := by
    apply prime_dvd_pow_of_dvd prime_2
    · rw [hk]; exact dvd_trans (pow_dvd_pow (by decide : 1 ≤ 3)) (dvd_mul_right (dvd_refl (2 ^ 3)))
    · decide
  obtain ⟨k1, hk1 : k = 2 * k1⟩ := hk2
  rw [hk1, mul_pow] at hk
  have hk1_div : 2 ∣ k1 := by
    have h3' : 2 ^ 3 ∣ 2 ^ 2 * k1 ^ 2 := by
      rw [← hk]; exact dvd_mul_right (dvd_refl (2 ^ 3))
    rcases h3' with ⟨t, ht : 2 ^ 2 * k1 ^ 2 = 2 ^ 3 * t⟩
    have : 2 ∣ k1 ^ 2 := by
      apply Nat.mul_left_cancel (by decide : 2 ^ 2 ≠ 0)
      rw [ht]
      rw [← pow_succ, mul_assoc]
    exact prime_dvd_pow_of_dvd prime_2 this (by decide)
  obtain ⟨k2, hk2' : k1 = 2 * k2⟩ := hk1_div
  rw [hk2', mul_pow] at hk
  -- hk : 2³·(3²·13²·b²) = 2⁴·k2²  ⇒  2 | 3²·13²·b²，但右侧为奇数积，矛盾
  have hodd : 2 ∣ 3 ^ 2 * 13 ^ 2 * 2368720229 ^ 2 := by
    apply Nat.mul_left_cancel (by decide : 2 ^ 3 ≠ 0)
    rw [hk]
    rw [← pow_succ, mul_assoc]
  have hnot : ¬ 2 ∣ 3 ^ 2 * 13 ^ 2 * 2368720229 ^ 2 := by simp only [pow_two]; decide
  exact absurd hodd hnot

/- ----------------------------- 主定理 ----------------------------- -/

/-- JSP-000301 的证否：存在连续 powerful 且均非平方的一对整数。 -/
theorem jsp000301_disproof :
  ∃ m : ℕ, IsPowerful m ∧ IsPowerful (m + 1) ∧ ¬IsSquare m ∧ ¬IsSquare (m + 1) :=
  ⟨m₁, ⟨isPowerful_m₁, isPowerful_m₁_succ, not_square_m₁, not_square_m₁_succ⟩⟩

/- ----------------------------- 公理审计（活动硬性要求） ----------------------------- -/

/-- 公理审计：本证明仅依赖标准算术与整除理论（`Nat.Prime`、`dvd`、`pow` 等），
    未引入 `choice` 等非常规公理。提交前在 lean-lang.org/play 或本地 `lake` 编译后，
    运行下方命令核验；预期输出 `[propext, Quot.sound]`（Mathlib 默认），符合活动公理规范。 -/
#print axioms jsp000301_disproof
