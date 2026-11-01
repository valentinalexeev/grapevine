import SarafanMosaic
import Mathlib.Tactic.LinearCombination

/-!
# Конфликт интересов ограничивает передачу информации (Кроуфорд–Собел, 1982)

Модель:
* отправитель знает число θ ∈ [0, 1] (например, настоящий бюджет);
* получатель выбирает действие a; он хочет a = θ, а отправитель хочет a = θ + b;
  `b` — конфликт интересов;
* слова ничего не стоят и не проверяются.

В равновесии отправитель сообщает только, в каком из N интервалов лежит θ:
границы 0 = a₀ < a₁ < … < a_N = 1, а получатель на интервале выбирает его середину
(это его оптимум при квадратичных потерях и равномерном распределении θ;
это свойство входит в модель как предположение).

Доказано:
* `IsEquilibrium.indiff` — на каждой границе отправителю безразлично,
  какой из двух соседних интервалов назвать;
* `IsEquilibrium.gap_step` — каждый следующий интервал длиннее предыдущего на 4b;
* **`crawford_sobel`** — в любом равновесии с N интервалами 2·N·(N − 1)·b < 1;
* `fewer_intervals`, `no_info` — при большом конфликте интервалов мало,
  при b ≥ 1/4 — один, то есть слова не передают ничего;
* `exists_equilibrium` — если 2·N·(N − 1)·b < 1, равновесие с N интервалами существует;
* **`equilibrium_exists_iff`** — точный критерий: равновесие с N интервалами
  существует ⇔ 2·N·(N − 1)·b < 1.

Следствие для передачи информации: за один такой разговор честно передаётся
не больше log₂N(b) бит, где N(b) — наибольшее N с 2·N·(N − 1)·b < 1.
-/

namespace Sarafan.CheapTalk

/-- Разбиение отрезка [0, 1] на N интервалов. -/
structure Partition (K : Type*) [Zero K] [One K] [LT K] (N : ℕ) where
  a : ℕ → K
  zero : a 0 = 0
  one : a N = 1
  mono : ∀ i < N, a i < a (i + 1)

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

namespace Partition

variable {N : ℕ} (P : Partition K N)

/-- Действие получателя, услышавшего «интервал i», — середина интервала. -/
def mid (i : ℕ) : K := (P.a i + P.a (i + 1)) / 2

/-- Равновесие: отправитель любого типа θ из интервала i (включая границы)
не хочет назвать никакой другой интервал j. -/
def IsEquilibrium (b : K) : Prop :=
  ∀ i < N, ∀ θ : K, P.a i ≤ θ → θ ≤ P.a (i + 1) →
    ∀ j < N, (P.mid i - (θ + b)) ^ 2 ≤ (P.mid j - (θ + b)) ^ 2

variable {P}

/-- На границе двух интервалов отправителю безразлично, какой назвать:
его идеальное действие ровно посередине между двумя действиями получателя. -/
theorem IsEquilibrium.indiff {b : K} (h : P.IsEquilibrium b) {i : ℕ} (hi : i + 1 < N) :
    P.a (i + 1) + b = (P.mid i + P.mid (i + 1)) / 2 := by
  have h1 := h i (by omega) (P.a (i + 1)) (le_of_lt (P.mono i (by omega))) le_rfl (i + 1) hi
  have h2 := h (i + 1) hi (P.a (i + 1)) le_rfl (le_of_lt (P.mono (i + 1) hi)) i (by omega)
  have heq := le_antisymm h1 h2
  have hlt : P.mid i < P.mid (i + 1) := by
    unfold mid
    have := P.mono i (by omega)
    have := P.mono (i + 1) hi
    linarith
  have hprod : (P.mid (i + 1) - P.mid i) *
      (P.mid (i + 1) + P.mid i - 2 * (P.a (i + 1) + b)) = 0 := by
    linear_combination (-1 : K) * heq
  rcases mul_eq_zero.1 hprod with h0 | h0
  · linarith
  · linarith

/-- Каждый следующий интервал длиннее предыдущего ровно на 4b. -/
theorem IsEquilibrium.gap_step {b : K} (h : P.IsEquilibrium b) {i : ℕ} (hi : i + 1 < N) :
    P.a (i + 1 + 1) - P.a (i + 1) = (P.a (i + 1) - P.a i) + 4 * b := by
  have := h.indiff hi
  unfold mid at this
  linarith

/-- Длина k-го интервала: длина первого плюс 4·b·k. -/
theorem IsEquilibrium.gap {b : K} (h : P.IsEquilibrium b) :
    ∀ k < N, P.a (k + 1) - P.a k = (P.a 1 - P.a 0) + 4 * b * k := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    have hs := h.gap_step (i := k) hk
    have := ih (by omega)
    push_cast
    linarith

/-- Положение k-й границы. -/
theorem IsEquilibrium.position {b : K} (h : P.IsEquilibrium b) :
    ∀ k ≤ N, P.a k = k * (P.a 1 - P.a 0) + 2 * b * k * (k - 1) := by
  intro k
  induction k with
  | zero => intro _; simp [P.zero]
  | succ k ih =>
    intro hk
    have hg := h.gap k (by omega)
    have := ih (by omega)
    push_cast
    linear_combination hg + this

end Partition

open Partition

/-- **Граница Кроуфорда–Собела.** В любом равновесии с N интервалами
`2·N·(N − 1)·b < 1`. -/
theorem crawford_sobel {N : ℕ} {P : Partition K N} {b : K} (h : P.IsEquilibrium b)
    (hN : 0 < N) : 2 * (N : K) * (N - 1) * b < 1 := by
  have hpos := h.position N le_rfl
  rw [P.one] at hpos
  have hg : 0 < P.a 1 - P.a 0 := sub_pos.2 (by simpa using P.mono 0 hN)
  have hNpos : (0 : K) < N := by exact_mod_cast hN
  nlinarith [mul_pos hNpos hg]

/-- Если `2·n·(n − 1)·b ≥ 1`, в равновесии меньше n интервалов. -/
theorem fewer_intervals {N : ℕ} {P : Partition K N} {b : K} (hb : 0 ≤ b)
    (h : P.IsEquilibrium b) (hN : 0 < N) {n : ℕ}
    (hn : 1 ≤ 2 * (n : K) * (n - 1) * b) : N < n := by
  rcases Nat.eq_zero_or_pos n with rfl | hnpos
  · norm_num at hn
  by_contra hcon
  have hnN : (n : K) ≤ N := by exact_mod_cast not_lt.1 hcon
  have hn1 : (1 : K) ≤ n := by exact_mod_cast hnpos
  have hcs := crawford_sobel h hN
  have hprod : (n : K) * (n - 1) ≤ N * (N - 1) :=
    mul_le_mul hnN (by linarith) (by linarith) (by linarith)
  have := mul_le_mul_of_nonneg_right hprod hb
  nlinarith

/-- При конфликте интересов b ≥ 1/4 слова не передают ничего: интервал один. -/
theorem no_info {N : ℕ} {P : Partition K N} {b : K} (hb : 1 / 4 ≤ b)
    (h : P.IsEquilibrium b) (hN : 0 < N) : N = 1 := by
  have := fewer_intervals (n := 2) (by linarith) h hN (by norm_num; linarith)
  omega

lemma sq_le_of_mid_le {u v t : K} (huv : u ≤ v) (ht : 2 * t ≤ u + v) :
    (u - t) ^ 2 ≤ (v - t) ^ 2 := by
  nlinarith [mul_nonneg (sub_nonneg.2 huv) (by linarith : (0 : K) ≤ u + v - 2 * t)]

lemma sq_le_of_le_mid {u v t : K} (hvu : v ≤ u) (ht : u + v ≤ 2 * t) :
    (u - t) ^ 2 ≤ (v - t) ^ 2 := by
  nlinarith [mul_nonneg (sub_nonneg.2 hvu) (by linarith : (0 : K) ≤ 2 * t - u - v)]

/-- **Граница достижима.** Если `2·N·(N − 1)·b < 1`, равновесие с N интервалами
существует: интервалы растут на 4b, первый занимает оставшуюся длину. -/
theorem exists_equilibrium {b : K} (hb : 0 ≤ b) {N : ℕ} (hN : 0 < N)
    (h : 2 * (N : K) * (N - 1) * b < 1) : ∃ P : Partition K N, P.IsEquilibrium b := by
  have hNpos : (0 : K) < N := by exact_mod_cast hN
  have hN0 : (N : K) ≠ 0 := ne_of_gt hNpos
  set g : K := (1 - 2 * N * (N - 1) * b) / N with hg
  have hgpos : 0 < g := div_pos (by linarith) hNpos
  let a : ℕ → K := fun k => k * g + 2 * b * k * (k - 1)
  have hstep : ∀ i : ℕ, a (i + 1) - a i = g + 4 * b * i := by
    intro i; simp only [a]; push_cast; ring
  have hmono : ∀ i, a i < a (i + 1) := by
    intro i
    have := hstep i
    have : (0 : K) ≤ 4 * b * i := by positivity
    linarith
  refine ⟨⟨a, by simp [a], ?_, fun i _ => hmono i⟩, ?_⟩
  · simp only [a]
    rw [hg]
    field_simp
    ring
  · intro i hi θ hθ1 hθ2 j hj
    let m : ℕ → K := fun k => (a k + a (k + 1)) / 2
    change (m i - (θ + b)) ^ 2 ≤ (m j - (θ + b)) ^ 2
    have hind : ∀ k, 2 * (a (k + 1) + b) = m k + m (k + 1) := by
      intro k; simp only [m, a]; push_cast; ring
    have hmmono : Monotone m := by
      refine monotone_nat_of_le_succ fun k => ?_
      have h1 := hmono k
      have h2 := hmono (k + 1)
      simp only [m]
      linarith
    change a i ≤ θ at hθ1
    change θ ≤ a (i + 1) at hθ2
    rcases lt_trichotomy i j with hlt | rfl | hgt
    · apply sq_le_of_mid_le (hmmono hlt.le)
      have := hind i
      have := hmmono (show i + 1 ≤ j by omega)
      linarith
    · exact le_rfl
    · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
      apply sq_le_of_le_mid (hmmono hgt.le)
      have := hind i'
      have := hmmono (show j ≤ i' by omega)
      linarith

/-- **Точный критерий.** Равновесие с N интервалами существует ⇔ `2·N·(N − 1)·b < 1`. -/
theorem equilibrium_exists_iff {b : K} (hb : 0 ≤ b) {N : ℕ} (hN : 0 < N) :
    (∃ P : Partition K N, P.IsEquilibrium b) ↔ 2 * (N : K) * (N - 1) * b < 1 :=
  ⟨fun ⟨_, hP⟩ => crawford_sobel hP hN, exists_equilibrium hb hN⟩

/-! ### Примеры -/

/-- Конфликт 1%: 7 интервалов возможны (≈ 2,8 бита) … -/
example : ∃ P : Partition ℚ 7, P.IsEquilibrium (1 / 100) :=
  exists_equilibrium (by norm_num) (by norm_num) (by norm_num)

/-- … а 8 — уже нет. -/
example : ¬ ∃ P : Partition ℚ 8, P.IsEquilibrium (1 / 100) := by
  rw [equilibrium_exists_iff (by norm_num) (by norm_num)]
  norm_num

/-- Конфликт 1/4: даже два интервала невозможны — слова ничего не значат. -/
example : ¬ ∃ P : Partition ℚ 2, P.IsEquilibrium (1 / 4) := by
  rw [equilibrium_exists_iff (by norm_num) (by norm_num)]
  norm_num

end Sarafan.CheapTalk
