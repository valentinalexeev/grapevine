import Sarafan
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Field.Rat

/-!
# Асимметричная информация: мозаика, рычаги, утечки

1. **Контекст решает.** Одна и та же подсказка не даёт постороннему ничего,
   а тому, у кого есть нужное знание, — всё сообщение (`context_decides`).
2. **Мозаика.** Фрагменты, каждый из которых по отдельности ничего не раскрывает,
   вместе раскрывают всё: аддитивное разделение (`additive_private`,
   `additive_reveal`) и пороговая схема Шамира (`shamir_reconstruct`,
   `shamir_private`): любые k фрагментов раскрывают секрет, любые k − 1 — ничего.
3. **Рычаги.** Чем больше знает Z, чем больше допустимая ошибка, чем шире сеть,
   чем короче её задержка и чем позже официальное объявление, тем легче слухам
   обогнать объявление (`levers`). Обратное — инструменты защиты.
4. **Утечка через посвящённых.** Если k посвящённых каждый день независимо
   проговариваются с вероятностью q, вероятность, что за T дней утечки не будет,
   равна (1 − q)^(kT). Она падает с ростом k и T (`noLeak_anti_insiders`,
   `noLeak_anti_days`), а риск утечки не больше k·T·q (`leak_le`).
   Отсюда правило: если k·T·q ≤ α, риск не больше α (`safe_window`).
-/

namespace Sarafan

open Polynomial

/-! ## 1. Контекст решает -/

/-- Подсказка `h = x + key`. Посторонний, не знающий `key`, не может исключить
ни одного сообщения; знающий `key` восстанавливает сообщение однозначно. -/
theorem context_decides {G : Type*} [AddGroup G] (h : G) :
    {x : G | ∃ key, x + key = h} = Set.univ ∧
      ∀ key, {x : G | x + key = h} = {h - key} := by
  refine ⟨Set.eq_univ_of_forall fun x => ⟨-x + h, by simp [← add_assoc]⟩, fun key => ?_⟩
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
  exact ⟨fun hx => eq_sub_of_add_eq hx, fun hx => by rw [hx, sub_add_cancel]⟩

/-! ## 2. Мозаика: аддитивное разделение секрета

Секрет — сумма n долей. Если не хватает хотя бы одной доли, остальные совместимы
с любым секретом, причём ровно одним способом: они не дают о секрете ничего. -/

theorem additive_private {G : Type*} [AddCommGroup G] {n : ℕ} (j : Fin n)
    (f : Fin n → G) (s' : G) :
    ∃! g : G, ∑ i, Function.update f j g i = s' := by
  have key : ∀ g, ∑ i, Function.update f j g i =
      g + ∑ i ∈ Finset.univ \ {j}, f i :=
    fun g => Finset.sum_update_of_mem (Finset.mem_univ j) f g
  refine ⟨s' - ∑ i ∈ Finset.univ \ {j}, f i, ?_, fun g hg => ?_⟩
  · simp only [key, sub_add_cancel]
  · have hg' : ∑ i, Function.update f j g i = s' := hg
    rw [key] at hg'
    exact eq_sub_of_add_eq hg'

/-- Все доли вместе раскрывают секрет. -/
theorem additive_reveal {G : Type*} [AddCommGroup G] {n : ℕ} (f g : Fin n → G)
    (h : ∀ i, f i = g i) : ∑ i, f i = ∑ i, g i := by
  simp [h]

/-! ## 2'. Мозаика: пороговая схема Шамира

Секрет `s` — значение в нуле многочлена степени `< k` над конечным полем.
Доля — значение многочлена в ненулевой точке. -/

/-- Любые k долей однозначно определяют многочлен, а значит и секрет. -/
theorem shamir_reconstruct {F : Type*} [Field F] {k : ℕ} (S : Finset F)
    (hS : k ≤ S.card) {p q : F[X]} (hp : p.degree < k) (hq : q.degree < k)
    (hpq : ∀ x ∈ S, p.eval x = q.eval x) : p.eval 0 = q.eval 0 := by
  have hk : (k : WithBot ℕ) ≤ S.card := by exact_mod_cast hS
  rw [Polynomial.eq_of_degrees_lt_of_eval_finset_eq S (lt_of_lt_of_le hp hk)
    (lt_of_lt_of_le hq hk) hpq]

/-- Любые k − 1 долей не дают о секрете ничего: для **каждого** возможного
секрета `s'` существует ровно один многочлен степени `< k`, согласующийся
с увиденными долями. Если раздающий выбирает многочлен равновероятно, то все
секреты остаются равновероятными. -/
theorem shamir_private {F : Type*} [Field F] [DecidableEq F] {k : ℕ}
    (S : Finset F) (hS : S.card + 1 = k) (h0 : (0 : F) ∉ S)
    (val : F → F) (s' : F) :
    ∃! p : F[X], p.degree < k ∧ p.eval 0 = s' ∧ ∀ x ∈ S, p.eval x = val x := by
  set T := insert (0 : F) S with hT
  have hTcard : T.card = k := by rw [hT, Finset.card_insert_of_notMem h0, hS]
  set r : F → F := Function.update val 0 s' with hr
  have hinj : Set.InjOn id (T : Set F) := Set.injOn_id _
  set p := Lagrange.interpolate T id r
  have hdeg : p.degree < k := by
    have := Lagrange.degree_interpolate_lt (s := T) (v := id) r hinj
    rw [hTcard] at this
    exact this
  have hnode : ∀ x ∈ T, p.eval x = r x := fun x hx =>
    Lagrange.eval_interpolate_at_node (s := T) (v := id) r hinj hx
  refine ⟨p, ⟨hdeg, ?_, fun x hx => ?_⟩, ?_⟩
  · rw [hnode 0 (Finset.mem_insert_self 0 S), hr, Function.update_self]
  · have hx0 : x ≠ 0 := fun h => h0 (h ▸ hx)
    rw [hnode x (Finset.mem_insert_of_mem hx), hr, Function.update_of_ne hx0]
  · rintro q ⟨hqdeg, hq0, hqS⟩
    have hk : (k : WithBot ℕ) = T.card := by rw [hTcard]
    refine Polynomial.eq_of_degrees_lt_of_eval_finset_eq T (hk ▸ hqdeg) (hk ▸ hdeg) ?_
    intro x hx
    rw [hnode x hx]
    rcases Finset.mem_insert.1 hx with rfl | hxS
    · rw [hq0, hr, Function.update_self]
    · have hx0 : x ≠ 0 := fun h => h0 (h ▸ hxS)
      rw [hqS x hxS, hr, Function.update_of_ne hx0]

/-! ## 3. Рычаги нападения и защиты -/

namespace SideInfo

variable {X Y : Type*} (dist : X → X → ℕ)

/-- Z побеждает слухами: восстанавливает сообщение раньше официального объявления. -/
def RumourWins (compat : X → Y → Prop) (r C d T : ℕ) : Prop :=
  ∃ τ < T, Solvable compat dist r (C * (τ - d))

/-- **Рычаги.** Если Z знает больше (`compat₂` уже `compat₁`), допускает большую
ошибку, сеть шире, её задержка меньше, а объявление позже — слухам не труднее.
Прочитанное наоборот: защищающийся уменьшает `C` (меньше посвящённых),
сдвигает объявление раньше (`T`), увеличивает задержку (`d`). -/
theorem levers {compat₁ compat₂ : X → Y → Prop} {r r' C C' d d' T T' : ℕ}
    (hfiner : ∀ x y, compat₂ x y → compat₁ x y) (hr : r ≤ r')
    (hC : C ≤ C') (hd : d' ≤ d) (hT : T ≤ T')
    (hwin : RumourWins dist compat₁ r C d T) :
    RumourWins dist compat₂ r' C' d' T' := by
  obtain ⟨τ, hτ, enc, dec, hok⟩ := hwin
  have hbase : Solvable compat₂ dist r' (C * (τ - d)) :=
    ⟨enc, dec, fun x y hxy => le_trans (hok x y (hfiner x y hxy)) hr⟩
  refine ⟨T' - 1, by omega, hbase.mono compat₂ dist r' ?_⟩
  exact Nat.mul_le_mul hC (by omega)

/-- Защита сроком: если объявить не позже, чем первые обрывки могут дойти до Z,
слухи не выигрывают ни при каких знаниях Z, если ему вообще нужна информация. -/
theorem announce_first {compat : X → Y → Prop} {r C d T : ℕ} (hT : T ≤ d)
    (hneed : ¬ Solvable compat dist r 0) :
    ¬ RumourWins dist compat r C d T := by
  rintro ⟨τ, hτ, h⟩
  have : C * (τ - d) = 0 := by
    rw [show τ - d = 0 by omega, Nat.mul_zero]
  rw [this] at h
  exact hneed h

end SideInfo

/-! ## 4. Утечка через посвящённых

Модель: k посвящённых, каждый день каждый независимо проговаривается
с вероятностью q. Вероятность, что за T дней утечки не будет, — `noLeak`. -/

section Leak

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

def noLeak (q : K) (k T : ℕ) : K := (1 - q) ^ (k * T)

theorem noLeak_anti_days {q : K} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (k : ℕ) {T T' : ℕ}
    (hT : T ≤ T') : noLeak q k T' ≤ noLeak q k T :=
  pow_le_pow_of_le_one (by linarith) (by linarith) (Nat.mul_le_mul_left k hT)

theorem noLeak_anti_insiders {q : K} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) {k k' : ℕ} (T : ℕ)
    (hk : k ≤ k') : noLeak q k' T ≤ noLeak q k T :=
  pow_le_pow_of_le_one (by linarith) (by linarith) (Nat.mul_le_mul_right T hk)

/-- Риск утечки не больше k·T·q (неравенство Бернулли). -/
theorem leak_le {q : K} (_hq0 : 0 ≤ q) (hq1 : q ≤ 1) (k T : ℕ) :
    1 - noLeak q k T ≤ k * T * q := by
  have h := one_add_mul_le_pow (a := -q) (by linarith) (k * T)
  unfold noLeak
  rw [← sub_eq_add_neg] at h
  push_cast at h
  linarith

/-- **Правило безопасного окна.** Если k·T·q ≤ α, риск утечки за T дней не больше α.
Например, при α = 1/2 и q = 1/100: 5 посвящённых — 10 дней, 50 посвящённых — 1 день. -/
theorem safe_window {q α : K} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) {k T : ℕ}
    (h : (k : K) * T * q ≤ α) : 1 - noLeak q k T ≤ α :=
  le_trans (leak_le hq0 hq1 k T) h

example : 1 - noLeak (1 / 100 : ℚ) 5 10 ≤ 1 / 2 :=
  safe_window (by norm_num) (by norm_num) (by norm_num)

example : 1 - noLeak (1 / 100 : ℚ) 50 1 ≤ 1 / 2 :=
  safe_window (by norm_num) (by norm_num) (by norm_num)

/-- Нижняя оценка риска: `noLeak · (1 + k·T·q) ≤ 1`, то есть
вероятность утечки не меньше `k·T·q / (1 + k·T·q)`. Вместе с `leak_le`
это значит, что риск растёт примерно пропорционально k·T·q. -/
theorem noLeak_mul_le {q : K} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (k T : ℕ) :
    noLeak q k T * (1 + k * T * q) ≤ 1 := by
  unfold noLeak
  set n := k * T with hn
  have h1 : 1 + (n : K) * q ≤ (1 + q) ^ n := one_add_mul_le_pow (by linarith) n
  have h2 : (1 - q) ^ n * (1 + q) ^ n ≤ 1 := by
    rw [← mul_pow]
    exact pow_le_one₀ (by nlinarith) (by nlinarith)
  have h3 : (1 - q) ^ n * (1 + (n : K) * q) ≤ (1 - q) ^ n * (1 + q) ^ n :=
    mul_le_mul_of_nonneg_left h1 (pow_nonneg (by linarith) n)
  have hcast : ((k : K) * T * q) = (n : K) * q := by rw [hn]; push_cast; ring
  rw [hcast]
  linarith

/-- При 50 посвящённых за 10 дней утечка происходит с вероятностью не меньше 5/6. -/
example : 1 - noLeak (1 / 100 : ℚ) 50 10 ≥ 5 / 6 := by
  have h := noLeak_mul_le (q := (1 / 100 : ℚ)) (by norm_num) (by norm_num) 50 10
  norm_num at h ⊢
  linarith

end Leak

end Sarafan
