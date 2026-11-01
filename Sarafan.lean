import Mathlib.Tactic.Common
import Mathlib.Tactic.Positivity
import Mathlib.InformationTheory.Hamming
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Сарафанное радио: формальная модель

Вопрос: может ли оператор в узле Z восстановить сообщение из обрывков,
пришедших по сети, раньше, чем к нему напрямую придёт точное сообщение из A?

Модель (комбинаторная, без вероятностей):
* сообщение разбито с избыточностью на `m` фрагментов (как в кодах Рида–Соломона);
* для восстановления нужно `k` верных фрагментов, и ещё по 2 на каждый
  из `t` возможно искажённых — итого `k + 2t`;
* `arrival i` — момент прихода i-го фрагмента в Z;
* `tDirect` — момент прихода точного сообщения по прямому каналу.

Что доказано:
1. `rumourWins_iff`, `rumourWins_iff_fast_set` — точный критерий выигрыша сети.
2. `rumour_sometimes_wins`, `rumour_not_always_wins` — универсальная версия
   теории («всегда быстрее») ложна, но теория выполнима.
3. `causality` — если прямой канал не медленнее кратчайшего пути в сети,
   сарафан не выигрывает никогда.
4. `parallel_wins` — если прямой канал узкий, а путей достаточно,
   сарафан выигрывает гарантированно.
5. `unique_decoding`, `unique_codeword` — восстановление по искажённым данным
   корректно, если кодовые слова различаются больше чем в 2t позициях.
6. `prior_knowledge`, `prior_knowledge_tight` — если Z знает, что сообщение
   одно из |S| кандидатов, достаточно ровно ⌈log₂|S|⌉ бит, и меньше нельзя.
7. `tolerance_mono`, `exact_impossible_of_corrupt`, `example_80_wins` —
   допустимая ошибка: при искажениях без кодирования точное восстановление
   невозможно, а порог 80% достижим.
8. `rumour_general`, `rumour_general_loses` — общая теорема: сарафан может выиграть,
   только если log₂|M| − log₂V(r) ≤ C · (tDirect − 1 − d).
9. `SideInfo.rumour_exact`, `SideInfo.solvable_iff` — точная теорема (необходимо
   и достаточно) для случая, когда A и сеть не знают, что известно Z
   (постановка Wyner–Ziv / Witsenhausen).
   `Pentagon.price_of_blindness` — пример, где это незнание стоит лишний бит.
-/

namespace Sarafan

/-! ## 1. Модель и критерий -/

structure Scenario where
  /-- сколько верных фрагментов нужно для восстановления -/
  k       : ℕ
  /-- сколько фрагментов может прийти искажёнными -/
  t       : ℕ
  /-- сколько фрагментов идёт по сети -/
  m       : ℕ
  /-- момент прихода i-го фрагмента в Z -/
  arrival : Fin m → ℕ
  /-- момент прихода точного сообщения напрямую из A -/
  tDirect : ℕ

namespace Scenario

/-- Сколько фрагментов нужно с учётом возможных искажений. -/
def need (s : Scenario) : ℕ := s.k + 2 * s.t

/-- Сколько фрагментов пришло в Z к моменту τ. -/
def received (s : Scenario) (τ : ℕ) : ℕ :=
  (Finset.univ.filter (fun i => s.arrival i ≤ τ)).card

/-- К моменту τ Z может однозначно восстановить сообщение. -/
def canDecodeAt (s : Scenario) (τ : ℕ) : Prop := s.need ≤ s.received τ

instance (s : Scenario) (τ : ℕ) : Decidable (s.canDecodeAt τ) :=
  inferInstanceAs (Decidable (s.need ≤ s.received τ))

/-- Теория верна для сценария: Z восстановил сообщение строго раньше прямой доставки. -/
def rumourWins (s : Scenario) : Prop := ∃ τ < s.tDirect, s.canDecodeAt τ

/-- Чем позже, тем больше фрагментов пришло. -/
theorem received_mono (s : Scenario) {τ₁ τ₂ : ℕ} (h : τ₁ ≤ τ₂) :
    s.received τ₁ ≤ s.received τ₂ := by
  unfold received
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  omega

/-- Критерий: достаточно проверить последний момент перед прямой доставкой. -/
theorem rumourWins_iff (s : Scenario) :
    s.rumourWins ↔ 0 < s.tDirect ∧ s.canDecodeAt (s.tDirect - 1) := by
  constructor
  · rintro ⟨τ, hτ, hd⟩
    refine ⟨by omega, ?_⟩
    unfold canDecodeAt at hd ⊢
    exact le_trans hd (s.received_mono (by omega))
  · rintro ⟨hpos, hd⟩
    exact ⟨s.tDirect - 1, by omega, hd⟩

instance (s : Scenario) : Decidable s.rumourWins :=
  decidable_of_iff _ s.rumourWins_iff.symm

/-- Критерий в «человеческой» форме: сеть выигрывает тогда и только тогда,
когда найдётся `k + 2t` фрагментов, каждый из которых обгоняет прямую доставку. -/
theorem rumourWins_iff_fast_set (s : Scenario) (hk : 0 < s.k) :
    s.rumourWins ↔
      ∃ S : Finset (Fin s.m), s.need ≤ S.card ∧ ∀ i ∈ S, s.arrival i < s.tDirect := by
  constructor
  · intro h
    obtain ⟨hpos, hd⟩ := s.rumourWins_iff.1 h
    refine ⟨Finset.univ.filter (fun i => s.arrival i ≤ s.tDirect - 1), hd, ?_⟩
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    omega
  · rintro ⟨S, hcard, hfast⟩
    have h0 : 0 < S.card := by
      have : s.need = s.k + 2 * s.t := rfl
      omega
    obtain ⟨i, hi⟩ := Finset.card_pos.mp h0
    have hpos : 0 < s.tDirect := by
      have := hfast i hi
      omega
    refine ⟨s.tDirect - 1, by omega, ?_⟩
    unfold canDecodeAt received
    refine le_trans hcard (Finset.card_le_card ?_)
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have := hfast j hj
    omega

end Scenario

open Scenario

/-! ## 2. Иногда да, но не всегда -/

/-- Нужно 2 фрагмента без искажений; они приходят в моменты 1, 1, 2;
прямая доставка — в момент 10. -/
def sFast : Scenario := ⟨2, 0, 3, ![1, 1, 2], 10⟩

/-- Те же параметры, но фрагменты приходят в моменты 5, 12, 20. -/
def sSlow : Scenario := ⟨2, 0, 3, ![5, 12, 20], 10⟩

theorem fast_wins : sFast.rumourWins := by decide

theorem slow_loses : ¬ sSlow.rumourWins := by decide

theorem rumour_sometimes_wins : ∃ s : Scenario, s.rumourWins := ⟨sFast, fast_wins⟩

/-- Универсальная версия теории («всегда быстрее») ложна. -/
theorem rumour_not_always_wins : ¬ ∀ s : Scenario, s.rumourWins :=
  fun h => slow_loses (h sSlow)

/-! ## 3. Причинность: когда сарафан проигрывает всегда -/

/-- Если каждый фрагмент идёт не быстрее `d` (кратчайший путь в сети),
а прямой канал доставляет к моменту `d` или раньше, сеть не выигрывает. -/
theorem causality (s : Scenario) (d : ℕ) (hk : 0 < s.k)
    (hlat : ∀ i, d ≤ s.arrival i) (hdir : s.tDirect ≤ d) : ¬ s.rumourWins := by
  rw [s.rumourWins_iff_fast_set hk]
  rintro ⟨S, hcard, hfast⟩
  have h0 : 0 < S.card := by
    have : s.need = s.k + 2 * s.t := rfl
    omega
  obtain ⟨i, hi⟩ := Finset.card_pos.mp h0
  have h1 := hfast i hi
  have h2 := hlat i
  omega

/-! ## 4. Пропускная способность: когда сарафан выигрывает гарантированно -/

/-- Сообщение из `k * f` символов. Прямой канал: задержка `L`, скорость `c`.
Сеть: `m` параллельных путей, каждый с задержкой `L'` и скоростью `c'`,
по каждому идёт один фрагмент из `f` символов. -/
def parallel (k t m L L' f c c' : ℕ) : Scenario where
  k := k
  t := t
  m := m
  arrival := fun _ => L' + f / c'
  tDirect := L + (k * f) / c

/-- Узкий прямой канал + достаточно путей ⇒ сарафан выигрывает. -/
theorem parallel_wins (k t m L L' f c c' : ℕ) (hm : k + 2 * t ≤ m)
    (hfast : L' + f / c' < L + (k * f) / c) :
    (parallel k t m L L' f c c').rumourWins := by
  refine ⟨L' + f / c', hfast, ?_⟩
  show k + 2 * t ≤ (Finset.univ.filter (fun _ : Fin m => L' + f / c' ≤ L' + f / c')).card
  simpa using hm

/-! ## 5. Корректность восстановления по искажённым данным -/

/-- Если кодовые слова отстоят больше чем на 2t, а принятое слово `r`
искажено не более чем в `t` позициях относительно `c₁`, спутать его с `c₂` нельзя. -/
theorem unique_decoding {ι : Type*} [Fintype ι] {β : ι → Type*}
    [∀ i, DecidableEq (β i)] {c₁ c₂ r : ∀ i, β i} {t : ℕ}
    (hd : 2 * t < hammingDist c₁ c₂)
    (h₁ : hammingDist r c₁ ≤ t) :
    t < hammingDist r c₂ := by
  have := hammingDist_triangle c₁ r c₂
  rw [hammingDist_comm c₁ r] at this
  omega

/-- В коде с минимальным расстоянием больше 2t любое слово, искажённое
не более чем в t позициях, однозначно определяет исходное кодовое слово. -/
theorem unique_codeword {ι : Type*} [Fintype ι] {β : ι → Type*}
    [∀ i, DecidableEq (β i)] (C : Set (∀ i, β i)) (t : ℕ)
    (hC : ∀ c₁ ∈ C, ∀ c₂ ∈ C, c₁ ≠ c₂ → 2 * t < hammingDist c₁ c₂)
    {r c₁ c₂ : ∀ i, β i} (h₁ : c₁ ∈ C) (h₂ : c₂ ∈ C)
    (hr₁ : hammingDist r c₁ ≤ t) (hr₂ : hammingDist r c₂ ≤ t) : c₁ = c₂ := by
  by_contra hne
  have := unique_decoding (hC c₁ h₁ c₂ h₂ hne) hr₁
  omega

/-! ## 6. Априорное знание Z -/

/-- Если Z знает, что сообщение — одно из `|S| ≤ 2^b` кандидатов,
ему достаточно получить `b` бит, а не всё сообщение. -/
theorem prior_knowledge {S : Type*} [Fintype S] (b : ℕ)
    (h : Fintype.card S ≤ 2 ^ b) :
    ∃ enc : S → Fin (2 ^ b), Function.Injective enc := by
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le (α := S) (β := Fin (2 ^ b))
    (by rw [Fintype.card_fin]; exact h)
  exact ⟨e, e.injective⟩

/-- И меньше нельзя: если кандидатов больше `2^b`, `b` бит не хватит. -/
theorem prior_knowledge_tight {S : Type*} [Fintype S] (b : ℕ)
    (h : 2 ^ b < Fintype.card S) (enc : S → Fin (2 ^ b)) :
    ¬ Function.Injective enc := by
  intro hinj
  have h2 : Fintype.card S ≤ 2 ^ b := by
    simpa using Fintype.card_le_of_injective enc hinj
  exact absurd h2 (not_le.mpr h)

/-! ## 7. Допустимая ошибка: частичное восстановление

Сообщение разбито на `m` кусков без кодирования. Каждый кусок идёт по сети
и либо приходит целым, либо искажённым. Z принимает решение, когда у него
есть хотя бы `q` верных кусков из `m` (например, 8 из 10 = 80%). -/

structure Partial where
  m       : ℕ
  arrival : Fin m → ℕ
  clean   : Fin m → Bool
  tDirect : ℕ

namespace Partial

/-- Сколько верных кусков есть у Z к моменту τ. -/
def goodBy (p : Partial) (τ : ℕ) : ℕ :=
  (Finset.univ.filter (fun i => p.arrival i ≤ τ ∧ p.clean i = true)).card

/-- Z может принять решение с точностью не хуже q из m. -/
def canDecideAt (p : Partial) (q τ : ℕ) : Prop := q ≤ p.goodBy τ

instance (p : Partial) (q τ : ℕ) : Decidable (p.canDecideAt q τ) :=
  inferInstanceAs (Decidable (q ≤ p.goodBy τ))

def wins (p : Partial) (q : ℕ) : Prop := ∃ τ < p.tDirect, p.canDecideAt q τ

/-- Чем больше допустимая ошибка, тем легче выиграть. -/
theorem tolerance_mono (p : Partial) {q₁ q₂ : ℕ} (h : q₁ ≤ q₂) (hw : p.wins q₂) :
    p.wins q₁ := by
  obtain ⟨τ, hτ, hd⟩ := hw
  exact ⟨τ, hτ, le_trans h hd⟩

/-- Если хоть один кусок искажён, точное восстановление без кодирования невозможно. -/
theorem goodBy_lt_of_corrupt (p : Partial) (i : Fin p.m) (hi : p.clean i = false)
    (τ : ℕ) : p.goodBy τ < p.m := by
  unfold goodBy
  calc (Finset.univ.filter (fun j => p.arrival j ≤ τ ∧ p.clean j = true)).card
      ≤ (Finset.univ.erase i).card := by
        apply Finset.card_le_card
        intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
        simp only [Finset.mem_erase, Finset.mem_univ, and_true]
        intro hji
        rw [hji, hi] at hj
        simp at hj
    _ < p.m := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
          Fintype.card_fin]
        have := i.isLt
        omega

theorem exact_impossible_of_corrupt (p : Partial) (i : Fin p.m)
    (hi : p.clean i = false) : ¬ p.wins p.m := by
  rintro ⟨τ, _, hd⟩
  have := p.goodBy_lt_of_corrupt i hi τ
  unfold canDecideAt at hd
  omega

/-- 10 кусков: 9 приходят к моменту 9, последний — к моменту 50.
Прямая доставка — к моменту 20. Один кусок по дороге искажён. -/
def example10 : Partial :=
  ⟨10, ![1, 2, 3, 4, 5, 6, 7, 8, 9, 50],
       ![true, true, true, false, true, true, true, true, true, true], 20⟩

/-- Требование 100% — сарафан проигрывает. -/
theorem example_exact_loses : ¬ example10.wins 10 :=
  example10.exact_impossible_of_corrupt ⟨3, by decide⟩ (by decide)

/-- Требование 80% — сарафан выигрывает: к моменту 9 есть 8 верных кусков. -/
theorem example_80_wins : example10.wins 8 := ⟨9, by decide, by decide⟩

end Partial

/-! ## 8. Общая теорема

Общая постановка:
* `M` — сообщения, которые Z считает возможными (априорное знание уже учтено:
  чем больше Z знает, тем меньше `M`);
* `dist` — мера ошибки, `r` — допустимая ошибка;
* `V` — сколько сообщений помещается в «шар допустимой ошибки» радиуса `r`;
* `bits τ` — сколько бит полезной информации дошло до Z к моменту τ;
* `d` — длина кратчайшего пути от A до Z, `C` — пропускная способность
  минимального разреза сети между A и Z (бит за единицу времени).

Сеть физически не может доставить больше чем `C * (τ - d)` бит к моменту τ
(при τ ≤ d это ноль — причинность).

Теорема: если Z успевает до прямой доставки восстановить любое сообщение из `M`
с ошибкой не больше `r`, то `|M| ≤ 2^(C·(tDirect − 1 − d)) · V`.
В логарифмах: `log₂|M| − log₂V ≤ C · (tDirect − 1 − d)`.

Слева — сколько информации Z действительно нужно (неопределённость минус то,
что прощает допустимая ошибка). Справа — сколько сеть может доставить
до прямого сообщения. -/

/-- Лемма о покрытии: b бит с ошибкой ≤ r различают не больше `2^b · V` сообщений. -/
theorem covering_bound {M : Type*} [Fintype M] (dist : M → M → ℕ) (r b V : ℕ)
    (enc : M → Fin (2 ^ b)) (dec : Fin (2 ^ b) → M)
    (hok : ∀ x, dist (dec (enc x)) x ≤ r)
    (hV : ∀ c, (Finset.univ.filter (fun x => dist c x ≤ r)).card ≤ V) :
    Fintype.card M ≤ 2 ^ b * V := by
  classical
  have hsub : (Finset.univ : Finset M) ⊆
      Finset.univ.biUnion
        (fun w : Fin (2 ^ b) => Finset.univ.filter (fun x => dist (dec w) x ≤ r)) := by
    intro x _
    simp only [Finset.mem_biUnion, Finset.mem_univ, Finset.mem_filter, true_and]
    exact ⟨enc x, hok x⟩
  calc Fintype.card M = (Finset.univ : Finset M).card := Finset.card_univ.symm
    _ ≤ _ := Finset.card_le_card hsub
    _ ≤ ∑ w : Fin (2 ^ b), (Finset.univ.filter (fun x => dist (dec w) x ≤ r)).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _w : Fin (2 ^ b), V := Finset.sum_le_sum (fun w _ => hV (dec w))
    _ = 2 ^ b * V := by simp

/-- **Общая теорема о сарафанном радио** (необходимое условие выигрыша). -/
theorem rumour_general {M : Type*} [Fintype M] (dist : M → M → ℕ) (r V : ℕ)
    (hV : ∀ c, (Finset.univ.filter (fun x => dist c x ≤ r)).card ≤ V)
    (bits : ℕ → ℕ) (d C tDirect : ℕ)
    (hcap : ∀ τ, bits τ ≤ C * (τ - d))
    (hwin : ∃ τ < tDirect, ∃ (enc : M → Fin (2 ^ bits τ)) (dec : Fin (2 ^ bits τ) → M),
        ∀ x, dist (dec (enc x)) x ≤ r) :
    Fintype.card M ≤ 2 ^ (C * (tDirect - 1 - d)) * V := by
  obtain ⟨τ, hτ, enc, dec, hok⟩ := hwin
  have h1 := covering_bound dist r (bits τ) V enc dec hok hV
  have h2 : bits τ ≤ C * (tDirect - 1 - d) :=
    le_trans (hcap τ) (Nat.mul_le_mul_left C (by omega))
  exact le_trans h1 (Nat.mul_le_mul_right V (Nat.pow_le_pow_right (by norm_num) h2))

/-- То же в форме опровержения: если информации нужно больше, чем сеть
успевает доставить, сарафан проигрывает при любой стратегии узлов и Z. -/
theorem rumour_general_loses {M : Type*} [Fintype M] (dist : M → M → ℕ) (r V : ℕ)
    (hV : ∀ c, (Finset.univ.filter (fun x => dist c x ≤ r)).card ≤ V)
    (bits : ℕ → ℕ) (d C tDirect : ℕ)
    (hcap : ∀ τ, bits τ ≤ C * (τ - d))
    (hbig : 2 ^ (C * (tDirect - 1 - d)) * V < Fintype.card M) :
    ¬ ∃ τ < tDirect, ∃ (enc : M → Fin (2 ^ bits τ)) (dec : Fin (2 ^ bits τ) → M),
        ∀ x, dist (dec (enc x)) x ≤ r := by
  intro hwin
  have := rumour_general dist r V hV bits d C tDirect hcap hwin
  exact absurd this (not_le.mpr hbig)

/-! ## 9. Точная теорема: знания Z, о которых A не знает (постановка Wyner–Ziv)

В разделе 8 знания Z сужали множество сообщений «для всех». В реальной сети
источник и узлы не знают, что именно известно Z. Поэтому:
* `X` — все сообщения, `Y` — возможные состояния знаний Z;
* `compat x y` — сообщение `x` не противоречит знаниям `y`;
* кодер (A и сеть) видит только `x`, декодер (Z) — полученные биты и `y`.

Здесь ответ точный (необходимо и достаточно), без асимптотики Шеннона:
задача решается `b` битами ⇔ сообщения можно раскрасить в `2^b` цветов так,
чтобы внутри каждого цвета сообщения, совместимые с одним `y`,
лежали в одном шаре ошибки радиуса `r`. -/

namespace SideInfo

variable {X Y : Type*} (compat : X → Y → Prop) (dist : X → X → ℕ) (r : ℕ)

/-- Z восстанавливает сообщение с ошибкой ≤ r, получив b бит;
кодер не знает знаний Z. -/
def Solvable (b : ℕ) : Prop :=
  ∃ (enc : X → Fin (2 ^ b)) (dec : Fin (2 ^ b) → Y → X),
    ∀ x y, compat x y → dist (dec (enc x) y) x ≤ r

/-- То же, но кодер знает знания Z (так было неявно в разделе 8). -/
def SolvableInformed (b : ℕ) : Prop :=
  ∃ (enc : X → Y → Fin (2 ^ b)) (dec : Fin (2 ^ b) → Y → X),
    ∀ x y, compat x y → dist (dec (enc x y) y) x ≤ r

/-- Допустимая раскраска сообщений в `2^b` цветов. -/
def GoodColoring {b : ℕ} (c : X → Fin (2 ^ b)) : Prop :=
  ∀ y w, ∃ center : X, ∀ x, compat x y → c x = w → dist center x ≤ r

/-- **Точный критерий.** b бит хватает ⇔ есть допустимая раскраска в 2^b цветов. -/
theorem solvable_iff [Nonempty X] (b : ℕ) :
    Solvable compat dist r b ↔ ∃ c : X → Fin (2 ^ b), GoodColoring compat dist r c := by
  constructor
  · rintro ⟨enc, dec, hok⟩
    refine ⟨enc, fun y w => ⟨dec w y, fun x hx hc => ?_⟩⟩
    subst hc
    exact hok x y hx
  · rintro ⟨c, hc⟩
    choose center hcenter using hc
    exact ⟨c, fun w y => center y w, fun x y hx => hcenter y (c x) x hx rfl⟩

/-- Если A знает, что известно Z, задача не сложнее. -/
theorem Solvable.informed {b : ℕ} (h : Solvable compat dist r b) :
    SolvableInformed compat dist r b := by
  obtain ⟨enc, dec, hok⟩ := h
  exact ⟨fun x _ => enc x, dec, hok⟩

/-- Больше бит — не хуже. -/
theorem Solvable.mono {b b' : ℕ} (h : Solvable compat dist r b) (hb : b ≤ b') :
    Solvable compat dist r b' := by
  obtain ⟨enc, dec, hok⟩ := h
  have hle : 2 ^ b ≤ 2 ^ b' := Nat.pow_le_pow_right (by norm_num) hb
  refine ⟨fun x => Fin.castLE hle (enc x),
    fun w y => if hw : w.val < 2 ^ b then dec ⟨w.val, hw⟩ y
      else dec ⟨0, by positivity⟩ y, ?_⟩
  intro x y hxy
  have hlt : (Fin.castLE hle (enc x)).val < 2 ^ b := (enc x).isLt
  beta_reduce
  split
  · exact hok x y hxy
  · next h => exact absurd hlt h

/-- Нижняя граница из раздела 8 остаётся верной для каждого состояния знаний Z:
`|M_y| ≤ 2^b · V`, где `M_y` — сообщения, совместимые со знаниями `y`. -/
theorem card_bound [Fintype X] [∀ x y, Decidable (compat x y)] {b V : ℕ}
    (h : Solvable compat dist r b)
    (hV : ∀ c, (Finset.univ.filter (fun x => dist c x ≤ r)).card ≤ V) (y : Y) :
    (Finset.univ.filter (fun x => compat x y)).card ≤ 2 ^ b * V := by
  classical
  obtain ⟨enc, dec, hok⟩ := h
  have hsub : Finset.univ.filter (fun x => compat x y) ⊆
      Finset.univ.biUnion
        (fun w : Fin (2 ^ b) => Finset.univ.filter (fun x => dist (dec w y) x ≤ r)) := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    simp only [Finset.mem_biUnion, Finset.mem_univ, Finset.mem_filter, true_and]
    exact ⟨enc x, hok x y hx⟩
  calc _ ≤ _ := Finset.card_le_card hsub
    _ ≤ ∑ w : Fin (2 ^ b), (Finset.univ.filter (fun x => dist (dec w y) x ≤ r)).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _w : Fin (2 ^ b), V := Finset.sum_le_sum (fun w _ => hV (dec w y))
    _ = 2 ^ b * V := by simp

/-- Нулевая ошибка: допустимая раскраска — это правильная раскраска
«графа путаницы», где два сообщения соединены, если Z с какими-то знаниями
не может исключить ни одно из них (Witsenhausen, 1976). -/
theorem goodColoring_zero_iff [Nonempty X] (hdist : ∀ a b, dist a b = 0 ↔ a = b)
    {b : ℕ} (c : X → Fin (2 ^ b)) :
    GoodColoring compat dist 0 c ↔
      ∀ x x', x ≠ x' → (∃ y, compat x y ∧ compat x' y) → c x ≠ c x' := by
  constructor
  · rintro hc x x' hne ⟨y, hx, hx'⟩ hcc
    obtain ⟨center, hcen⟩ := hc y (c x)
    have h1 := (hdist _ _).1 (Nat.le_zero.1 (hcen x hx rfl))
    have h2 := (hdist _ _).1 (Nat.le_zero.1 (hcen x' hx' hcc.symm))
    exact hne (h1.symm.trans h2)
  · intro hproper y w
    classical
    by_cases hex : ∃ x, compat x y ∧ c x = w
    · obtain ⟨x, hx, hcx⟩ := hex
      refine ⟨x, fun x' hx' hcx' => ?_⟩
      by_cases heq : x = x'
      · subst heq; exact le_of_eq ((hdist _ _).2 rfl)
      · exact absurd (hcx.trans hcx'.symm) (hproper x x' heq ⟨y, hx, hx'⟩)
    · simp only [not_exists, not_and] at hex
      obtain ⟨x0⟩ := ‹Nonempty X›
      exact ⟨x0, fun x hx hcx => absurd hcx (hex x hx)⟩

/-- **Точная теорема о сарафанном радио.** Пусть сеть доставляет в Z к моменту τ
ровно `C · (τ − d)` бит (с учётом кодирования это достижимо: теорема
Ahlswede–Cai–Li–Yeung о потоке информации). Тогда Z восстанавливает сообщение
с ошибкой ≤ r раньше прямой доставки ⇔ задача решается `C · (T − 1 − d)` битами. -/
theorem rumour_exact (C d T : ℕ) (hT : 0 < T) :
    (∃ τ < T, Solvable compat dist r (C * (τ - d))) ↔
      Solvable compat dist r (C * (T - 1 - d)) := by
  constructor
  · rintro ⟨τ, hτ, h⟩
    exact h.mono compat dist r (Nat.mul_le_mul_left C (by omega))
  · intro h
    exact ⟨T - 1, by omega, h⟩

end SideInfo

/-! ### Пример: цена того, что сеть не знает, что известно Z

Пять сообщений по кругу: 0, 1, 2, 3, 4. Z всегда знает, что сообщение —
одно из двух соседних: `y` или `y + 1` (по модулю 5).
* Если A знает, какие два варианта у Z, хватает 1 бита: «первый или второй».
* Если не знает — 1 бита не хватает: граф путаницы — цикл из 5 вершин,
  его нельзя раскрасить в 2 цвета. Нужно 2 бита. -/

namespace Pentagon

def compat (x y : Fin 5) : Prop := x = y ∨ x = y + 1

instance : ∀ x y, Decidable (compat x y) := fun x y => by unfold compat; infer_instance

def dist (a b : Fin 5) : ℕ := if a = b then 0 else 1

theorem dist_zero (a b : Fin 5) : dist a b = 0 ↔ a = b := by
  unfold dist; split_ifs with h <;> simp [h]

/-- A знает, что известно Z: хватает 1 бита. -/
theorem informed_one_bit : SideInfo.SolvableInformed compat dist 0 1 := by
  refine ⟨fun x y => if x = y then 0 else 1, fun w y => if w = 0 then y else y + 1, ?_⟩
  decide

/-- A не знает, что известно Z: 1 бита не хватает. -/
theorem blind_one_bit_fails : ¬ SideInfo.Solvable compat dist 0 1 := by
  rw [SideInfo.solvable_iff]
  rintro ⟨c, hc⟩
  rw [SideInfo.goodColoring_zero_iff compat dist dist_zero] at hc
  have hne : ∀ i : Fin 5, i ≠ i + 1 := by decide
  have e : ∀ i : Fin 5, (c i).val ≠ (c (i + 1)).val := fun i h =>
    hc i (i + 1) (hne i) ⟨i, Or.inl rfl, Or.inr rfl⟩ (Fin.ext h)
  have e0 := e 0; have e1 := e 1; have e2 := e 2; have e3 := e 3; have e4 := e 4
  have b0 := (c 0).isLt; have b1 := (c 1).isLt; have b2 := (c 2).isLt
  have b3 := (c 3).isLt; have b4 := (c 4).isLt
  simp only [show (0 : Fin 5) + 1 = 1 from rfl, show (1 : Fin 5) + 1 = 2 from rfl,
    show (2 : Fin 5) + 1 = 3 from rfl, show (3 : Fin 5) + 1 = 4 from rfl,
    show (4 : Fin 5) + 1 = 0 from rfl, pow_one] at e0 e1 e2 e3 e4 b0 b1 b2 b3 b4
  omega

/-- 2 бит хватает. -/
theorem blind_two_bits : SideInfo.Solvable compat dist 0 2 := by
  rw [SideInfo.solvable_iff]
  refine ⟨![0, 1, 0, 1, 2], ?_⟩
  rw [SideInfo.goodColoring_zero_iff compat dist dist_zero]
  decide

/-- Итог: незнание источника о знаниях Z стоит здесь целый лишний бит. -/
theorem price_of_blindness :
    SideInfo.SolvableInformed compat dist 0 1 ∧ ¬ SideInfo.Solvable compat dist 0 1 :=
  ⟨informed_one_bit, blind_one_bit_fails⟩

end Pentagon

end Sarafan
