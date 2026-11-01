import SarafanDisclosure

/-!
# Следствие: преждевременные действия

Пока официального ответа нет, участники Z действуют на основе того, что знают
к этому моменту (теоремы 1′ и 4 говорят, что именно они знают). Часть таких
действий окажется лишней: при полной информации их бы не совершили.

1. **Лишние действия — только у тех, кому вопрос не закрыт**
   (`regret_only_unresolved`). Полное закрытие главного вопроса убирает
   и лишние, и упущенные действия (`full_resolution`).
2. **Частичное раскрытие может увеличить число лишних действий**
   (`partial_can_increase_regret`): 8 отделов, 3 затронуты, порог 1/2.
   Без раскрытия лишних действий 0, после «отделы 6 и 7 не затронуты» — 3.
   При пороге 3/10 то же раскрытие уменьшает их с 5 до 3 (`partial_can_decrease_regret`).
3. **Ценность информации** (`best_policy`, `value_of_information`, `refinement_helps`):
   для получателя с верными ожиданиями более подробное раскрытие не увеличивает
   ожидаемые потери — уменьшается сумма лишних и упущенных действий.
4. **Объявленная дата** (`shorter_wait_fewer_actions`): если сотрудник ждёт
   при ожидаемом сроке ответа w, он ждёт и при любом меньшем сроке.
-/

namespace Sarafan.Actions

open Finset

/-! ## 1–2. Отделы, пороги и лишние действия -/

section Departments

variable {n : ℕ}

/-- Руководитель отдела i действует (например, ищет работу), если вероятность
«мой отдел затронут» не меньше порога θ = a/b (b > 0).
`pool` — отделы, по которым решение ещё не объявлено; известно, сколько среди
них затронутых, поэтому вероятность для отдела из `pool` равна
|affected ∩ pool| / |pool|, и условие k/m ≥ a/b записано как a·m ≤ b·k.
Остальные знают свой статус точно (вероятность 1 или 0). -/
def acts (affected pool : Finset (Fin n)) (a b : ℕ) (i : Fin n) : Prop :=
  if i ∈ pool then a * pool.card ≤ b * (affected ∩ pool).card
  else if i ∈ affected then a ≤ b else a = 0

instance (affected pool : Finset (Fin n)) (a b : ℕ) (i : Fin n) :
    Decidable (acts affected pool a b i) := by
  unfold acts; infer_instance

/-- Лишние действия: действует, хотя отдел не затронут. -/
def regret (affected pool : Finset (Fin n)) (a b : ℕ) : ℕ :=
  (univ.filter (fun i => acts affected pool a b i ∧ i ∉ affected)).card

/-- Упущенные действия: не действует, хотя отдел затронут. -/
def missed (affected pool : Finset (Fin n)) (a b : ℕ) : ℕ :=
  (univ.filter (fun i => ¬ acts affected pool a b i ∧ i ∈ affected)).card

/-- **Лишние действия — только у тех, кому вопрос не закрыт** (порог θ = a/b > 0). -/
theorem regret_only_unresolved (affected pool : Finset (Fin n)) {a b : ℕ} (ha : 0 < a) :
    regret affected pool a b ≤ (pool.filter (fun i => i ∉ affected)).card := by
  apply card_le_card
  intro i hi
  simp only [mem_filter, mem_univ, true_and] at hi ⊢
  obtain ⟨hact, hna⟩ := hi
  refine ⟨?_, hna⟩
  by_contra hp
  unfold acts at hact
  rw [if_neg hp, if_neg hna] at hact
  omega

/-- **Полное закрытие главного вопроса** убирает и лишние, и упущенные действия
(порог 0 < θ ≤ 1, то есть 0 < a ≤ b). -/
theorem full_resolution (affected : Finset (Fin n)) {a b : ℕ} (ha : 0 < a) (hab : a ≤ b) :
    regret affected ∅ a b = 0 ∧ missed affected ∅ a b = 0 := by
  constructor
  · have := regret_only_unresolved affected ∅ (b := b) ha
    simpa using this
  · unfold missed
    rw [card_eq_zero, filter_eq_empty_iff]
    rintro i - ⟨hna, hin⟩
    apply hna
    unfold acts
    rw [if_neg (Finset.notMem_empty i), if_pos hin]
    exact hab

/-- 8 отделов, затронуты 0, 1, 2. -/
def A3 : Finset (Fin 8) := {0, 1, 2}

/-- Частичное раскрытие: «отделы 6 и 7 не затронуты». -/
def partialPool : Finset (Fin 8) := univ \ {6, 7}

/-- **Частичное раскрытие может увеличить число лишних действий.**
Порог 1/2: без раскрытия (вероятность 3/8) не действует никто; после
исключения двух отделов вероятность у остальных 3/6 = 1/2, и действуют все шесть,
из них трое — лишние. -/
theorem partial_can_increase_regret :
    regret A3 univ 1 2 = 0 ∧ regret A3 partialPool 1 2 = 3 := by
  decide

/-- При пороге 3/10 то же раскрытие уменьшает лишние действия с 5 до 3,
а полное раскрытие — до 0. -/
theorem partial_can_decrease_regret :
    regret A3 univ 3 10 = 5 ∧ regret A3 partialPool 3 10 = 3 ∧ regret A3 ∅ 3 10 = 0 := by
  decide

/-- При пороге 1/2 частичное раскрытие убирает упущенные действия (3 → 0):
лишних стало больше, упущенных меньше. -/
theorem partial_reduces_missed :
    missed A3 univ 1 2 = 3 ∧ missed A3 partialPool 1 2 = 0 := by
  decide

end Departments

/-! ## 3. Ценность информации -/

section Value

variable {X A C K : Type*} [Fintype X] [Fintype A] [Nonempty A] [Fintype C] [DecidableEq C]
  [AddCommMonoid K] [LinearOrder K] [IsOrderedAddMonoid K]

/-- Для любого правила действий ρ, зависящего от раскрытой информации `cell x`,
есть правило π с ожидаемыми потерями не больше (оптимальное в каждой клетке).
`f a x` — взвешенные по вероятности потери от действия a в состоянии x. -/
theorem best_policy (cell : X → C) (f : A → X → K) (ρ : C → A) :
    ∃ π : C → A, ∑ x, f (π (cell x)) x ≤ ∑ x, f (ρ (cell x)) x := by
  classical
  have hmin : ∀ c, ∃ a, ∀ a', ∑ x ∈ univ.filter (fun x => cell x = c), f a x ≤
      ∑ x ∈ univ.filter (fun x => cell x = c), f a' x := by
    intro c
    obtain ⟨a, -, ha⟩ := Finset.exists_min_image univ
      (fun a => ∑ x ∈ univ.filter (fun x => cell x = c), f a x) univ_nonempty
    exact ⟨a, fun a' => ha a' (mem_univ _)⟩
  choose π hπ using hmin
  refine ⟨π, ?_⟩
  have regroup : ∀ σ : C → A, ∑ x, f (σ (cell x)) x =
      ∑ c, ∑ x ∈ univ.filter (fun x => cell x = c), f (σ c) x := by
    intro σ
    rw [← Finset.sum_fiberwise univ cell (fun x => f (σ (cell x)) x)]
    apply sum_congr rfl
    intro c _
    apply sum_congr rfl
    intro x hx
    rw [(mem_filter.1 hx).2]
  rw [regroup π, regroup ρ]
  exact sum_le_sum (fun c _ => hπ c (ρ c))

/-- **Ценность информации.** С раскрытием можно действовать не хуже,
чем при любом фиксированном действии без раскрытия. -/
theorem value_of_information (cell : X → C) (f : A → X → K) (a₀ : A) :
    ∃ π : C → A, ∑ x, f (π (cell x)) x ≤ ∑ x, f a₀ x :=
  best_policy cell f (fun _ => a₀)

omit [Fintype C] [DecidableEq C] in
/-- **Более подробное раскрытие не хуже.** Если раскрытие `cell'` подробнее
(грубое получается из него функцией g), то оптимальное правило при `cell'`
не хуже любого правила при грубом раскрытии. -/
theorem refinement_helps {C' : Type*} [Fintype C'] [DecidableEq C']
    (cell' : X → C') (g : C' → C) (f : A → X → K) (π : C → A) :
    ∃ π' : C' → A, ∑ x, f (π' (cell' x)) x ≤ ∑ x, f (π (g (cell' x))) x :=
  best_policy cell' f (fun c' => π (g c'))

end Value

/-! ## 4. Объявленная дата -/

section Waiting

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Сотрудник с вероятностью p быть затронутым действует сейчас, если ожидаемая
цена лишнего действия (1 − p)·R меньше ожидаемой цены ожидания p·c·w,
где w — сколько, по его мнению, ждать официального ответа. -/
def actsNow (p R c w : K) : Prop := (1 - p) * R < p * c * w

/-- **Объявленная дата сокращает преждевременные действия.** Если сотрудник
ждёт при ожидаемом сроке w, он ждёт и при любом меньшем сроке w'. -/
theorem shorter_wait_fewer_actions {p R c w w' : K} (hp : 0 ≤ p) (hc : 0 ≤ c)
    (hw : w' ≤ w) (hwait : ¬ actsNow p R c w) : ¬ actsNow p R c w' := by
  unfold actsNow at *
  intro h
  apply hwait
  have := mul_le_mul_of_nonneg_left hw (mul_nonneg hp hc)
  linarith

end Waiting

end Sarafan.Actions
