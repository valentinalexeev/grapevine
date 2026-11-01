import SarafanExact

/-!
# Постепенное раскрытие авторитетным источником

Источник A раскрывает сообщение по частям. К моменту τ официальные заявления
исключили часть вариантов: остаётся множество `off τ`, убывающее со временем.
Z соединяет официальную часть и слухи.

1. **Обобщённая теорема 1′** (`decide_iff_covers`): Z может решить в момент τ ⇔
   оставшиеся после официальных заявлений варианты покрываются 2^(C·(τ − d))
   шарами ошибки. Официальной части хватает одной ⇔ хватает одного шара.
2. **Монотонность** (`decide_later`, `more_disclosure_helps`): решение, доступное
   в момент τ, доступно и позже; более полное раскрытие не мешает.
   Частичное раскрытие сужает задачу, которую решают слухи.
3. **Порядок раскрытия** (`order_lower`, `order_decision_first`): если официальный
   канал отвечает на один вопрос «да/нет» за период, а решение Z зависит от
   K классов, то нужно не меньше log₂K периодов при любом порядке, и порядок
   «сначала главное» укладывается ровно в ⌈log₂K⌉. Пример (`detail_first_slow`,
   `decision_first_fast`): «сначала детали» — 3 периода, «сначала главное» — 1.
4. **Молчание как сигнал** (`silence_reveals`): если правило «говорить только
   о хорошем» известно, по набору сказанного восстанавливаются все темы,
   включая те, о которых промолчали.
-/

namespace Sarafan.Disclosure

open Finset

/-! ## 1–2. Официальная часть и слухи -/

section Official

variable {M : Type*} (dist : M → M → ℕ) (r : ℕ)

/-- Варианты, удовлетворяющие `S`, покрываются n шарами радиуса r. -/
def CoversOn (S : M → Prop) (n : ℕ) : Prop :=
  ∃ c : Fin n → M, ∀ x, S x → ∃ i, dist (c i) x ≤ r

/-- По b битам слухов Z восстанавливает любое сообщение из `S` с ошибкой ≤ r. -/
def DecodableOn (S : M → Prop) (b : ℕ) : Prop :=
  ∃ (enc : M → Fin (2 ^ b)) (dec : Fin (2 ^ b) → M), ∀ x, S x → dist (dec (enc x)) x ≤ r

/-- **Обобщённая теорема 1′.** Решение по официальной части `S` и b битам слухов
возможно ⇔ `S` покрывается 2^b шарами. -/
theorem decide_iff_covers (S : M → Prop) (b : ℕ) :
    DecodableOn dist r S b ↔ CoversOn dist r S (2 ^ b) := by
  classical
  constructor
  · rintro ⟨enc, dec, hok⟩
    exact ⟨dec, fun x hx => ⟨enc x, hok x hx⟩⟩
  · rintro ⟨c, hc⟩
    refine ⟨fun x => if h : S x then Classical.choose (hc x h) else ⟨0, by positivity⟩,
      c, fun x hx => ?_⟩
    simp only [hx, ↓reduceDIte]
    exact Classical.choose_spec (hc x hx)

/-- Официальной части хватает без слухов ⇔ оставшиеся варианты лежат в одном шаре. -/
theorem official_alone_iff (S : M → Prop) :
    DecodableOn dist r S 0 ↔ CoversOn dist r S 1 := by
  simpa using decide_iff_covers dist r S 0

/-- Более полное раскрытие (меньше вариантов) не мешает. -/
theorem more_disclosure_helps {S S' : M → Prop} (h : ∀ x, S' x → S x) {b : ℕ}
    (hd : DecodableOn dist r S b) : DecodableOn dist r S' b := by
  obtain ⟨enc, dec, hok⟩ := hd
  exact ⟨enc, dec, fun x hx => hok x (h x hx)⟩

/-- Больше бит слухов — не хуже. -/
theorem DecodableOn.mono_bits {S : M → Prop} {b b' : ℕ} (hd : DecodableOn dist r S b)
    (hb : b ≤ b') : DecodableOn dist r S b' := by
  obtain ⟨enc, dec, hok⟩ := hd
  have hle : 2 ^ b ≤ 2 ^ b' := Nat.pow_le_pow_right (by norm_num) hb
  refine ⟨fun x => Fin.castLE hle (enc x),
    fun w => if hw : w.val < 2 ^ b then dec ⟨w.val, hw⟩ else dec ⟨0, by positivity⟩, ?_⟩
  intro x hx
  have hlt : (Fin.castLE hle (enc x)).val < 2 ^ b := (enc x).isLt
  beta_reduce
  split
  · exact hok x hx
  · next h => exact absurd hlt h

/-- Если официальное раскрытие только уточняется со временем (`off` убывает),
то решение, доступное в момент τ, доступно и в любой более поздний момент. -/
theorem decide_later {off : ℕ → M → Prop}
    (hanti : ∀ t t', t ≤ t' → ∀ x, off t' x → off t x) {C d τ τ' : ℕ} (hτ : τ ≤ τ')
    (h : DecodableOn dist r (off τ) (C * (τ - d))) :
    DecodableOn dist r (off τ') (C * (τ' - d)) :=
  (more_disclosure_helps dist r (hanti τ τ' hτ) h).mono_bits dist r
    (Nat.mul_le_mul_left C (by omega))

/-- **Сравнение политик раскрытия.** Если политика `off'` к каждому моменту
раскрывает не меньше, чем `off`, то при `off'` Z может решить не позже. -/
theorem fuller_policy_not_later {off off' : ℕ → M → Prop}
    (hfull : ∀ t x, off' t x → off t x) {C d τ : ℕ}
    (h : DecodableOn dist r (off τ) (C * (τ - d))) :
    DecodableOn dist r (off' τ) (C * (τ - d)) :=
  more_disclosure_helps dist r (hfull τ) h

end Official

/-! ## 3. Порядок раскрытия: «сначала главное» -/

section Order

variable {M K : Type*} (D : M → K)

/-- Ответы на первые t официальных вопросов «да/нет» определяют класс решения D. -/
def Determines (q : ℕ → M → Bool) (t : ℕ) : Prop :=
  ∀ x x', (∀ i < t, q i x = q i x') → D x = D x'

/-- **Нижняя граница.** При любом порядке вопросов, если за t периодов решение
определено, то классов решения не больше 2^t. -/
theorem order_lower [Fintype M] [DecidableEq K] (q : ℕ → M → Bool) (t : ℕ)
    (h : Determines D q t) : (univ.image D).card ≤ 2 ^ t := by
  classical
  let ans : M → (Fin t → Bool) := fun x i => q i x
  let f : K → (Fin t → Bool) := fun k =>
    if hk : ∃ x, D x = k then ans (Classical.choose hk) else fun _ => false
  have hinj : Set.InjOn f (univ.image D : Set K) := by
    intro k1 hk1 k2 hk2 hf
    simp only [coe_image, coe_univ, Set.image_univ, Set.mem_range] at hk1 hk2
    have e1 := Classical.choose_spec hk1
    have e2 := Classical.choose_spec hk2
    simp only [f, hk1, hk2, ↓reduceDIte] at hf
    rw [← e1, ← e2]
    apply h
    intro i hi
    exact congrFun hf ⟨i, hi⟩
  calc (univ.image D).card ≤ (univ : Finset (Fin t → Bool)).card :=
        card_le_card_of_injOn f (fun _ _ => mem_univ _) hinj
    _ = 2 ^ t := by simp

/-- **Порядок «сначала главное» оптимален.** Если классов решения K ≤ 2^b,
существуют b вопросов, ответы на которые определяют решение. -/
theorem order_decision_first [Fintype K] {b : ℕ} (hK : Fintype.card K ≤ 2 ^ b) :
    ∃ q : ℕ → M → Bool, Determines D q b := by
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le (α := K) (β := Fin (2 ^ b))
    (by simpa using hK)
  refine ⟨fun i x => (e (D x)).val.testBit i, fun x x' h => ?_⟩
  apply e.injective
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < b
  · exact h i hi
  · have hpow : 2 ^ b ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (e (D x)).isLt hpow),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le (e (D x')).isLt hpow)]

/-- Пример: 8 вариантов, решение зависит от старшего бита («затронут ли мой отдел»).
Порядок «сначала детали» — младшие биты первыми. -/
def detailFirst (i : ℕ) (x : Fin 8) : Bool := x.val.testBit i

/-- Порядок «сначала главное» — старший бит первым. -/
def decisionFirst (i : ℕ) (x : Fin 8) : Bool := x.val.testBit (2 - i)

def decision (x : Fin 8) : Bool := decide (4 ≤ x.val)

/-- «Сначала детали»: двух официальных заявлений мало… -/
theorem detail_first_slow : ¬ Determines decision detailFirst 2 := by
  unfold Determines; decide

/-- …нужны все три. -/
theorem detail_first_three : Determines decision detailFirst 3 := by
  unfold Determines; decide

/-- «Сначала главное»: хватает одного заявления. -/
theorem decision_first_fast : Determines decision decisionFirst 1 := by
  unfold Determines; decide

end Order

/-! ## 4. Молчание как сигнал -/

/-- k тем, каждая «хорошая» или «плохая». Правило источника: сообщать только
о хороших; о плохих молчать. -/
def announced {k : ℕ} (x : Fin k → Bool) : Fin k → Option Bool :=
  fun i => if x i then some true else none

/-- **Молчание раскрывает.** Если правило известно, по сказанному однозначно
восстанавливаются все темы, включая те, о которых промолчали. -/
theorem silence_reveals (k : ℕ) : Function.Injective (announced (k := k)) := by
  intro x x' h
  funext i
  have hi := congrFun h i
  unfold announced at hi
  cases hx : x i <;> cases hx' : x' i <;> simp_all

end Sarafan.Disclosure
