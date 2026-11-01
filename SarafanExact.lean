import SarafanCheapTalk

/-!
# Уточнения после разбора: точные и вычислимые версии

1. **Точная теорема 1** (`rumour_exact_informed`). Если A знает, что известно Z,
   сеть выигрывает ⇔ число покрытия N(ε) ≤ 2^(C·(T − 1 − d)). Прежняя оценка
   `|M| ≤ N(ε)·V(ε)` — следствие (`card_le_coverNum_mul`).
2. **Цена незнания, двусторонняя оценка.** Если A не знает, что известно Z:
   * снизу: `max_y |M_y| ≤ 2^b` (`blind_lower`);
   * сверху: если каждое сообщение путается не более чем с Δ другими,
     хватает b бит при Δ + 1 ≤ 2^b (`blind_upper`, через жадную раскраску `greedy`).
   Пятиугольник: снизу 1 бит, сверху 2 — и нужно ровно 2 (верхняя граница достигается).
3. **Обратная задача** (`inverse_capacity`). Если Z восстановил сообщение к моменту τ,
   то C·(τ − d) ≥ log₂N(ε): по наблюдению оценивается пропускная способность.
4. **Утечки кругами** (`leak_clusters_le`). Посвящённые разбиты на независимые круги
   с вероятностями p_j; риск за T дней ≤ T·Σ p_j. Внутри круга утечки могут быть
   как угодно связаны: важен не состав, а число кругов (`leak_clusters_uniform`).
-/

namespace Sarafan.Exact

open Finset

/-! ## 1. Число покрытия и точная теорема 1 -/

section Covering

variable {M : Type*} [Fintype M] (dist : M → M → ℕ) (r : ℕ)

/-- n шаров радиуса r покрывают все сообщения. -/
def Covers (n : ℕ) : Prop := ∃ c : Fin n → M, ∀ x, ∃ i, dist (c i) x ≤ r

/-- Восстановление по b битам с ошибкой ≤ r ⇔ покрытие 2^b шарами. -/
theorem decodable_iff_covers (b : ℕ) :
    (∃ (enc : M → Fin (2 ^ b)) (dec : Fin (2 ^ b) → M), ∀ x, dist (dec (enc x)) x ≤ r) ↔
      Covers dist r (2 ^ b) := by
  constructor
  · rintro ⟨enc, dec, hok⟩
    exact ⟨dec, fun x => ⟨enc x, hok x⟩⟩
  · rintro ⟨c, hc⟩
    choose idx hidx using hc
    exact ⟨idx, c, hidx⟩

/-- Больше шаров — не хуже. -/
theorem Covers.mono [Nonempty M] {n n' : ℕ} (h : Covers dist r n) (hn : n ≤ n') :
    Covers dist r n' := by
  obtain ⟨c, hc⟩ := h
  obtain ⟨x0⟩ := ‹Nonempty M›
  have hpos : 0 < n := by
    obtain ⟨i, _⟩ := hc x0
    exact Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt
  refine ⟨fun i => if h : i.val < n then c ⟨i.val, h⟩ else c ⟨0, hpos⟩, fun x => ?_⟩
  obtain ⟨i, hi⟩ := hc x
  refine ⟨Fin.castLE hn i, ?_⟩
  have hlt : (Fin.castLE hn i).val < n := i.isLt
  simp only [dif_pos hlt]
  exact hi

/-- Тривиальное покрытие: каждое сообщение — свой центр. -/
theorem covers_card (hrefl : ∀ x, dist x x ≤ r) : Covers dist r (Fintype.card M) :=
  ⟨fun i => (Fintype.equivFin M).symm i,
    fun x => ⟨Fintype.equivFin M x, by simpa using hrefl x⟩⟩

open Classical in
/-- Число покрытия N(ε): наименьшее число шаров ошибки, покрывающих все сообщения. -/
noncomputable def coverNum (hrefl : ∀ x, dist x x ≤ r) : ℕ :=
  Nat.find ⟨Fintype.card M, covers_card dist r hrefl⟩

theorem covers_iff_coverNum_le [Nonempty M] (hrefl : ∀ x, dist x x ≤ r) (n : ℕ) :
    Covers dist r n ↔ coverNum dist r hrefl ≤ n := by
  classical
  constructor
  · intro h
    exact Nat.find_min' _ h
  · intro h
    exact (Nat.find_spec ⟨Fintype.card M, covers_card dist r hrefl⟩).mono dist r h

/-- Прежняя нижняя оценка: |M| ≤ n·V для любого покрытия n шарами. -/
theorem card_le_of_covers {n V : ℕ} (h : Covers dist r n)
    (hV : ∀ c, (univ.filter (fun x => dist c x ≤ r)).card ≤ V) :
    Fintype.card M ≤ n * V := by
  classical
  obtain ⟨c, hc⟩ := h
  have hsub : (univ : Finset M) ⊆
      univ.biUnion (fun i : Fin n => univ.filter (fun x => dist (c i) x ≤ r)) := by
    intro x _
    simp only [mem_biUnion, mem_univ, mem_filter, true_and]
    exact hc x
  calc Fintype.card M = (univ : Finset M).card := card_univ.symm
    _ ≤ _ := card_le_card hsub
    _ ≤ ∑ i : Fin n, (univ.filter (fun x => dist (c i) x ≤ r)).card := card_biUnion_le
    _ ≤ ∑ _i : Fin n, V := sum_le_sum (fun i _ => hV (c i))
    _ = n * V := by simp

theorem card_le_coverNum_mul [Nonempty M] (hrefl : ∀ x, dist x x ≤ r) {V : ℕ}
    (hV : ∀ c, (univ.filter (fun x => dist c x ≤ r)).card ≤ V) :
    Fintype.card M ≤ coverNum dist r hrefl * V :=
  card_le_of_covers dist r ((covers_iff_coverNum_le dist r hrefl _).2 le_rfl) hV

/-- **Точная теорема 1.** Сеть доставляет к моменту τ ровно C·(τ − d) бит.
Z восстанавливает сообщение с ошибкой ≤ r раньше прямой доставки ⇔
N(ε) ≤ 2^(C·(T − 1 − d)), то есть ⌈log₂N(ε)⌉ ≤ C·(T − 1 − d). -/
theorem rumour_exact_informed [Nonempty M] (hrefl : ∀ x, dist x x ≤ r)
    (C d T : ℕ) (hT : 0 < T) :
    (∃ τ < T, ∃ (enc : M → Fin (2 ^ (C * (τ - d)))) (dec : Fin (2 ^ (C * (τ - d))) → M),
        ∀ x, dist (dec (enc x)) x ≤ r) ↔
      coverNum dist r hrefl ≤ 2 ^ (C * (T - 1 - d)) := by
  rw [← covers_iff_coverNum_le dist r hrefl]
  constructor
  · rintro ⟨τ, hτ, h⟩
    have hc := (decodable_iff_covers dist r _).1 h
    exact hc.mono dist r (Nat.pow_le_pow_right (by norm_num)
      (Nat.mul_le_mul_left C (by omega)))
  · intro h
    exact ⟨T - 1, by omega, (decodable_iff_covers dist r _).2 h⟩

/-- **Обратная задача.** Если Z восстановил сообщение к моменту τ, получив не больше
C·(τ − d) бит, то N(ε) ≤ 2^(C·(τ − d)), то есть C ≥ log₂N(ε) / (τ − d). -/
theorem inverse_capacity [Nonempty M] (hrefl : ∀ x, dist x x ≤ r) {b C d τ : ℕ}
    (hcap : b ≤ C * (τ - d))
    (hdec : ∃ (enc : M → Fin (2 ^ b)) (dec : Fin (2 ^ b) → M), ∀ x, dist (dec (enc x)) x ≤ r) :
    coverNum dist r hrefl ≤ 2 ^ (C * (τ - d)) := by
  have hc := (decodable_iff_covers dist r b).1 hdec
  exact (covers_iff_coverNum_le dist r hrefl _).1
    (hc.mono dist r (Nat.pow_le_pow_right (by norm_num) hcap))

end Covering

/-! ## 2. Жадная раскраска и цена незнания -/

/-- **Жадная раскраска.** Если каждое сообщение путается не более чем с Δ другими,
сообщения можно раскрасить в Δ + 1 цвет так, что путающиеся получают разные цвета. -/
theorem greedy {X : Type*} [Fintype X] [DecidableEq X] (conf : X → X → Prop)
    [DecidableRel conf] (hsymm : ∀ x x', conf x x' → conf x' x) (Δ : ℕ)
    (hdeg : ∀ x, (univ.filter (fun x' => x' ≠ x ∧ conf x x')).card ≤ Δ) :
    ∃ c : X → Fin (Δ + 1), ∀ x x', x ≠ x' → conf x x' → c x ≠ c x' := by
  suffices H : ∀ S : Finset X, ∃ c : X → Fin (Δ + 1),
      ∀ x ∈ S, ∀ x' ∈ S, x ≠ x' → conf x x' → c x ≠ c x' by
    obtain ⟨c, hc⟩ := H univ
    exact ⟨c, fun x x' => hc x (mem_univ _) x' (mem_univ _)⟩
  intro S
  induction S using Finset.induction_on with
  | empty => exact ⟨fun _ => 0, by simp⟩
  | insert a S haS ih =>
    obtain ⟨c, hc⟩ := ih
    set used := (S.filter (fun x' => conf a x')).image c
    have hused : used.card < (univ : Finset (Fin (Δ + 1))).card := by
      calc used.card ≤ (S.filter (fun x' => conf a x')).card := card_image_le
        _ ≤ (univ.filter (fun x' => x' ≠ a ∧ conf a x')).card := by
            apply card_le_card
            intro x' hx'
            simp only [mem_filter, mem_univ, true_and] at hx' ⊢
            exact ⟨fun h => haS (h ▸ hx'.1), hx'.2⟩
        _ ≤ Δ := hdeg a
        _ < Δ + 1 := Nat.lt_succ_self Δ
        _ = _ := by simp
    obtain ⟨col, -, hcol⟩ := exists_mem_notMem_of_card_lt_card hused
    have hfree : ∀ x' ∈ S, conf a x' → col ≠ c x' := by
      intro x' hx' hconf heq
      apply hcol
      rw [heq]
      exact mem_image_of_mem c (mem_filter.2 ⟨hx', hconf⟩)
    refine ⟨Function.update c a col, ?_⟩
    intro x hx x' hx' hne hconf
    rcases mem_insert.1 hx with rfl | hxS <;> rcases mem_insert.1 hx' with rfl | hx'S
    · exact absurd rfl hne
    · rw [Function.update_self, Function.update_of_ne (Ne.symm hne)]
      exact hfree x' hx'S hconf
    · rw [Function.update_of_ne hne, Function.update_self]
      exact Ne.symm (hfree x hxS (hsymm _ _ hconf))
    · have hxa : x ≠ x' := hne
      have h1 : x ≠ a := fun h => haS (h ▸ hxS)
      have h2 : x' ≠ a := fun h => haS (h ▸ hx'S)
      rw [Function.update_of_ne h1, Function.update_of_ne h2]
      exact hc x hxS x' hx'S hxa hconf

section Blind

variable {X Y : Type*} [Fintype X] (compat : X → Y → Prop) [∀ x y, Decidable (compat x y)]
  (dist : X → X → ℕ)

/-- **Нижняя граница цены незнания.** Если b бит хватает при нулевой ошибке,
то при любом состоянии знаний y вариантов не больше 2^b. -/
theorem blind_lower (hdist : ∀ a b, dist a b = 0 ↔ a = b) {b : ℕ}
    (h : SideInfo.Solvable compat dist 0 b) (y : Y) :
    (univ.filter (fun x => compat x y)).card ≤ 2 ^ b := by
  classical
  have := SideInfo.card_bound compat dist 0 (V := 1) h (fun c => by
    apply card_le_one.2
    intro a ha a' ha'
    simp only [mem_filter, mem_univ, true_and, Nat.le_zero] at ha ha'
    exact ((hdist _ _).1 ha).symm.trans ((hdist _ _).1 ha')) y
  simpa using this

/-- **Верхняя граница цены незнания.** Если каждое сообщение путается
(возможно при одних и тех же знаниях Z) не более чем с Δ другими и Δ + 1 ≤ 2^b,
то b бит хватает, даже когда A не знает, что известно Z. -/
theorem blind_upper [Nonempty X] [DecidableEq X]
    [∀ x x', Decidable (∃ y, compat x y ∧ compat x' y)]
    (hdist : ∀ a b, dist a b = 0 ↔ a = b) (Δ b : ℕ)
    (hdeg : ∀ x, (univ.filter (fun x' => x' ≠ x ∧ ∃ y, compat x y ∧ compat x' y)).card ≤ Δ)
    (hb : Δ + 1 ≤ 2 ^ b) : SideInfo.Solvable compat dist 0 b := by
  obtain ⟨c, hc⟩ := greedy (fun x x' => ∃ y, compat x y ∧ compat x' y)
    (fun x x' ⟨y, h1, h2⟩ => ⟨y, h2, h1⟩) Δ hdeg
  rw [SideInfo.solvable_iff]
  refine ⟨fun x => Fin.castLE hb (c x), ?_⟩
  rw [SideInfo.goodColoring_zero_iff compat dist hdist]
  intro x x' hne hconf heq
  exact hc x x' hne hconf (Fin.castLE_injective hb heq)

end Blind

/-- Пятиугольник: в каждом состоянии знаний 2 варианта (нижняя граница — 1 бит),
каждое сообщение путается с двумя соседями (верхняя — ⌈log₂ 3⌉ = 2 бита),
и нужно ровно 2: верхняя граница достигается. -/
theorem pentagon_bounds :
    (∀ y : Fin 5, (univ.filter (fun x => Pentagon.compat x y)).card = 2) ∧
    (∀ x : Fin 5, (univ.filter (fun x' => x' ≠ x ∧
        ∃ y, Pentagon.compat x y ∧ Pentagon.compat x' y)).card ≤ 2) ∧
    SideInfo.Solvable Pentagon.compat Pentagon.dist 0 2 ∧
    ¬ SideInfo.Solvable Pentagon.compat Pentagon.dist 0 1 := by
  refine ⟨by decide, by decide, ?_, Pentagon.blind_one_bit_fails⟩
  exact blind_upper Pentagon.compat Pentagon.dist Pentagon.dist_zero 2 2 (by decide)
    (by norm_num)

/-! ## 3. Утечки кругами посвящённых -/

section Clusters

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {ι : Type*}

/-- Неравенство Вейерштрасса: ∏(1 − pᵢ) ≥ 1 − Σ pᵢ при pᵢ ∈ [0, 1]. -/
theorem weierstrass (s : Finset ι) (p : ι → K) (h0 : ∀ i ∈ s, 0 ≤ p i)
    (h1 : ∀ i ∈ s, p i ≤ 1) : 1 - ∑ i ∈ s, p i ≤ ∏ i ∈ s, (1 - p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s has ih =>
    rw [sum_insert has, prod_insert has]
    have ha0 := h0 a (mem_insert_self a s)
    have ha1 := h1 a (mem_insert_self a s)
    have ih' := ih (fun i hi => h0 i (mem_insert_of_mem hi))
      (fun i hi => h1 i (mem_insert_of_mem hi))
    have hs0 : 0 ≤ ∑ i ∈ s, p i := sum_nonneg (fun i hi => h0 i (mem_insert_of_mem hi))
    nlinarith [mul_le_mul_of_nonneg_left ih' (sub_nonneg.2 ha1), mul_nonneg ha0 hs0]

/-- Вероятность, что за T дней не проговорится ни один из независимых кругов. -/
def noLeakClusters (s : Finset ι) (p : ι → K) (T : ℕ) : K := (∏ j ∈ s, (1 - p j)) ^ T

/-- **Риск утечки кругами.** Круги независимы, круг j проговаривается за день
с вероятностью p_j (внутри круга утечки связаны как угодно).
Риск за T дней ≤ T·Σ p_j. -/
theorem leak_clusters_le (s : Finset ι) (p : ι → K) (h0 : ∀ i ∈ s, 0 ≤ p i)
    (h1 : ∀ i ∈ s, p i ≤ 1) (T : ℕ) :
    1 - noLeakClusters s p T ≤ T * ∑ j ∈ s, p j := by
  unfold noLeakClusters
  set P := ∏ j ∈ s, (1 - p j)
  set S := ∑ j ∈ s, p j
  have hP0 : 0 ≤ P := prod_nonneg (fun i hi => sub_nonneg.2 (h1 i hi))
  have hPS : 1 - S ≤ P := weierstrass s p h0 h1
  have hS0 : 0 ≤ S := sum_nonneg h0
  by_cases hS : S ≤ 1
  · have hb := one_add_mul_le_pow (a := -S) (by linarith) T
    have hmono := pow_le_pow_left₀ (by linarith : (0 : K) ≤ 1 - S) hPS T
    rw [← sub_eq_add_neg] at hb
    linarith
  · rcases Nat.eq_zero_or_pos T with rfl | hT
    · simp
    · have hT1 : (1 : K) ≤ T := by exact_mod_cast hT
      have hPT : 0 ≤ P ^ T := pow_nonneg hP0 T
      nlinarith

/-- Если каждый из g кругов проговаривается с вероятностью не больше q,
риск за T дней ≤ g·T·q, сколько бы людей ни было в кругах. -/
theorem leak_clusters_uniform (s : Finset ι) (p : ι → K) {q : K}
    (h0 : ∀ i ∈ s, 0 ≤ p i) (h1 : ∀ i ∈ s, p i ≤ 1) (hq : ∀ i ∈ s, p i ≤ q) (T : ℕ) :
    1 - noLeakClusters s p T ≤ s.card * T * q := by
  have h := leak_clusters_le s p h0 h1 T
  have hsum : ∑ j ∈ s, p j ≤ s.card * q := by
    have := sum_le_card_nsmul s p q hq
    simpa [nsmul_eq_mul] using this
  have hT0 : (0 : K) ≤ T := Nat.cast_nonneg T
  nlinarith [mul_le_mul_of_nonneg_left hsum hT0]

end Clusters

end Sarafan.Exact
