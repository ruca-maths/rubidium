/-
  Rubidium.K7 — 定理 K7′（周期性）の形式化

  定理 K7′：すべての m で、全局面の勝敗表は r について周期的（前周期を許す）。
    N₀ < 2^(m(m+1))、0 < T ≤ 2^(m(m+1))、
    および r ≥ N₀ なら全 p について IsP m (r+T) p ↔ IsP m r p。
  ブロックの理論 H(j) を使わない証明。
  - `isP_big`：p > m の局面 (r, p) は (r, 0) と同じ（どの手 k ≤ m も p と 0 に等しくない）。
  - `window_step`：「窓」（行 r, …, r+m−1 の、p ≤ m の P/N）が行 s, … と同じなら、行 r+m も同じ。
    (r+m, p) からの手 k（1 ≤ k ≤ m）の行き先は (r + (m−k), k) で、窓の中にある。
  - `window_all`：窓が同じなら、それ以降のすべての行が同じ（t についての帰納法）。
  - 窓を長さ m(m+1) の Bool の列 `win` にし、2 進の符号 `enc` で 2^{m(m+1)} 未満の自然数にする。
  - `pigeon`：f i < B（i ≤ B）なら、i < j ≤ B で f i = f j となるものがある（B についての帰納法）。
-/
import Rubidium.Decide

namespace Rubidium

/-- p > m の局面は p = 0 の局面と同じ。-/
theorem isP_big (m r p : Nat) (hp : m < p) : IsP m r p ↔ IsP m r 0 := by
  rw [isP_iff, isP_iff m r 0]
  constructor
  · intro h k hk1 hkm hkr _ hP; exact h k hk1 hkm hkr (by omega) hP
  · intro h k hk1 hkm hkr _ hP; exact h k hk1 hkm hkr (by omega) hP

/-- 窓が同じなら、次の行も同じ。-/
theorem window_step (m r s : Nat) (hw : ∀ i, i < m → ∀ p, p ≤ m → (IsP m (r + i) p ↔ IsP m (s + i) p)) :
    ∀ p, IsP m (r + m) p ↔ IsP m (s + m) p := by
  intro p
  rw [isP_iff, isP_iff m (s + m) p]
  constructor
  · intro h k hk1 hkm _ hkp hP
    apply h k hk1 hkm (by omega) hkp
    rw [show r + m - k = r + (m - k) by omega]
    rw [show s + m - k = s + (m - k) by omega] at hP
    exact (hw (m - k) (by omega) k hkm).mpr hP
  · intro h k hk1 hkm _ hkp hP
    apply h k hk1 hkm (by omega) hkp
    rw [show s + m - k = s + (m - k) by omega]
    rw [show r + m - k = r + (m - k) by omega] at hP
    exact (hw (m - k) (by omega) k hkm).mp hP

/-- 窓が同じなら、それ以降のすべての行が同じ。-/
theorem window_all (m r s : Nat) (hw : ∀ i, i < m → ∀ p, p ≤ m → (IsP m (r + i) p ↔ IsP m (s + i) p)) :
    ∀ t p, IsP m (r + t) p ↔ IsP m (s + t) p := by
  -- まず、すべての t で窓 (r+t) と窓 (s+t) が同じ
  have hall : ∀ t, ∀ i, i < m → ∀ p, p ≤ m → (IsP m (r + t + i) p ↔ IsP m (s + t + i) p) := by
    intro t
    induction t with
    | zero => intro i hi p hp; rw [Nat.add_zero, Nat.add_zero]; exact hw i hi p hp
    | succ t ih =>
      intro i hi p hp
      by_cases hlast : i + 1 < m
      · rw [show r + (t + 1) + i = r + t + (i + 1) by omega, show s + (t + 1) + i = s + t + (i + 1) by omega]
        exact ih (i + 1) hlast p hp
      · have hi' : i = m - 1 := by omega
        rw [show r + (t + 1) + i = r + t + m by omega, show s + (t + 1) + i = s + t + m by omega]
        exact window_step m (r + t) (s + t) ih p
  intro t p
  by_cases hm : 0 < m
  · by_cases hp : p ≤ m
    · have := hall t 0 hm p hp
      rwa [Nat.add_zero, Nat.add_zero] at this
    · rw [isP_big m _ p (by omega), isP_big m (s + t) p (by omega)]
      have := hall t 0 hm 0 (by omega)
      rwa [Nat.add_zero, Nat.add_zero] at this
  · -- m = 0：手がないので、すべて P
    have hm0 : m = 0 := by omega
    subst hm0
    constructor <;> intro _ <;> rw [isP_iff] <;> intro k hk1 hkm <;> omega

/-! ### 鳩の巣原理 -/

theorem pigeon : ∀ B (f : Nat → Nat), (∀ i, i ≤ B → f i < B) → ∃ i j, i < j ∧ j ≤ B ∧ f i = f j := by
  intro B
  induction B with
  | zero => intro f hf; have := hf 0 (Nat.le_refl 0); omega
  | succ B ih =>
    intro f hf
    by_cases hex : ∃ i, i ≤ B ∧ f i = f (B + 1)
    · obtain ⟨i, hi, he⟩ := hex
      exact ⟨i, B + 1, by omega, Nat.le_refl _, he⟩
    · have hne : ∀ i, i ≤ B → f i ≠ f (B + 1) := fun i hi he => hex ⟨i, hi, he⟩
      let g : Nat → Nat := fun i => if f i = B then f (B + 1) else f i
      have hg : ∀ i, i ≤ B → g i < B := by
        intro i hi
        simp only [g]
        split
        · rename_i hfi
          have h1 := hf (B + 1) (Nat.le_refl _)
          have h2 := hne i hi
          omega
        · have := hf i (by omega); omega
      obtain ⟨i, j, hij, hjB, hgij⟩ := ih g hg
      refine ⟨i, j, hij, by omega, ?_⟩
      simp only [g] at hgij
      by_cases hi : f i = B <;> by_cases hj : f j = B
      · rw [hi, hj]
      · rw [ite_eq_left hi, ite_eq_right hj] at hgij; exact absurd hgij.symm (hne j (by omega))
      · rw [ite_eq_right hi, ite_eq_left hj] at hgij; exact absurd hgij (hne i (by omega))
      · rw [ite_eq_right hi, ite_eq_right hj] at hgij; exact hgij

/-! ### 窓の符号化 -/

/-- Bool の列の 2 進の符号。-/
def enc : List Bool → Nat
  | [] => 0
  | b :: l => 2 * enc l + (if b then 1 else 0)

theorem enc_lt : ∀ l : List Bool, enc l < 2 ^ l.length := by
  intro l
  induction l with
  | nil => simp [enc]
  | cons b l ih =>
    simp only [enc, List.length_cons, Nat.pow_succ]
    split <;> omega

theorem enc_inj : ∀ l₁ l₂ : List Bool, l₁.length = l₂.length → enc l₁ = enc l₂ → l₁ = l₂ := by
  intro l₁
  induction l₁ with
  | nil => intro l₂ h _; cases l₂ with | nil => rfl | cons _ _ => simp at h
  | cons b l ih =>
    intro l₂ h he
    cases l₂ with
    | nil => simp at h
    | cons c l' =>
      simp only [enc] at he
      simp only [List.length_cons] at h
      have hbc : b = c := by cases b <;> cases c <;> simp at he ⊢ <;> omega
      subst hbc
      have : enc l = enc l' := by cases b <;> simp at he <;> omega
      rw [ih l' (by omega) this]

/-- 行 r から始まる窓：q < m(m+1) について、(r + q/(m+1), q mod (m+1)) が P か。-/
def win (m r : Nat) : List Bool :=
  List.ofFn (fun q : Fin (m * (m + 1)) => isPb m (r + q.val / (m + 1)) (q.val % (m + 1)))

theorem win_length (m r : Nat) : (win m r).length = m * (m + 1) := by simp [win]

/-- 窓の列が同じなら、窓の局面の P/N が同じ。-/
theorem win_eq (m r s : Nat) (h : win m r = win m s) :
    ∀ i, i < m → ∀ p, p ≤ m → (IsP m (r + i) p ↔ IsP m (s + i) p) := by
  intro i hi p hp
  have hq : p + i * (m + 1) < m * (m + 1) := by
    have : (i + 1) * (m + 1) ≤ m * (m + 1) := Nat.mul_le_mul_right _ (by omega)
    rw [Nat.succ_mul] at this; omega
  have hdiv : (p + i * (m + 1)) / (m + 1) = i := by
    rw [Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt (by omega), Nat.zero_add]
  have hmod : (p + i * (m + 1)) % (m + 1) = p := by
    rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
  have hget := congrArg (fun l => l[p + i * (m + 1)]?) h
  simp only [win, List.getElem?_ofFn] at hget
  simp only [hq, dite_true, Option.some.injEq, hdiv, hmod] at hget
  rw [← isPb_iff, ← isPb_iff, hget]

/-- 定理 K7′：すべての m で、全局面の勝敗表は r について周期的（前周期を許す）。-/
theorem K7' (m : Nat) : ∃ N₀ T, 0 < T ∧ N₀ < 2 ^ (m * (m + 1)) ∧ T ≤ 2 ^ (m * (m + 1)) ∧
    ∀ r, N₀ ≤ r → ∀ p, (IsP m (r + T) p ↔ IsP m r p) := by
  let B := 2 ^ (m * (m + 1))
  obtain ⟨i, j, hij, hjB, he⟩ := pigeon B (fun r => enc (win m r))
    (fun r _ => by have := enc_lt (win m r); rwa [win_length] at this)
  have hw := win_eq m i j (enc_inj _ _ (by rw [win_length, win_length]) he)
  refine ⟨i, j - i, by omega, ?_, ?_, ?_⟩
  · omega
  · omega
  intro r hr p
  have := window_all m i j hw (r - i) p
  rw [show i + (r - i) = r by omega, show j + (r - i) = r + (j - i) by omega] at this
  exact this.symm

/-! ### 周期を使った有限状態の特徴づけ -/

/-- 周期 `T` が `N` 以降の全局面に成り立つなら、P/N は周期内の剰余で決まる。-/
theorem isP_quotient_period (m N T : Nat)
    (hperiod : ∀ r, N ≤ r → ∀ p, (IsP m (r + T) p ↔ IsP m r p)) :
    ∀ q s p, (IsP m (N + q * T + s) p ↔ IsP m (N + s) p) := by
  intro q
  induction q with
  | zero => intro s p; simp
  | succ q ih =>
    intro s p
    have hstep : (IsP m (N + (q + 1) * T + s) p ↔ IsP m (N + q * T + s) p) := by
      have heq : N + (q + 1) * T + s = N + q * T + s + T := by
        simp [Nat.add_mul]
        omega
      rw [heq]
      exact hperiod (N + q * T + s) (by omega) p
    exact hstep.trans (ih s p)

/-- `N` 以降の一般局面は、周期内の代表 `N + ((r-N) % T)` の有限表で分類できる。-/
theorem isP_mod_period (m N T : Nat) (hT : 0 < T)
    (hperiod : ∀ r, N ≤ r → ∀ p, (IsP m (r + T) p ↔ IsP m r p)) :
    ∀ r p, N ≤ r →
      (IsP m r p ↔ IsP m (N + (r - N) % T) p) := by
  intro r p hr
  let q := (r - N) / T
  let s := (r - N) % T
  have hdecomp : r = N + q * T + s := by
    dsimp [q, s]
    have hdivision : (r - N) % T + T * ((r - N) / T) = r - N := Nat.mod_add_div (r - N) T
    have hmul : T * ((r - N) / T) = ((r - N) / T) * T := Nat.mul_comm T ((r - N) / T)
    omega
  rw [hdecomp]
  have hslt : s < T := Nat.mod_lt _ hT
  have hsub : N + q * T + s - N = q * T + s := by omega
  rw [hsub]
  have hrem : (q * T + s) % T = s := by
    rw [Nat.mul_comm q T, Nat.add_mod, Nat.mul_mod_right, Nat.zero_add, Nat.mod_eq_of_lt hslt]
    exact Nat.mod_eq_of_lt hslt
  rw [hrem]
  exact isP_quotient_period m N T hperiod q s p

/-- 奇数 `m ≥ 7` では、周期内の有限個の行が全ての一般局面を分類する。
    周期と前周期には `K7'` の明示的な上界がある。-/
theorem K7_odd_general_states (m : Nat) (_hm : 7 ≤ m) (_hodd : m % 2 = 1) :
    ∃ N T, 0 < T ∧ N < 2 ^ (m * (m + 1)) ∧ T ≤ 2 ^ (m * (m + 1)) ∧
      ∀ r p, N ≤ r →
        (isPb m r p = true ↔ isPb m (N + (r - N) % T) p = true) := by
  obtain ⟨N, T, hT, hN, hTbound, hperiod⟩ := K7' m
  refine ⟨N, T, hT, hN, hTbound, ?_⟩
  intro r p hr
  rw [isPb_iff, isPb_iff]
  exact isP_mod_period m N T hT hperiod r p hr

end Rubidium
