/-
  Rubidium.SmallOdd — P/N の小さい奇数 m = 1, 3, 5 の全局面分類。
-/
import Rubidium.K7

namespace Rubidium

/-- m = 1 では、空の山または直前手が 1 の局面がちょうど P 局面。-/
theorem K10_m1_all_states (r p : Nat) : IsP 1 r p ↔ r = 0 ∨ p = 1 := by
  by_cases hr : r = 0
  · subst r
    constructor
    · intro _; exact Or.inl rfl
    · intro _; exact isP_zero 1 p
  · have hrpos : 1 ≤ r := by omega
    by_cases hp : p = 1
    · subst p
      constructor
      · intro _; exact Or.inr rfl
      · intro _
        rw [isP_iff]
        intro k hk1 hkm hkr hkp
        omega
    · constructor
      · intro hP
        have hprev : IsP 1 (r - 1) 1 := by
          rw [isP_iff]
          intro k hk1 hkm hkr hkp
          omega
        have hnot := (isP_iff 1 r p).mp hP 1 (by omega) (by omega) (by omega) (by omega)
        exact False.elim (hnot hprev)
      · intro h
        rcases h with hzero | hone
        · exact False.elim (hr hzero)
        · exact False.elim (hp hone)

/-- m = 3 では、2^12 以下の周期状態表が全ての十分大きい局面を分類する。-/
theorem K10_m3_finite_states :
    ∃ N T, 0 < T ∧ N < 2 ^ 12 ∧ T ≤ 2 ^ 12 ∧
      ∀ r p, N ≤ r →
        (isPb 3 r p = true ↔ isPb 3 (N + (r - N) % T) p = true) := by
  obtain ⟨N, T, hT, hN, hTbound, hperiod⟩ := K7' 3
  have hN' : N < 2 ^ 12 := by simpa using hN
  have hT' : T ≤ 2 ^ 12 := by simpa using hTbound
  refine ⟨N, T, hT, hN', hT', ?_⟩
  intro r p hr
  rw [isPb_iff, isPb_iff]
  exact isP_mod_period 3 N T hT hperiod r p hr

/-- m = 5 では、2^30 以下の周期状態表が全ての十分大きい局面を分類する。-/
theorem K10_m5_finite_states :
    ∃ N T, 0 < T ∧ N < 2 ^ 30 ∧ T ≤ 2 ^ 30 ∧
      ∀ r p, N ≤ r →
        (isPb 5 r p = true ↔ isPb 5 (N + (r - N) % T) p = true) := by
  obtain ⟨N, T, hT, hN, hTbound, hperiod⟩ := K7' 5
  have hN' : N < 2 ^ 30 := by simpa using hN
  have hT' : T ≤ 2 ^ 30 := by simpa using hTbound
  refine ⟨N, T, hT, hN', hT', ?_⟩
  intro r p hr
  rw [isPb_iff, isPb_iff]
  exact isP_mod_period 5 N T hT hperiod r p hr

end Rubidium
