import Rubidium.Game
import Rubidium.K4Even
import Rubidium.K4Full

/-
  SG-011：K4 で決まる開始局面 (n, 0)。
  - m = 1 では、n ≥ 1 のすべての開始局面が先手必勝（P 局面は n = 0 だけ）。
  - ev2(m+1) = true（m が偶数、または m が奇数で v2(m+1) が偶数）のとき、
    (n, 0) が P 局面 ⇔ (m+1) | n。
-/
namespace Rubidium

/-- m = 1 で直前に 1 個取られていれば、合法手がないので P 局面。-/
theorem isP_one_one (r : Nat) : IsP 1 r 1 := by
  rw [isP_iff]
  intro k hk1 hkm _ hkp
  omega

/-- m = 1 の開始局面：(n, 0) が P 局面 ⇔ n = 0。-/
theorem start_m_one (n : Nat) : IsP 1 n 0 ↔ n = 0 := by
  constructor
  · intro h
    by_cases hn : n = 0
    · exact hn
    · rw [isP_iff] at h
      exact absurd (isP_one_one (n - 1)) (h 1 (by omega) (by omega) (by omega) (by omega))
  · intro h
    subst h
    exact isP_zero 1 0

/-- ev2(m+1) = true の開始局面：(n, 0) が P 局面 ⇔ (m+1) | n。
    m が偶数なら K4_even、m が奇数なら K4_odd による。-/
theorem start_ev2 (m : Nat) (hev : ev2 (m + 1) = true) (n : Nat) :
    IsP m n 0 ↔ n % (m + 1) = 0 := by
  by_cases hm : m % 2 = 0
  · exact K4_even m hm n
  · exact K4_odd m (by omega) hev n

/-- m が偶数なら ev2(m+1) = true。-/
theorem ev2_succ_of_even (m : Nat) (hm : m % 2 = 0) : ev2 (m + 1) = true :=
  ev2_odd (m + 1) (by omega)

/-- SG-011：m = 1、または ev2(m+1) = true の場合の MainTheorem。-/
theorem MainTheorem_K4_cases (m n : Nat) :
    (m = 1 → (IsP m n 0 ↔ n = 0)) ∧
    (ev2 (m + 1) = true → (IsP m n 0 ↔ n % (m + 1) = 0)) := by
  refine ⟨?_, fun hev => start_ev2 m hev n⟩
  intro h
  subst h
  exact start_m_one n

end Rubidium
