/-
  Rubidium.EvenM — SG-004: General even-m P-position structure and 2-adic valuation rules

  This module formalizes:
  1. General 2-adic valuation (`v2`) arithmetic rules (multiplication, powers of 2,
     divisibility, odd part, addition, and subtraction).
  2. Complete characterization of `IsP m r p` for ALL states `(r, p)` when `m` is even:
     - `r % (m + 1) = 0` => `IsP m r p` for all `p`.
     - `r % (m + 1) ≠ 0` and `p ≠ r % (m + 1)` => `¬ IsP m r p`.
     - `r % (m + 1) ≠ 0` and `p = r % (m + 1)` => `IsP m r p ↔ evenDiagSteps m (r / (m + 1)) (r % (m + 1)) % 2 = 0`,
       together with the 2-adic reduction `evenDiagSteps m j d = v2 d + evenDiagSteps m j (d / 2 ^ v2 d)`.
  3. Explicit winning-move existence for all N-positions when `m` is even.
  4. General `(r, p)` row/off-diagonal structure for all `m` with `v2(m + 1)` even.
-/
import Rubidium.K4Full

namespace Rubidium

/-! ### 1. General 2-adic valuation (`v2`) rules -/

theorem v2_zero : v2 0 = 0 := by
  rw [v2]; simp

theorem v2_one : v2 1 = 0 :=
  v2_odd 1 (by omega)

theorem v2_two_mul (n : Nat) (hn : 1 ≤ n) : v2 (2 * n) = v2 n + 1 := by
  rw [v2_even (2 * n) (by omega) (by omega)]
  have h : 2 * n / 2 = n := by omega
  rw [h]

theorem v2_mul_two (n : Nat) (hn : 1 ≤ n) : v2 (n * 2) = v2 n + 1 := by
  rw [Nat.mul_comm]
  exact v2_two_mul n hn

theorem v2_pow_two : ∀ k : Nat, v2 (2 ^ k) = k
  | 0 => v2_one
  | k + 1 => by
    rw [Nat.pow_succ, v2_mul_two (2 ^ k) (Nat.one_le_two_pow), v2_pow_two k]

theorem v2_pow_two_mul (k n : Nat) (hn : 1 ≤ n) : v2 (2 ^ k * n) = k + v2 n := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hpow : 1 ≤ 2 ^ k * n := Nat.mul_pos (Nat.two_pow_pos k) hn
    rw [Nat.pow_succ, Nat.mul_right_comm, v2_mul_two (2 ^ k * n) hpow, ih]
    omega

theorem v2_mul (a b : Nat) (ha : 1 ≤ a) (hb : 1 ≤ b) : v2 (a * b) = v2 a + v2 b := by
  induction a using Nat.strongRecOn with
  | _ a ih =>
    by_cases hao : a % 2 = 1
    · rw [v2_odd a hao, Nat.zero_add]
      clear ih
      induction b using Nat.strongRecOn with
      | _ b ihb =>
        by_cases hbo : b % 2 = 1
        · have habo : (a * b) % 2 = 1 := by
            rw [Nat.mul_mod, hao, hbo]
          rw [v2_odd b hbo, v2_odd (a * b) habo]
        · have hbe : b % 2 = 0 := by omega
          have habe : (a * b) % 2 = 0 := by
            rw [Nat.mul_mod, hbe]; simp
          have hab1 : 1 ≤ a * b := Nat.mul_pos ha hb
          have hdiv : a * b / 2 = a * (b / 2) :=
            Nat.mul_div_assoc a (Nat.dvd_of_mod_eq_zero hbe)
          rw [v2_even b (by omega) hbe, v2_even (a * b) (by omega) habe, hdiv]
          rw [ihb (b / 2) (by omega) (by omega)]
    · have hae : a % 2 = 0 := by omega
      have habe : (a * b) % 2 = 0 := by
        rw [Nat.mul_mod, hae]; simp
      have hab1 : 1 ≤ a * b := Nat.mul_pos ha hb
      have hdiv : a * b / 2 = (a / 2) * b := by
        rw [Nat.mul_comm a b, Nat.mul_div_assoc b (Nat.dvd_of_mod_eq_zero hae), Nat.mul_comm]
      rw [v2_even a (by omega) hae, v2_even (a * b) (by omega) habe, hdiv]
      rw [ih (a / 2) (by omega) (by omega)]
      omega

/-- Every positive `n` is divisible by `2 ^ v2 n`, and the quotient is odd. -/
theorem pow_two_v2_decomp : ∀ n : Nat, 1 ≤ n →
    2 ^ v2 n * (n / 2 ^ v2 n) = n ∧ (n / 2 ^ v2 n) % 2 = 1 := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro hn
    by_cases ho : n % 2 = 1
    · rw [v2_odd n ho]
      simp [ho]
    · have he : n % 2 = 0 := by omega
      rw [v2_even n (by omega) he]
      obtain ⟨hdecomp, hodd⟩ := ih (n / 2) (by omega) (by omega)
      have hdiv : n / 2 ^ (v2 (n / 2) + 1) = (n / 2) / 2 ^ v2 (n / 2) := by
        rw [Nat.pow_succ, Nat.mul_comm, ← Nat.div_div_eq_div_mul]
      rw [hdiv]
      refine ⟨?_, hodd⟩
      rw [Nat.pow_succ, Nat.mul_right_comm, hdecomp]
      omega

theorem pow_two_v2_dvd (n : Nat) (hn : 1 ≤ n) : 2 ^ v2 n ∣ n :=
  ⟨n / 2 ^ v2 n, (pow_two_v2_decomp n hn).1.symm⟩

theorem odd_div_pow_two_v2 (n : Nat) (hn : 1 ≤ n) : (n / 2 ^ v2 n) % 2 = 1 :=
  (pow_two_v2_decomp n hn).2

theorem pos_div_pow_two_v2 (n : Nat) (hn : 1 ≤ n) : 1 ≤ n / 2 ^ v2 n := by
  have hodd := odd_div_pow_two_v2 n hn
  apply Nat.pos_of_ne_zero
  intro h0
  rw [h0] at hodd
  omega

theorem v2_add_gt (x y : Nat) (hx : 1 ≤ x) (hy : 1 ≤ y) (hlt : v2 y < v2 x) :
    v2 (x + y) = v2 y := by
  rw [Nat.add_comm]
  exact v2_add y x hy hx hlt

theorem v2_add_eq (x y : Nat) (hx : 1 ≤ x) (hy : 1 ≤ y) (heq : v2 x = v2 y) :
    v2 x + 1 ≤ v2 (x + y) := by
  obtain ⟨hdx, hox⟩ := pow_two_v2_decomp x hx
  obtain ⟨hdy, hoy⟩ := pow_two_v2_decomp y hy
  rw [← heq] at hdy hoy
  have ha_pos : 1 ≤ x / 2 ^ v2 x := pos_div_pow_two_v2 x hx
  have hab_even : (x / 2 ^ v2 x + y / 2 ^ v2 x) % 2 = 0 := by omega
  have hab_pos : 1 ≤ x / 2 ^ v2 x + y / 2 ^ v2 x := Nat.le_trans ha_pos (Nat.le_add_right _ _)
  have hsum : x + y = 2 ^ v2 x * (x / 2 ^ v2 x + y / 2 ^ v2 x) := by
    rw [Nat.mul_add, hdx, hdy]
  rw [hsum, v2_pow_two_mul (v2 x) (x / 2 ^ v2 x + y / 2 ^ v2 x) hab_pos,
      v2_even (x / 2 ^ v2 x + y / 2 ^ v2 x) (by omega) hab_even]
  omega

theorem v2_sub_lt (x y : Nat) (hy : 1 ≤ y) (hxy : y < x) (hlt : v2 y < v2 x) :
    v2 (x - y) = v2 y := by
  have hsplit : x = (x - y) + y := by omega
  by_cases hlt1 : v2 (x - y) < v2 y
  · have := v2_add (x - y) y (by omega) hy hlt1
    rw [← hsplit] at this; omega
  · by_cases hlt2 : v2 y < v2 (x - y)
    · have := v2_add_gt (x - y) y (by omega) hy hlt2
      rw [← hsplit] at this; omega
    · omega

theorem v2_sub_gt (x y : Nat) (hy : 1 ≤ y) (hxy : y < x) (hlt : v2 x < v2 y) :
    v2 (x - y) = v2 x := by
  have hsplit : x = (x - y) + y := by omega
  by_cases hlt1 : v2 (x - y) < v2 y
  · have := v2_add (x - y) y (by omega) hy hlt1
    rw [← hsplit] at this; exact this.symm
  · by_cases hlt2 : v2 y < v2 (x - y)
    · have := v2_add_gt (x - y) y (by omega) hy hlt2
      rw [← hsplit] at this; omega
    · have heq : v2 (x - y) = v2 y := by omega
      have := v2_add_eq (x - y) y (by omega) hy heq
      rw [← hsplit] at this; omega

/-! ### 2. Complete `(r, p)` characterization for even `m` -/

/-- Exact transition for `(j*(m+1) + d, d)` when `m` is even and `d` is even (`1 ≤ d ≤ m`).
    The unique candidate P-move is `k = d / 2`. -/
theorem even_diag_even (m j d : Nat) (hm : m % 2 = 0) (hd1 : 1 ≤ d) (hdm : d ≤ m) (hde : d % 2 = 0) :
    IsP m (j * (m + 1) + d) d ↔ ¬ IsP m (j * (m + 1) + d / 2) (d / 2) := by
  rw [isP_iff]
  constructor
  · intro hP hP2
    apply hP (d / 2) (by omega) (by omega) (by omega) (by omega)
    rw [show j * (m + 1) + d - d / 2 = j * (m + 1) + d / 2 by omega]
    exact hP2
  · intro hN k hk1 hkm hkr hkd hPk
    by_cases hlt : k < d
    · rw [show j * (m + 1) + d - k = j * (m + 1) + (d - k) by omega] at hPk
      by_cases heq : k = d - k
      · have hk2 : k = d / 2 := by omega
        rw [hk2, show d - d / 2 = d / 2 by omega] at hPk
        exact hN hPk
      · exact not_isP_of_row m (j * (m + 1)) (d - k) k (row_all m hm j) (by omega) (by omega) heq hPk
    · have hgt : d < k := by omega
      cases j with
      | zero => omega
      | succ j' =>
        rw [show (j' + 1) * (m + 1) + d - k = j' * (m + 1) + (m + 1 + d - k) by
          rw [Nat.succ_mul]; omega] at hPk
        exact not_isP_of_row m (j' * (m + 1)) (m + 1 + d - k) k (row_all m hm j')
          (by omega) (by omega) (by omega) hPk

/-- Base case for `(0*(m+1) + d, d)` when `d` is odd (`1 ≤ d ≤ m`). -/
theorem even_diag_odd_zero (m d : Nat) (hd1 : 1 ≤ d) (hdm : d ≤ m) (hdo : d % 2 = 1) :
    IsP m (0 * (m + 1) + d) d := by
  rw [Nat.zero_mul, Nat.zero_add, K3 m d d hd1 hdm]
  exact ⟨rfl, ev2_odd d hdo⟩

/-- Exact transition for `((j+1)*(m+1) + d, d)` when `m` is even and `d` is odd (`1 ≤ d ≤ m`).
    The unique candidate P-move is `k = (m + 1 + d) / 2`. -/
theorem even_diag_odd_succ (m j d : Nat) (hm : m % 2 = 0) (hd1 : 1 ≤ d) (hdm : d ≤ m) (hdo : d % 2 = 1) :
    IsP m ((j + 1) * (m + 1) + d) d ↔ ¬ IsP m (j * (m + 1) + (m + 1 + d) / 2) ((m + 1 + d) / 2) := by
  rw [isP_iff]
  constructor
  · intro hP hP2
    have hk_le_m : (m + 1 + d) / 2 ≤ m := by omega
    apply hP ((m + 1 + d) / 2) (by omega) hk_le_m
      (by rw [Nat.succ_mul]; omega) (by omega)
    rw [show (j + 1) * (m + 1) + d - (m + 1 + d) / 2 = j * (m + 1) + (m + 1 + d) / 2 by
      rw [Nat.succ_mul]; omega]
    exact hP2
  · intro hN k hk1 hkm hkr hkd hPk
    by_cases hlt : k < d
    · rw [show (j + 1) * (m + 1) + d - k = (j + 1) * (m + 1) + (d - k) by omega] at hPk
      exact not_isP_of_row m ((j + 1) * (m + 1)) (d - k) k (row_all m hm (j + 1))
        (by omega) (by omega) (by omega) hPk
    · have hgt : d < k := by omega
      rw [show (j + 1) * (m + 1) + d - k = j * (m + 1) + (m + 1 + d - k) by
        rw [Nat.succ_mul]; omega] at hPk
      by_cases heq : k = m + 1 + d - k
      · have hk2 : k = (m + 1 + d) / 2 := by omega
        rw [hk2, show m + 1 + d - (m + 1 + d) / 2 = (m + 1 + d) / 2 by omega] at hPk
        exact hN hPk
      · exact not_isP_of_row m (j * (m + 1)) (m + 1 + d - k) k (row_all m hm j)
          (by omega) (by omega) heq hPk

/-- Exact number of forced diagonal moves from `(j*(m+1) + d, d)` down to `(0, odd)`
    when `m` is even. Every even `d` halves `d`; every odd `d` with `j ≥ 1` maps
    `(j, d) ↦ (j - 1, (m + 1 + d) / 2)`. -/
def evenDiagSteps (m j d : Nat) : Nat :=
  if d = 0 then 0
  else if d % 2 = 0 then evenDiagSteps m j (d / 2) + 1
  else match j with
    | 0 => 0
    | j' + 1 => evenDiagSteps m j' ((m + 1 + d) / 2) + 1
termination_by (j, d)
decreasing_by
  · exact Prod.Lex.right j (by omega)
  · exact Prod.Lex.left _ _ (by omega)

theorem evenDiagSteps_even (m j d : Nat) (hd : 1 ≤ d) (hde : d % 2 = 0) :
    evenDiagSteps m j d = evenDiagSteps m j (d / 2) + 1 := by
  rw [evenDiagSteps.eq_def]
  have hd0 : d ≠ 0 := by omega
  simp [hd0, hde]

theorem evenDiagSteps_odd_zero (m d : Nat) (hdo : d % 2 = 1) :
    evenDiagSteps m 0 d = 0 := by
  rw [evenDiagSteps.eq_def]
  have hd0 : d ≠ 0 := by omega
  have hne : d % 2 ≠ 0 := by omega
  simp [hd0, hne]

theorem evenDiagSteps_odd_succ (m j d : Nat) (hdo : d % 2 = 1) :
    evenDiagSteps m (j + 1) d = evenDiagSteps m j ((m + 1 + d) / 2) + 1 := by
  rw [evenDiagSteps.eq_def]
  have hd0 : d ≠ 0 := by omega
  have hne : d % 2 ≠ 0 := by omega
  simp [hd0, hne]

/-- 2-adic reduction of `evenDiagSteps`: stripping `v2 d` factors of 2 adds `v2 d` steps. -/
theorem evenDiagSteps_v2 (m j : Nat) : ∀ d : Nat, 1 ≤ d →
    evenDiagSteps m j d = v2 d + evenDiagSteps m j (d / 2 ^ v2 d) := by
  intro d
  induction d using Nat.strongRecOn with
  | _ d ih =>
    intro hd
    by_cases hdo : d % 2 = 1
    · rw [v2_odd d hdo]; simp
    · have hde : d % 2 = 0 := by omega
      rw [evenDiagSteps_even m j d hd hde, v2_even d (by omega) hde]
      have hdiv : d / 2 ^ (v2 (d / 2) + 1) = (d / 2) / 2 ^ v2 (d / 2) := by
        rw [Nat.pow_succ, Nat.mul_comm, ← Nat.div_div_eq_div_mul]
      rw [hdiv, ih (d / 2) (by omega) (by omega)]
      omega

/-- On the first block (`j = 0`), `evenDiagSteps m 0 d = v2 d`. -/
theorem evenDiagSteps_zero_eq_v2 (m d : Nat) (hd : 1 ≤ d) :
    evenDiagSteps m 0 d = v2 d := by
  rw [evenDiagSteps_v2 m 0 d hd, evenDiagSteps_odd_zero m (d / 2 ^ v2 d) (odd_div_pow_two_v2 d hd),
      Nat.add_zero]

/-- Exact characterization of diagonal states `(j*(m+1) + d, d)` for even `m`. -/
theorem even_diag_iff (m : Nat) (hm : m % 2 = 0) :
    ∀ j d, 1 ≤ d → d ≤ m →
      (IsP m (j * (m + 1) + d) d ↔ evenDiagSteps m j d % 2 = 0) := by
  intro j
  induction j with
  | zero =>
    intro d hd1 hdm
    rw [Nat.zero_mul, Nat.zero_add, K3 m d d hd1 hdm, ev2_iff_v2 d hd1,
        evenDiagSteps_zero_eq_v2 m d hd1]
    simp
  | succ j ih =>
    intro d
    induction d using Nat.strongRecOn with
    | _ d ihd =>
      intro hd1 hdm
      by_cases hde : d % 2 = 0
      · rw [even_diag_even m (j + 1) d hm hd1 hdm hde,
            evenDiagSteps_even m (j + 1) d hd1 hde,
            ihd (d / 2) (by omega) (by omega) (by omega)]
        omega
      · have hdo : d % 2 = 1 := by omega
        rw [even_diag_odd_succ m j d hm hd1 hdm hdo,
            evenDiagSteps_odd_succ m j d hdo,
            ih ((m + 1 + d) / 2) (by omega) (by omega)]
        omega

/-- 2-adic reduction for diagonal states of even `m`. -/
theorem even_diag_v2_reduction (m j d : Nat) (hm : m % 2 = 0) (hd1 : 1 ≤ d) (hdm : d ≤ m) :
    IsP m (j * (m + 1) + d) d ↔
      (v2 d % 2 = 0 ↔ IsP m (j * (m + 1) + d / 2 ^ v2 d) (d / 2 ^ v2 d)) := by
  have hpos : 1 ≤ d / 2 ^ v2 d := pos_div_pow_two_v2 d hd1
  have hle : d / 2 ^ v2 d ≤ m := Nat.le_trans (Nat.div_le_self d _) hdm
  rw [even_diag_iff m hm j d hd1 hdm,
      even_diag_iff m hm j (d / 2 ^ v2 d) hpos hle,
      evenDiagSteps_v2 m j d hd1]
  omega

/-- Main SG-004 theorem: complete characterization of `IsP m r p` for ALL even `m`,
    and ALL states `(r, p)`. -/
theorem even_isP_iff (m : Nat) (hm : m % 2 = 0) (r p : Nat) :
    IsP m r p ↔
      r % (m + 1) = 0 ∨
      (p = r % (m + 1) ∧ evenDiagSteps m (r / (m + 1)) (r % (m + 1)) % 2 = 0) := by
  have hdiv : r = (r / (m + 1)) * (m + 1) + r % (m + 1) := by
    have := Nat.div_add_mod r (m + 1)
    rw [Nat.mul_comm] at this; omega
  have hmod_lt : r % (m + 1) < m + 1 := Nat.mod_lt r (by omega)
  by_cases h0 : r % (m + 1) = 0
  · constructor
    · intro _; exact Or.inl h0
    · intro _
      have hr : r = (r / (m + 1)) * (m + 1) := by omega
      rw [hr]; exact row_all m hm (r / (m + 1)) p
  · by_cases hp : p = r % (m + 1)
    · have hdiag := even_diag_iff m hm (r / (m + 1)) (r % (m + 1)) (by omega) (by omega)
      rw [← hdiv] at hdiag
      rw [hp, hdiag]
      simp [h0]
    · constructor
      · intro hP
        have hnot := not_isP_of_row m ((r / (m + 1)) * (m + 1)) (r % (m + 1)) p
          (row_all m hm (r / (m + 1))) (by omega) (by omega) hp
        rw [← hdiv] at hnot
        exact absurd hP hnot
      · intro h
        rcases h with h' | ⟨h', _⟩
        · exact absurd h' h0
        · exact absurd h' hp

/-- Explicit winning move for any N-position `(r, p)` when `m` is even. -/
theorem even_winning_move (m : Nat) (hm : m % 2 = 0) (r p : Nat) (hN : ¬ IsP m r p) :
    ∃ k, 1 ≤ k ∧ k ≤ m ∧ k ≤ r ∧ k ≠ p ∧ IsP m (r - k) k := by
  have hdiv : r = (r / (m + 1)) * (m + 1) + r % (m + 1) := by
    have := Nat.div_add_mod r (m + 1)
    rw [Nat.mul_comm] at this; omega
  have hmod_lt : r % (m + 1) < m + 1 := Nat.mod_lt r (by omega)
  have h0 : r % (m + 1) ≠ 0 := by
    intro h0; apply hN
    have hr : r = (r / (m + 1)) * (m + 1) := by omega
    rw [hr]; exact row_all m hm (r / (m + 1)) p
  by_cases hp : p = r % (m + 1)
  · by_cases hde : (r % (m + 1)) % 2 = 0
    · refine ⟨(r % (m + 1)) / 2, by omega, by omega, by omega, by omega, ?_⟩
      have hP2 : IsP m ((r / (m + 1)) * (m + 1) + (r % (m + 1)) / 2) ((r % (m + 1)) / 2) := by
        apply Classical.byContradiction
        intro hN2
        have hP := (even_diag_even m (r / (m + 1)) (r % (m + 1)) hm (by omega) (by omega) hde).mpr hN2
        rw [← hdiv, ← hp] at hP
        exact hN hP
      rw [show r - (r % (m + 1)) / 2 = (r / (m + 1)) * (m + 1) + (r % (m + 1)) / 2 by omega]
      exact hP2
    · have hdo : (r % (m + 1)) % 2 = 1 := by omega
      cases hj : r / (m + 1) with
      | zero =>
        exfalso
        have hP := even_diag_odd_zero m (r % (m + 1)) (by omega) (by omega) hdo
        have hr : 0 * (m + 1) + r % (m + 1) = r := by rw [← hj]; exact hdiv.symm
        rw [hr, ← hp] at hP
        exact hN hP
      | succ j' =>
        have hmul : (j' + 1) * (m + 1) = j' * (m + 1) + (m + 1) := Nat.succ_mul j' (m + 1)
        have hr_eq : r = (j' + 1) * (m + 1) + r % (m + 1) := by rw [← hj]; exact hdiv
        have hk_le_r : (m + 1 + r % (m + 1)) / 2 ≤ r := by omega
        refine ⟨(m + 1 + r % (m + 1)) / 2, by omega, by omega, hk_le_r, by omega, ?_⟩
        have hP2 : IsP m (j' * (m + 1) + (m + 1 + r % (m + 1)) / 2) ((m + 1 + r % (m + 1)) / 2) := by
          apply Classical.byContradiction
          intro hN2
          have hP := (even_diag_odd_succ m j' (r % (m + 1)) hm (by omega) (by omega) hdo).mpr hN2
          rw [← hr_eq, ← hp] at hP
          exact hN hP
        have hsub : r - (m + 1 + r % (m + 1)) / 2 = j' * (m + 1) + (m + 1 + r % (m + 1)) / 2 := by
          omega
        rw [hsub]
        exact hP2
  · refine ⟨r % (m + 1), by omega, by omega, by omega, fun e => hp e.symm, ?_⟩
    rw [show r - r % (m + 1) = (r / (m + 1)) * (m + 1) by omega]
    exact row_all m hm (r / (m + 1)) (r % (m + 1))

/-! ### 3. General `(r, p)` row and off-diagonal structure for all `v2(m + 1)` even -/

/-- When `v2(m + 1)` is even (`ev2 (m + 1) = true`), every multiple of `m + 1` is an all-P row. -/
theorem even_v2_row_all (m : Nat) (hev : ev2 (m + 1) = true) (j p : Nat) :
    IsP m (j * (m + 1)) p := by
  by_cases hmo : m % 2 = 1
  · exact (row_all_odd m hmo hev j).1 p
  · exact row_all m (by omega) j p

/-- When `v2(m + 1)` is even, every off-diagonal state (`r % (m + 1) ≠ 0`, `p ≠ r % (m + 1)`) is N. -/
theorem even_v2_off_diag_not_isP (m : Nat) (hev : ev2 (m + 1) = true) (r p : Nat)
    (h0 : r % (m + 1) ≠ 0) (hp : p ≠ r % (m + 1)) : ¬ IsP m r p := by
  have hdiv : r = (r / (m + 1)) * (m + 1) + r % (m + 1) := by
    have := Nat.div_add_mod r (m + 1)
    rw [Nat.mul_comm] at this; omega
  have hmod_lt : r % (m + 1) < m + 1 := Nat.mod_lt r (by omega)
  have hnot := not_isP_of_row m ((r / (m + 1)) * (m + 1)) (r % (m + 1)) p
    (even_v2_row_all m hev (r / (m + 1))) (by omega) (by omega) hp
  rw [← hdiv] at hnot
  exact hnot

/-- When `m` is odd and `v2(m + 1)` is even, diagonal states with `v2(r % (m + 1)) ≤ v2((m + 1) / 2)`
    are P iff `v2(r % (m + 1))` is even. -/
theorem even_v2_odd_m_diag_iff (m : Nat) (hmo : m % 2 = 1) (hev : ev2 (m + 1) = true) (r : Nat)
    (h0 : r % (m + 1) ≠ 0) (hv : v2 (r % (m + 1)) ≤ v2 ((m + 1) / 2)) :
    IsP m r (r % (m + 1)) ↔ v2 (r % (m + 1)) % 2 = 0 := by
  have hdiv : r = (r / (m + 1)) * (m + 1) + r % (m + 1) := by
    have := Nat.div_add_mod r (m + 1)
    rw [Nat.mul_comm] at this; omega
  have hmod_lt : r % (m + 1) < m + 1 := Nat.mod_lt r (by omega)
  have hblk := (row_all_odd m hmo hev (r / (m + 1))).2 (r % (m + 1)) (by omega) (by omega) hv
  rw [← hdiv] at hblk
  exact hblk

end Rubidium
