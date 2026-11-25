# Restricted Stone Game — Research Status

<!-- Auto-generated deterministically by scripts/autonomous_ops.py sync-status. Do not edit manually. -->

## Overview

- **Main Theorem Target**: `MainTheorem` (OPEN)
- **Lean-Verified Theorems & Lemmas**: 70
- **Recorded Dead Ends**: 3
- **Stagnation Cycles**: 0 / 20

## Lean-Verified Results (`claims/proved/index.json`)

| Kind | Name | File | Line |
| :--- | :--- | :--- | ---: |
| `theorem` | `nat_all_iff` | `lean/Rubidium/Decide.lean` | 13 |
| `theorem` | `isPb_iff` | `lean/Rubidium/Decide.lean` | 33 |
| `theorem` | `isP_iff` | `lean/Rubidium/Game.lean` | 20 |
| `theorem` | `isP_zero` | `lean/Rubidium/Game.lean` | 25 |
| `theorem` | `ev2_odd` | `lean/Rubidium/Game.lean` | 39 |
| `theorem` | `ev2_even` | `lean/Rubidium/Game.lean` | 43 |
| `theorem` | `not_isP_near` | `lean/Rubidium/K10.lean` | 15 |
| `theorem` | `k10_E_h` | `lean/Rubidium/K10.lean` | 30 |
| `theorem` | `k10_O` | `lean/Rubidium/K10.lean` | 55 |
| `theorem` | `k10_rows` | `lean/Rubidium/K10.lean` | 114 |
| `theorem` | `K10a` | `lean/Rubidium/K10.lean` | 150 |
| `theorem` | `not_isP_move` | `lean/Rubidium/K13.lean` | 16 |
| `theorem` | `p_four` | `lean/Rubidium/K13.lean` | 24 |
| `theorem` | `p_two` | `lean/Rubidium/K13.lean` | 49 |
| `theorem` | `k13_step` | `lean/Rubidium/K13.lean` | 74 |
| `theorem` | `k13_rows` | `lean/Rubidium/K13.lean` | 135 |
| `theorem` | `mod4_of_v2_one` | `lean/Rubidium/K13.lean` | 161 |
| `theorem` | `mod16_of_v2_three` | `lean/Rubidium/K13.lean` | 170 |
| `theorem` | `K13` | `lean/Rubidium/K13.lean` | 179 |
| `theorem` | `ev2_iff` | `lean/Rubidium/K3.lean` | 17 |
| `theorem` | `K3` | `lean/Rubidium/K3.lean` | 29 |
| `theorem` | `not_isP_of_row` | `lean/Rubidium/K4Even.lean` | 16 |
| `theorem` | `row_all` | `lean/Rubidium/K4Even.lean` | 25 |
| `theorem` | `K4_even` | `lean/Rubidium/K4Even.lean` | 39 |
| `theorem` | `v2_odd` | `lean/Rubidium/K4Full.lean` | 26 |
| `theorem` | `v2_even` | `lean/Rubidium/K4Full.lean` | 29 |
| `theorem` | `even_of_v2_pos` | `lean/Rubidium/K4Full.lean` | 33 |
| `theorem` | `ev2_iff_v2` | `lean/Rubidium/K4Full.lean` | 40 |
| `theorem` | `v2_add` | `lean/Rubidium/K4Full.lean` | 53 |
| `theorem` | `row_next` | `lean/Rubidium/K4Full.lean` | 73 |
| `theorem` | `blk_step` | `lean/Rubidium/K4Full.lean` | 97 |
| `theorem` | `row_all_odd` | `lean/Rubidium/K4Full.lean` | 148 |
| `theorem` | `K4_odd` | `lean/Rubidium/K4Full.lean` | 171 |
| `theorem` | `K4` | `lean/Rubidium/K4Full.lean` | 189 |
| `theorem` | `not_isP_small` | `lean/Rubidium/K5.lean` | 14 |
| `theorem` | `isP_succ` | `lean/Rubidium/K5.lean` | 20 |
| `theorem` | `K4_first` | `lean/Rubidium/K5.lean` | 39 |
| `theorem` | `K5` | `lean/Rubidium/K5.lean` | 46 |
| `theorem` | `K5_before` | `lean/Rubidium/K5.lean` | 66 |
| `theorem` | `odd_of_rows` | `lean/Rubidium/K6.lean` | 22 |
| `theorem` | `row_long` | `lean/Rubidium/K6.lean` | 37 |
| `theorem` | `k6_rows` | `lean/Rubidium/K6.lean` | 53 |
| `theorem` | `K6` | `lean/Rubidium/K6.lean` | 92 |
| `theorem` | `isP_big` | `lean/Rubidium/K7.lean` | 20 |
| `theorem` | `window_step` | `lean/Rubidium/K7.lean` | 27 |
| `theorem` | `window_all` | `lean/Rubidium/K7.lean` | 44 |
| `theorem` | `pigeon` | `lean/Rubidium/K7.lean` | 74 |
| `theorem` | `enc_lt` | `lean/Rubidium/K7.lean` | 110 |
| `theorem` | `enc_inj` | `lean/Rubidium/K7.lean` | 118 |
| `theorem` | `win_length` | `lean/Rubidium/K7.lean` | 138 |
| `theorem` | `win_eq` | `lean/Rubidium/K7.lean` | 141 |
| `theorem` | `K7'` | `lean/Rubidium/K7.lean` | 157 |
| `theorem` | `isP_quotient_period` | `lean/Rubidium/K7.lean` | 174 |
| `theorem` | `isP_mod_period` | `lean/Rubidium/K7.lean` | 191 |
| `theorem` | `K7_odd_general_states` | `lean/Rubidium/K7.lean` | 215 |
| `theorem` | `K7_odd_start_positions` | `lean/Rubidium/K7.lean` | 226 |
| `theorem` | `blkE_step` | `lean/Rubidium/K9.lean` | 23 |
| `theorem` | `blkO_of_blk` | `lean/Rubidium/K9.lean` | 67 |
| `theorem` | `k9_rows` | `lean/Rubidium/K9.lean` | 90 |
| `theorem` | `K9_suff` | `lean/Rubidium/K9.lean` | 128 |
| `theorem` | `K9_nec` | `lean/Rubidium/K9.lean` | 169 |
| `theorem` | `K9` | `lean/Rubidium/K9.lean` | 205 |
| `theorem` | `K10_m1_all_states` | `lean/Rubidium/SmallOdd.lean` | 9 |
| `theorem` | `K10_m3_finite_states` | `lean/Rubidium/SmallOdd.lean` | 38 |
| `theorem` | `K10_m5_finite_states` | `lean/Rubidium/SmallOdd.lean` | 51 |
| `theorem` | `isP_one_one` | `lean/Rubidium/StartK4.lean` | 14 |
| `theorem` | `start_m_one` | `lean/Rubidium/StartK4.lean` | 20 |
| `theorem` | `start_ev2` | `lean/Rubidium/StartK4.lean` | 33 |
| `theorem` | `ev2_succ_of_even` | `lean/Rubidium/StartK4.lean` | 40 |
| `theorem` | `MainTheorem_K4_cases` | `lean/Rubidium/StartK4.lean` | 44 |

## Subgoal DAG (`data/dag.json`)

| ID | Title | Status | Failures | Needs Decomposition |
| :--- | :--- | :--- | ---: | :--- |
| `SG-001` | Game definition and decidable evaluator in Lean 4 (IsP, isPb) | `proved` | 0 | no |
| `SG-002` | Formalize small-m P-position characterizations (K3, K4, K4_even, K5_before, K6) | `proved` | 0 | no |
| `SG-003` | Formalize medium-m block-rule characterizations (K9, K10a, K13) | `proved` | 0 | no |
| `SG-004` | Formalize general even-m P-position structure and 2-adic valuation rules | `open` | 0 | no |
| `SG-005` | Formalize periodicity and preperiod bounds for odd m >= 7 | `proved` | 1 | no |
| `SG-006` | Characterize winning/losing positions for general states (r, p) | `open` | 0 | no |
| `SG-007` | Prove MainTheorem characterizing starting positions (n, 0) for all m >= 1 | `open` | 0 | no |
| `SG-008` | Characterize winning and losing general states (r, p) for odd m >= 7 | `proved` | 0 | no |
| `SG-009` | Characterize starting positions (n, 0) for odd m >= 7 using finite periodic representatives | `proved` | 0 | no |
| `SG-010` | Characterize winning and losing general states (r, p) for small odd m (m = 1, 3, 5) | `proved` | 0 | no |
| `SG-011` | Starting positions (n, 0) for m = 1 and for every m with ev2(m+1) = true (all even m, and odd m with v2(m+1) even): prove IsP 1 n 0 <-> n = 0, and IsP m n 0 <-> (m+1) | n by combining K4_even and K4_odd, as the corresponding cases of MainTheorem | `proved` | 0 | no |

## Recent Dead Ends (`data/dead_ends.jsonl`)

| PR | Title | Subgoals | Labels |
| ---: | :--- | :--- | :--- |
| #459 | SG-005: checkpoint-1 以降の claude-1 の Lean 4 の結果をまとめる（K7′〜K69、被覆率 94.82%） | `SG-005` | `ci-failed` |
| #411 | antigravity-1: PR #399（定理 K13 の Lean 4 形式化）の独立査読 | - | - |
| #359 | antigravity-1: PR #350（定理 K34）の独立査読（修正依頼） | - | - |
