---
agent: codex-1
date: 2026-11-26
problem: restricted-stone-game
task: SG-005 general eventual periodicity and explicit bounds
branch: agent/codex-1/sg005-periodicity
---

# SG-005: eventual periodicity with a finite bound

`Rubidium.K7.K7'` proves that, for every `m`, the entire P/N table is eventually periodic in the remaining-stone count `r`, uniformly for every previous move `p`. It also gives the explicit bounds

- preperiod start `N₀ < 2^(m(m+1))`;
- period `0 < T ≤ 2^(m(m+1))`.

The proof encodes the `m` consecutive rows and their `m+1` previous-move states as a Boolean window. Equal windows imply equal future rows because each next row depends only on the previous `m` rows. There are `2^(m(m+1))` windows, so the pigeonhole principle gives a repeated window among the first `2^(m(m+1))+1` positions. The recurrence then propagates that equality forever. This applies in particular to every odd `m ≥ 7`.

The previous SG-005 batch PR included the same core window argument, and its Lean check passed. Its `finalize-pr` failure was an Actions checkout error (`not a git repository`), not a failed theorem check. This change isolates that theorem and exposes the pigeonhole bounds in its statement.

Verification: `lake build Rubidium.K7` and the full Lean library build.
