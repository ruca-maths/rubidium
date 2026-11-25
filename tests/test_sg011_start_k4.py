#!/usr/bin/env python3
"""Independent DP check of the SG-011 statements (lean/Rubidium/StartK4.lean).

The game is evaluated directly from the definition in PROBLEM.md:
a position (r, p) is P iff every legal move k (1 <= k <= min(m, r), k != p)
leads to a position (r - k, k) that is not P.
"""

from __future__ import annotations

import unittest


def p_table(m: int, r_max: int) -> list[list[bool]]:
    table = [[False] * (m + 1) for _ in range(r_max + 1)]
    for r in range(r_max + 1):
        for p in range(m + 1):
            table[r][p] = all(
                not table[r - k][k] for k in range(1, min(m, r) + 1) if k != p
            )
    return table


def ev2(r: int) -> bool:
    """True iff v2(r) is even (r >= 1); mirrors Rubidium.ev2."""
    v = 0
    while r % 2 == 0:
        r //= 2
        v += 1
    return v % 2 == 0


class StartK4Test(unittest.TestCase):
    def test_m_one(self) -> None:
        table = p_table(1, 300)
        for n in range(301):
            self.assertEqual(table[n][0], n == 0, n)

    def test_ev2_cases(self) -> None:
        for m in range(1, 41):
            if not ev2(m + 1):
                continue
            table = p_table(m, 6 * (m + 1) + 50)
            for n in range(len(table)):
                self.assertEqual(table[n][0], n % (m + 1) == 0, (m, n))


if __name__ == "__main__":
    unittest.main()
