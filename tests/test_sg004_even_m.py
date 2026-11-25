"""Independent verification tests for SG-004 (Rubidium.EvenM).

Directly implements the PROBLEM.md minimax definition of IsP(m, r, p)
and exhaustively verifies:
1. Complete even-m (r, p) characterization (`even_isP_iff` / `evenDiagSteps`).
2. 2-adic reduction (`evenDiagSteps_v2` / `even_diag_v2_reduction`).
3. Explicit winning-move construction (`even_winning_move`).
4. General v2(m+1)-even row, off-diagonal, and odd-m block rules.
"""

import unittest


def v2(n: int) -> int:
    if n == 0:
        return 0
    c = 0
    while n % 2 == 0:
        n //= 2
        c += 1
    return c


def solve_dp(m: int, max_r: int) -> list[list[bool]]:
    """Direct PROBLEM.md minimax DP for all 0 <= r <= max_r and 0 <= p <= m."""
    dp = [[False] * (m + 1) for _ in range(max_r + 1)]
    for p in range(m + 1):
        dp[0][p] = True
    for r in range(1, max_r + 1):
        lim = min(m, r)
        for p in range(m + 1):
            win = False
            for k in range(1, lim + 1):
                if k != p and dp[r - k][k]:
                    win = True
                    break
            dp[r][p] = not win
    return dp


def even_diag_steps(m: int, j: int, d: int) -> int:
    steps = 0
    while d != 0:
        if d % 2 == 0:
            d //= 2
            steps += 1
        elif j == 0:
            return steps
        else:
            j -= 1
            d = (m + 1 + d) // 2
            steps += 1
    return steps


class TestSG004EvenM(unittest.TestCase):
    def test_even_isP_iff_and_v2_reduction(self) -> None:
        for m in range(2, 22, 2):
            max_r = 6 * (m + 1)
            dp = solve_dp(m, max_r)
            for r in range(max_r + 1):
                j, d = divmod(r, m + 1)
                if d != 0:
                    # Verify 2-adic reduction identity on evenDiagSteps
                    s = even_diag_steps(m, j, d)
                    self.assertEqual(
                        s,
                        v2(d) + even_diag_steps(m, j, d // (2 ** v2(d))),
                        f"v2 reduction mismatch at m={m}, j={j}, d={d}",
                    )
                for p in range(m + 1):
                    expected = (d == 0) or (p == d and even_diag_steps(m, j, d) % 2 == 0)
                    self.assertEqual(
                        dp[r][p],
                        expected,
                        f"even_isP_iff mismatch at m={m}, r={r}, p={p}",
                    )

    def test_even_winning_move(self) -> None:
        for m in range(2, 18, 2):
            max_r = 5 * (m + 1)
            dp = solve_dp(m, max_r)
            for r in range(max_r + 1):
                j, d = divmod(r, m + 1)
                for p in range(m + 1):
                    if dp[r][p]:
                        continue
                    if p != d:
                        k = d
                    elif d % 2 == 0:
                        k = d // 2
                    else:
                        self.assertGreaterEqual(j, 1)
                        k = (m + 1 + d) // 2
                    self.assertTrue(1 <= k <= min(m, r) and k != p)
                    self.assertTrue(
                        dp[r - k][k],
                        f"winning move k={k} did not reach P at m={m}, r={r}, p={p}",
                    )

    def test_even_v2_odd_m_structure(self) -> None:
        # Odd m with v2(m+1) even: m = 3 (v2=2), 11 (v2=2), 15 (v2=4), 19 (v2=2)
        for m in (3, 11, 15, 19):
            self.assertEqual(v2(m + 1) % 2, 0)
            s = v2((m + 1) // 2)
            max_r = 5 * (m + 1)
            dp = solve_dp(m, max_r)
            for r in range(max_r + 1):
                d = r % (m + 1)
                for p in range(m + 1):
                    if d == 0:
                        self.assertTrue(dp[r][p])
                    elif p != d:
                        self.assertFalse(dp[r][p])
                    elif v2(d) <= s:
                        self.assertEqual(dp[r][d], v2(d) % 2 == 0)


if __name__ == "__main__":
    unittest.main()
