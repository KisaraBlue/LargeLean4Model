/-
Let $n$ and $k$ be nonnegative integers with $k \leqslant n$. Then
(i ) $\binom{n}{0}=\binom{n}{n}=1$
(ii) $\binom{n}{k}=\binom{n}{n-k}$.
-/

import Mathlib

example (n k : ℕ) (h : k ≤ n) : n.choose 0 = n.choose n ∧ n.choose n = 1 ∧ n.choose k = n.choose (n-k) := by
  apply And.intro
  . rw [Nat.choose_zero_right]
    exact symm (Nat.choose_self n)
  . apply And.intro
    . exact Nat.choose_self n
    . exact symm (Nat.choose_symm h)
