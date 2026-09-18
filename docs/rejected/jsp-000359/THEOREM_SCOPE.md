# Theorem scope inventory

## Public problem statement

For an infinite strictly increasing sequence of positive integers
`a_1 < a_2 < ...`, define

`count(x) = #{i : lcm(a_i, a_{i+1}) <= x}`.

The public Erdos Problem 440 page asks:

1. whether `count(x) = O(sqrt x)`; and
2. for the largest possible value of
   `liminf (count(x) / sqrt x)`.

The recorded sharp answer to the second question is `1`.

## Results visible in Erdos-Szemeredi (1980)

For the adjacent-pair case, the paper states:

- a sharp universal upper bound on the normalized `limsup`, with constant
  `sum_{k >= 1} (sqrt(k) - sqrt(k - 1)) / k`;
- a rigidity statement saying equality in that `limsup` bound forces normalized
  `liminf` equal to zero; and
- the universal sharp bound `liminf (count(x) / sqrt x) <= 1`.

The paper also discusses longer consecutive blocks. Those results should be
treated as out of scope unless the prize maintainers explicitly include them in
JSP-000359.

## Proposed Lean deliverable

Subject to maintainer confirmation, the minimum complete deliverable is:

1. a faithful definition of increasing positive-integer sequences and the
   adjacent-LCM counting function;
2. a universal `O(sqrt x)` theorem; and
3. the sharp universal `liminf <= 1` theorem, together with the natural-number
   example establishing attainability of `1`.

No `sorry`, `admit`, custom axioms, or weakened finite-only surrogate theorem
will be accepted in the final artifact.
