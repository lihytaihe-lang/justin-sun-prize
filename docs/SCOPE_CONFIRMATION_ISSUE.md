# Proposed scope-confirmation issue

## Title

`[Clarification] Exact complete-formalization scope for JSP-000359`

## Body

I am preparing an original Lean formalization for JSP-000359 and want to
confirm the full theorem scope before implementation.

The catalog describes the problem as:

> How often can consecutive terms of the specified integer sequence have a
> small least common multiple?

Erdos Problem 440 gives two questions for an infinite increasing sequence
`A = {a_1 < a_2 < ...}` and the counting function
`A(x) = #{i : lcm(a_i, a_{i+1}) <= x}`:

1. prove `A(x) = O(sqrt x)`; and
2. determine the largest possible value of
   `liminf_{x -> infinity} A(x) / sqrt x`, recorded as `1`.

The catalog also links a short exposition proving an explicit upper bound of
the form `A(x) <= c sqrt(x) + O(log x)`, where `c` is approximately `1.86`.
That exposition does not appear to prove the sharp `liminf <= 1` assertion.

Under the current complete-solutions-only contribution rule, would a qualifying
Lean submission for JSP-000359 need to formalize both the big-O bound and the
sharp `liminf <= 1` result from Erdos-Szemeredi (1980)? Please also confirm the
intended quantifiers/domain for `x` and whether the more general consecutive
`k`-tuple results in the 1980 paper are outside this JSP entry.

No claim is being made in this issue. This is a scope clarification intended to
avoid submitting a partial formalization.

## References

- Catalog entry: <https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0301-0400.md#jsp-000359>
- Original problem: <https://www.erdosproblems.com/440>
- Contribution rule: <https://github.com/TheJustinSunPrize/awards/blob/main/CONTRIBUTING.md#external-solver-and-lean-submissions>
