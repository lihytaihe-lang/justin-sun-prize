# JSP-000359 Lean formalization

Independent working repository for a possible Justin Sun Prize submission for
`JSP-000359` / Erdos Problem 440.

## Current status

This repository is in preflight. No award claim has been made.

Before implementation, the maintainers need to confirm the exact theorem scope
that counts as a complete formalization. The public catalog description is less
precise than the original problem, which contains both:

1. the bound `A(x) = O(sqrt x)`; and
2. the sharp upper bound `liminf A(x) / sqrt x <= 1`.

The short van Doorn exposition proves an explicit `c * sqrt x + log x` bound
with `c` approximately `1.86`; it does not by itself establish the sharp
`liminf <= 1` statement.

See [docs/SCOPE_CONFIRMATION_ISSUE.md](docs/SCOPE_CONFIRMATION_ISSUE.md) for the
maintainer question prepared before formalization begins.

## Sources

- Justin Sun Prize catalog entry: <https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0301-0400.md#jsp-000359>
- Erdos Problem 440: <https://www.erdosproblems.com/440>
- P. Erdos and E. Szemeredi, *Remarks on a problem of the American Mathematical Monthly*, Mat. Lapok 28 (1980), 121-124.
- W. van Doorn, *Sequences with bounded lcm for consecutive elements*.

## Submission boundary

The Lean proof will be kept in this external repository. The prize repository
will receive only catalog references and pinned proof metadata, as required by
its contribution rules.
