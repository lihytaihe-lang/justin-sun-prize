# Candidate audit

Audit date: 2026-09-18

## Outcome

`JSP-000359` has been reactivated as a deliberately later, independent
reproduction and process trial. It is not treated as the first solution or the
first Lean formalization.

## Duplicate status: JSP-000359 / Erdős 440

An earlier complete formalization exists.

- The official awards repository has an active submission, PR #34, covering
  both the square-root counting bound and the sharp lower-limit result.
- Official issue #22 records an earlier public Lean proof in
  `plby/lean-proofs`.
- This implementation is later in priority and must not be presented as first.
- The current rules permit multiple valid PRs for the same problem but order
  them by priority timestamp; a later PR has no guaranteed award share.

References:

- <https://github.com/TheJustinSunPrize/awards/pull/34>
- <https://github.com/TheJustinSunPrize/awards/issues/22>
- <https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos440.lean>

## Corpus-level finding

The official catalog's `Lean proof: No` field is not sufficient evidence that a
problem is unformalized. The public `plby/lean-proofs` progress snapshot dated
2026-08-27 reports 601 fully formalized solved problems and only four solved
problems without a complete local Comparator setup: Erdos #216, #504, #599,
and #610.

Those remaining problems are not clean low-risk targets:

- #216 / JSP-000198 has active formalization work and a large geometric and
  computational scope.
- #504 / JSP-000404 has several active partial formalization PRs and an
  unresolved full-classification proof gap.
- #599 / JSP-000486 is the infinite Erdos-Menger theorem, a deep set-theoretic
  graph result.
- #610 has public Lean-related work that treats major external results as
  assumptions; completing those foundations is a research-scale project.

## Rule interpretation used

The website allocates 70% to the mathematical solver and 30% to the person or
team that completes the Lean formalization and submits the verified PR. Merely
re-running or independently checking another person's Lean proof does not make
the checker the formalization author and is not being treated here as a claim
to the 30% role.

## Current action

Complete and verify the independent Lean 4.34 implementation, publish a pinned
commit in this repository, and only then prepare the narrow catalog-reference
PR required by the current contribution guide. Continue screening the harder
remaining problems in parallel with the proof work; do not claim or imply a
guaranteed payout from this duplicate submission.
