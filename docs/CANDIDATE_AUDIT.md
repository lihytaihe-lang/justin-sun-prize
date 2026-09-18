# Candidate audit

Audit date: 2026-09-18

## Outcome

No candidate has passed the adoption gate yet.

## Rejected candidate: JSP-000359 / Erdos 440

Reason: duplicate complete formalization.

- The official awards repository has an active submission, PR #34, covering
  both the square-root counting bound and the sharp lower-limit result.
- Official issue #22 records an earlier public Lean proof in
  `plby/lean-proofs`.
- A new independent implementation would be later in priority and must not be
  presented as the first or prize-qualifying formalization.

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

## Next safe action

Continue monitoring for a newly solved problem whose complete result has not
yet been formalized, or deliberately choose a research-scale open problem with
the understanding that completion is uncertain. Do not publish a scope issue,
formalization PR, or award claim until a candidate passes the adoption gate.
