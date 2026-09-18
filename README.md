# Justin Sun Prize Lean formalization workspace

Public, AI-assisted Lean 4 work owned by `lihytaihe-lang`.

## Current status

An independent reproduction of `JSP-000359` / Erdős problem 440 is in active
development. No official pull request or award claim has been made yet.

Earlier complete Lean work and an earlier official submission already exist.
This repository therefore does **not** claim mathematical novelty,
first-formalization priority, or guaranteed prize eligibility. The immediate
goal is a complete, reproducible, current-Mathlib proof that can be used for a
transparent first process submission.

## Formalized scope

The target is the complete displayed scope of Erdős problem 440:

1. for every strictly increasing positive-integer sequence, the number of
   adjacent pairs whose LCM is at most `x` is `O(sqrt x)`; and
2. the greatest attainable value of the normalized `liminf` is exactly `1`.

`JustinSunPrize.JSP000359.original_problem` is the final combined theorem.
The project uses Lean `4.34.0` and Mathlib `v4.34.0`.

## Build

```sh
lake update
lake exe cache get
lake build
```

The GitHub Actions workflow runs the same build on every push. A passing build
is necessary but is not, by itself, proof of statement fidelity or award
eligibility.

## Public sources

- Prize rules: <https://www.hejustinsun.com/prize/rules>
- Official repository: <https://github.com/TheJustinSunPrize/awards>
- Contribution rules: <https://github.com/TheJustinSunPrize/awards/blob/main/CONTRIBUTING.md>
- Public Lean corpus screened for duplicates: <https://github.com/plby/lean-proofs>
- Earlier independent reproduction / official PR #34:
  <https://github.com/TheJustinSunPrize/awards/pull/34>

## Submission boundary

Only work attributable to this repository's contributor will be submitted or
claimed. The mathematics is historical work of Erdős and Szemerédi. Existing
Lean proofs were inspected for scope and are cited; they are not represented as
this contributor's first proof. The new source is AI-assisted and is being
checked against the full original statement without `sorry`, `admit`, custom
axioms, or substituted assumptions.
