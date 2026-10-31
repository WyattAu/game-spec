# game-spec

Formal specifications and Lean 4 proofs for the WyattAu competition bots.
Runs the estate's research loop (see `ITERATIONS.md`): per spec area —
pull the literature → analyze the cutting edge → check whether other
ecosystems solved it or couldn't → implement in spec → adjust the proofs →
`lake build` green → repeat, 10 iterations.

Zero dependencies beyond Lean 4 core. Zero `sorry`s. CI fails on errors
**and** on any `declaration uses sorry`.

## Scope

| Game | Entry repo | Formal model | Key theorems |
|------|-----------|--------------|--------------|
| CodeCup 2027 Tumbleweed | `WyattAu/tumbleweed` (C++) | `GameSpec/Tumbleweed.lean` — axial hex cells, sightline raycast, placement, sightline counts | `seen_congr`, `seen_place_self` (the no-suicide foundation), `firstHit_congr`, empty-board sanity |
| Battlesnake | `WyattAu/wyatt-viper` (Rust) | queued (Iterations 6–8): grid occupancy w/ tail-vacate, head-to-head rules, safety theorem: `choose` never selects an unsafe move when a safe move exists | — |

## Layout

```
src/GameSpec/Axial.lean      axial hex geometry: cells, board extent, 6 dirs, offsets, offset_ne
src/GameSpec/Tumbleweed.lean colors/stacks/boards, rayStep/firstHit/seen, congruence theorems
docs/                        rules digests mirrored from bot-kit
ITERATIONS.md                the research-loop ledger
```

## Commands

```sh
lake build          # type-checks every proof; CI also greps for `sorry`
lake env lean src/GameSpec/Tumbleweed.lean   # single-module check
```

## Iteration roadmap (10 loops)

1. ✅ axial geometry + sightline model + `offset_ne`
2. ✅ keystone congruence (`seen_congr`, `seen_place_self`) + empty-board sanity
3. ✅ placement legality (`legalPlacement`) + no-recapture theorems
4. ✅ fill scanner (`fillStepScan`): soundness + completeness + fuel-bounded `fill`
5. ✅ totalValue monotonicity (`totalValue_place_gt`) + the two core-only sum lemmas (`sum_map_le`/`sum_map_lt`)
2. ✅ keystone congruence (`seen_congr`, `seen_place_self`) + empty-board sanity
3. placement legality (`seen ≥ 1`, no-suicide, strict-greater capture) as defs + the no-recapture theorem (opponent can never immediately retake)
4. territory fill simulation: termination (empty-cell count ↓ / total value ↑), saturation postcondition (post-fill, the filler has no legal move), determinism under row-major scan
5. engine-conformance bridge: property tests in `tumbleweed.cpp` mirroring each Lean lemma (the C++ territory sim must satisfy the same saturation postcondition)
6. Battlesnake grid: occupancy with tail-vacate semantics
7. viper safety: head-to-head deadly cells; theorem — `choose` output is safe whenever any safe move exists
8. ladder completeness: at least one safe move in every reachable position (the cornered-fallback is never needed)
9. game symmetry: Tumbleweed red/white play the same ruleset (protocol-level symmetry theorem)
10. extraction/conformance decision matrix (Lean spec ↔ C++/Rust: Aeneas vs hax vs Kani vs Creusot vs proptest mirror) + final report

## Related

- `WyattAu/tumbleweed` · `WyattAu/bot-kit` · `WyattAu/wyatt-viper` — the implementations
- `WyattAu/competitions` — the registry
- `WyattAu/accounting-spec` — the sibling formal repo where this loop protocol was born
