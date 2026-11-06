# EXTRACTION — Tumbleweed rules: Lean model → C++ engine traceability

Status: CURRENT (2026-11-06)

Where the truth lives:

| Question | Truth |
|---|---|
| Game rules, machine-checked | `src/GameSpec/Tumbleweed.lean` (this repo, 0 sorries) |
| Competition engine | `WyattAu/tumbleweed` `tumbleweed.cpp` |
| Rules-conformance tests | `WyattAu/tumbleweed` `tests/conformance.cpp` |
| Engine build/CI evidence | `WyattAu/tumbleweed` `.github/workflows/ci.yml` |
| Iteration ledger | `ITERATIONS.md` |

## The extraction matrix

Every rules-bearing Lean theorem and its C++ mirror. "Definitional" means
the property holds by construction in C++ (no separate test needed).

| It | Lean declaration (game-spec) | C++ mirror (conformance.cpp) | Channel |
|---|---|---|---|
| 1 | `offset_ne`, `rayStep`, `firstHit`, `seen` (k = 1..10, no self-sight) | `seen` walks `c + dc` — k = 0 excluded by construction | definitional + `sample_B2_E5` ("B2 sees E5, not itself") |
| 1 | third axis preserves `col − row` | `Grid::kSteps {1,1},{-1,-1}` | definitional + `sample_B2_E5` (B2↔E5 sightline) |
| 2 | `rayStep_congr_at`, `firstHitStep_foldl_congr`, `firstHit_congr`, `seen_congr` | — (model-internal congruence machinery) | lake build |
| 2 | `seen_place_self` (keystone) | `sweep_seen`: seen unchanged by any placement, all colours | conformance binary |
| 2 | `firstHit_emptyBoard`, `seen_emptyBoard` | empty board: no sightline hits | definitional (`Board` zero-init) |
| 3 | `place_value_self`, `place_value_ne` | `apply` writes `{color, seen}` once | definitional |
| 3 | `place_zero_ok`, `place_bound_ok` | `sweep_legal_and_place`: empty⇒0, values ∈ [0,6] | conformance binary |
| 3 | `legalPlacement` (4 conditions) | `sweep_legal_and_place`: full iff over every cell, both colours | conformance binary |
| 3 | `no_immediate_recapture(_legal)` | `legal()`: `v < seen_opponent ⇒ false` | definitional + iff test |
| 3 | `legalPlacementB_iff` | — (C++ has no Bool twin; `legal()` is the Prop) | lake build |
| 4 | `fillStepScan_sound/complete`, `fillStep`, `fill` | `Engine::fill` row-major scan; mirrored by `fill_bounded` | conformance binary (`fill_conformance`) |
| 5 | `totalValue`, `sum_map_const`, `totalValue_le_bound` | `total_value()` (Σ values); 6×91 = 546 cap | definitional + `fill_stable_of_big` bound test |
| 5 | `totalValue_place_gt`, `sum_map_le/lt` | `sweep_legal_and_place`: legal ⇒ total strictly increases | conformance binary |
| 6 | `fillStep_increase` | `fill_bounded`: every placed step adds ≥ 1 | conformance binary |
| 6 | `seen_le_six` | `sweep_seen`: counts ∈ [0, 6] | conformance binary |
| 6 | `fill_mono` | `fill_bounded`: total never decreases across steps | conformance binary |
| 7 | `fill_const_of_none` | fixpoint: no legal cells after fill; re-fill is a no-op | conformance binary |
| 7 | `fillStep_ok` | invariants re-checked after every applied move | conformance binary |
| 7 | `fill_stable_of_big` (≤ 547 iterations) | `fill_bounded` hard-caps at 547 | conformance binary |
| 7 | `fillStep_none_of_cap` | saturated board admits no legal placement | conformance binary (fixpoint check) |
| 7 | `fillStepScan_none_of_forall`, `fillStep_none_emptyBoard`, `fill_547_empty` | `test_empty_board`: 1 step, unchanged, territory 0 | conformance binary |
| 9 | `swapBoard` (+ involution), `seen_swap`, `legalPlacement_swap` | — (symmetry of the rules; engine is colour-agnostic by design — `legal`/`fill` take the colour as a parameter) | lake build |
| 9 | `rayStep_swap`, `fold_swap`, `firstHit_swap` | — (model-internal) | lake build |

Deliberately outside the model (strategy, not rules): `Engine::legal_moves`
scoring, `material_score`, `best()` territory eval, the 30 s clock. Those are
engine choices, verified by self-play (`scripts/match.py`) not by the rules
model.

## Verification channels

1. `lake build` — the Lean gate: every declaration above compiles, 0 sorries
   (game-spec CI on main).
2. Conformance binary — `tests/conformance.cpp` compiles the exact engine
   source and asserts every mirrored property: 1,148,925 checks, 0 failures
   (deterministic seeds 1–5, densities 10/25/50, random + reachable boards).
3. CI — `WyattAu/tumbleweed` quality workflow runs both channels plus the
   protocol smoke and self-play regression on every push.

## Catches the formalization produced

1. k = 0 ray self-sighting (a placed stack seeing itself) — pinned by
   `range' 1 10` / the C++ `c + dc` start.
2. The third sightline axis preserves `col − row` — validated against the
   official sample (red B2 → E5).
3. `me = Color.empty` silently broke the no-recapture theorem — forced into
   the open by the Lean statement.
4. `fill_mono`'s first reachability statement was unprovable as stated; the
   board-generalized induction is the fix (iteration 6 ledger).
5. `fill_self_of_big`'s original claim (`fill n b me = b`) was FALSE — the
   sequence stabilizes at the fixpoint board, not the start (iteration 7
   ledger; corrected to `fill_stable_of_big`).
6. The `@0` sentinel self-destruct in the engine's `best()` — found while
   aligning the eval with the model's monotonicity story (fixed in
   tumbleweed v2).
