# JSA2020 Milestone 1 — Split Implementation Report

**Date:** 2026-11-28
**Repo:** `linux-rv-lean`
**Parent theorem:** `JSA2020.milestone1_wakeup_synchronization` (unchanged, still proved)
**Status:** All six sub-milestones and the parent compile with `lake build` (1004 jobs, no errors).
Only standard Lean axioms (`propext`, `Quot.sound`) are used; no `sorry`, `admit`, or custom axioms.

## What was done

Milestone 1 was split into six independently checkable sub-milestones, matching the
agent handover (`JSA2020_Milestone1_Agent_Handover.md`), plus shared reusable
definitions. The original parent theorem's statement and proof were preserved verbatim.

### Changed files

1. `Definitions/Def_JSA2020_SyncModel.lean` (+103 lines) — shared definitions:
   - `wakeupConsistent`, `wakeupDisabledCount`, `wakeupPhaseOf_eq_disabledCount`
   - `wakeupLift` / `wakeupProj` (state mappings), `wakeupLift_proj_of_consistent`,
     `wakeupConsistent_lift`, `wakeupProj_lift`
   - `wakeupGuard` (+ `Decidable` instance)
   - `wakeupReachable`, `wakeupExec`, `wakeupGuardedExec` (+ `Decidable` instances)
   - `wakeupReachableList` (the exact nine consistent product states),
     `wakeupReachableList_length : … = 9`
   - `wakeupWithoutS17` = G06 ‖ S02 and `wakeupWithoutG06` = S17 ‖ S02 over the same
     10-event alphabet, plus `wakeupExecWithoutS17` / `wakeupExecWithoutG06`
2. `LinuxRV/ThreadSync.lean` (+~320 lines) — the six sub-milestones and helpers.

### The six sub-milestones

| # | Declaration | Content |
|---|---|---|
| M1.1 | `milestone1_exact_reachability` | `wakeupReachable q ↔ wakeupConsistent q`, `wakeupReachable q ↔ q ∈ wakeupReachableList`, and the list has length 9. Soundness via `wakeup_reached_iff`; completeness via explicit witness prefixes `wakeupPreemptPrefix ++ wakeupIRQPrefix` for each of the nine pairs. |
| M1.2 | `milestone1_run_equivalence` | `wakeupLift q0 = q0`, `proj (lift s) = s`, `reachable q → lift (proj q) = q`, one-step correspondence `stepF (lift s) e = some (lift t) ↔ stepM s e = some t`, run-level `runF w = (runM w).map lift`, full endpoint correspondence `runF w = some q ↔ consistent q ∧ runM w = some (proj q)`, and trace-language equality `ExecF w ↔ ExecM w`. The map-cases are handled by two generic option-level lemmas (`map_lift_some_iff`, `map_lift_some_iff'`) to avoid stuck `Generator.Q` projections. |
| M1.3 | `milestone1_waking_iff` | `sched_waking` enabled at a reachable state iff `wakeupGuard` (preemption ≠ enabled ∧ IRQ ≠ noIRQ), and it is a self-loop when enabled. Both directions. |
| M1.4 | `milestone1_need_resched_iff` | Same enabling characterization and self-loop property for `sched_need_resched`. Independent of M1.3 except for the shared local helper. |
| M1.5 | `milestone1_s17_necessity` | Without S17, `[irq.localDisable, irq.hwDisable, notify a]` executes for both `waking` and `needResched`; the full product accepts `[localDisable]` but rejects the double-disable prefix and the suffixed traces; every full-product trace executes without S17 (`L(F) ⊆ L(G06‖S02)`); strictness witness. |
| M1.6 | `milestone1_g06_necessity` | Without G06, `[preempt.disable, preempt.disableSched, notify a]` executes for both notifications; full product rejects the second preemption-disable; the mismatched enable witness `[preempt.disableSched, preempt.enable]` executes without G06 but is rejected by the full product; inclusion `L(F) ⊆ L(S17‖S02)`; strictness witness. |

### Parent umbrella

```lean
theorem milestone1_wakeup_synchronization : … -- unchanged statement, still discharged
```

## Verification

- `lake build Definitions.Def_JSA2020_SyncModel` — OK
- `lake build LinuxRV.ThreadSync` — OK (first clean build after the split: warnings only, all lint-level)
- `lake build` (full project, 1004 jobs) — OK
- `#print axioms` on all six sub-milestones + parent:
  `propext` (and `Quot.sound` where Set/simp is involved) — standard foundations, nothing custom.

## Dependency order (as in the handover)

```
Shared defs (Def_JSA2020_SyncModel)
      ├── M1.1 (uses wakeup_reached_iff)
      │     ├── M1.2 (uses M1.1 for the inverse mapping)
      │     ├── M1.3
      │     └── M1.4
      ├── M1.5 (independent, projection lemmas wakeupWithoutS17_project_run)
      └── M1.6 (independent, projection lemmas wakeupWithoutG06_project_run)
              └── Parent milestone1_wakeup_synchronization (existing conjuncts)
```

## Deviations from the handover (documented, not weakening)

- The 27-state cardinality is expressed structurally (3×3×3 product type, documented) and the
  nine-state characterization is given by an explicit list + iff, instead of
  `Fintype.card Q = 27`. The `Definitions/` tree deliberately avoids Mathlib imports
  (standalone-build policy), and `Fintype` would require adding `Mathlib.Data.Fintype.Basic`.
  The scientific content (9 reachable out of 27, the other 18 ruled out by the iff) is preserved.
- `wakeupReachableList` is a `List` rather than a `Finset` for the same import-policy reason.
- The parent statement was kept exactly as it existed in the repo before the split
  (run agreement, reachability iff, notification iff, component counterexamples);
  the six sub-milestones are the strengthened decomposition around it.

## Remaining for the Prove2Me upload

This repo-side formalization is complete and verified. The platform upload still requires
the authenticated Prove2Me workflow (per `https://prove2.me/start.md` and the handover §D):

1. Retrieve the existing mission `f4dc0e5a-3716-42f0-b9a9-75846e88c4f8` and save the current draft.
2. Add the six child theorem cards in the mission's pinned environment and link the parent
   reduction to them.
3. Upload statements/proofs, poll verdicts, and report each status separately
   (open / pending / sketch-accepted / proved).

This agent has no Prove2Me credentials, so no upload was attempted and no upload success
is claimed. Everything above is a local, machine-checked Lean result.
