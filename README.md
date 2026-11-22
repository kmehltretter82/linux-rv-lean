# Linux runtime verification in Lean

Linux runtime verification (RV) checks an observed sequence of kernel events against a model. This project studies what the monitor can conclude from that sequence. It hosts the Lean proofs and develops companion missions on [Prove2Me](https://prove2.me/).

## Verified in Lean

For a finite trace over two partially overlapping alphabets, the composed automaton reaches a given pair of states exactly when the projected traces reach the corresponding states separately. This gives the generated- and marked-language identities of Cassandras and Lafortune, chapter 2. If the next event fails after a legal prefix, at least one component that participates in that event has no transition, and conversely. [Proofs](LinuxRV/Parallel.lean) · [Chapter 2](https://doi.org/10.1007/978-0-387-68612-7_2)

The PREEMPT_RT application models all six switch labels in Figures 21–22. A switch is legal after a valid prefix exactly when S07 is in its `disabled` state and S08 is inside the scheduler. S07 merges IRQ masking and preemption disabling into the same intermediate state. Two consecutive IRQ-disable events can therefore take S07 to `disabled` by themselves. The theorem `switch_iff_controls` proves the interpretation in terms of both individual controls for histories in which each control alternates disable and enable. [Switch proofs](LinuxRV/Switch.lean) · [Source diagrams, p. 24](https://retis.santannapisa.it/~tommaso/publications/Elsevier-JSA-2020.pdf#page=24)

Build with `lake build` from the repository root. The project pins Lean 4.33.1 and the Prove2Me Mathlib revision. The standalone build includes the published Ramadge–Wonham generator with a narrower Mathlib import. [Generator source and attribution](Definitions/Def_RamadgeWonham_Shared_Generator.lean)

## First mission

Our first Linux mission is based on de Oliveira, Cucinotta, and de Oliveira’s *Efficient Formal Verification for the Linux Kernel* (SEFM 2019). Figure 4 draws a two-state wake-up monitor. Figure 5 encodes its transitions as a state-by-event matrix, with `-1` for an undefined transition. Figure 6 looks up the next state. These figures motivate the following **proposed correctness theorem**. [Paper and companion material](https://retis.santannapisa.it/~tommaso/papers/sefm19.php)

> Given a finite deterministic automaton with partial transitions and a finite, ordered trace over its event alphabet, the monitor built from its transition table reaches the source state after every legal prefix. If a next event has no transition, the monitor identifies its position and the state and event at the first failure.

1. **Table construction.** Prove that each cell encodes the specified successor or the undefined-transition sentinel.
2. **Trace execution.** Lift the single-step result to finite traces, including the empty trace and a failure on the first event.
3. **Worked example.** In Figure 4, disabling preemption makes `sched_waking` a legal self-loop. Re-enabling preemption makes the same event illegal. Check both traces against the published table.

The theorem concerns a mathematical model of table generation and lookup. A claim about the running kernel would additionally require evidence about the generator implementation, C representation, tracepoint instrumentation, and event ordering.

## Foundations to read and reuse

| Source | Role in the Lean development |
| --- | --- |
| Ramadge and Wonham, *Supervisory Control of a Class of Discrete Event Processes* (1987) | Reuse the published generator, partial transition function, and finite-word execution. Its **generated language** consists of all executable traces. Its **marked language** selects the traces ending in designated states. The monitor’s first-error property uses the generated language. [Paper](https://doi.org/10.1137/0325013) |
| Cassandras and Lafortune, *Introduction to Discrete Event Systems*, 2nd ed., ch. 2 | The **parallel-composition theorem** is proved here. Projection drops events outside each component’s alphabet. Both Linux papers use this construction to combine submodels. [Composition and event projections](Definitions/Def_CassandrasLafortune_Parallel.lean) · [Chapter, *Languages and Automata*](https://doi.org/10.1007/978-0-387-68612-7_2) |

As of November 22, 2026, Prove2Me lists the two Ramadge–Wonham goals (Theorems 7.1 and 10.1) as proved. All 7 synthesis milestones and all 9 quotient milestones are complete, including both parts of the supervisor-existence Theorem 6.1. The paper’s worked examples in §§11–12 are outside the milestone lists. [Synthesis mission](https://prove2.me/missions/bad7aaf3-40f1-4e24-aa6d-bd9bf41b9023) · [Quotient mission](https://prove2.me/missions/1d91bb1c-e3ad-4b2b-b153-18a2a9c7e0b8)

## Linux models and follow-up missions

Read the 2017 and 2018 models before the SEFM paper to see what goes into the monitor. The first proof can proceed with a single automaton. The composition theorem becomes relevant when moving on to the model built from several automata.

| Source | Proposed formalization |
| --- | --- |
| ETFA 2017 · *Automata-Based Modeling of Interrupts in the Linux PREEMPT RT Kernel* | Encode the IRQ/NMI model as the first interrupt case study. Check event sequences against its published transitions. This is the predecessor identified by the 2018 thread paper. [Paper](https://doi.org/10.1109/ETFA.2017.8247611) |
| EWILI 2018 · *Modeling the Behavior of Threads in the PREEMPT_RT Linux Kernel Using Automata* | Use the single-core thread model to replay Figure 5 against Figure 4. In Table 2, seven events have defined successors and the eighth is rejected. [Paper](https://hdl.handle.net/11382/527210) |
| ISORC 2019 · *Untangling the Intricacies of Thread Synchronization in the PREEMPT_RT Linux Kernel* | Trace the synchronization model cited as reference 33 in SEFM. Use its conference formulation alongside the expanded journal model below when choosing component automata. [Paper](https://retis.santannapisa.it/~tommaso/publications/IEEE-ISORC-2019.pdf) |
| Journal of Systems Architecture 2020 · *A Thread Synchronization Model for the PREEMPT_RT Linux Kernel* | The S07/S08 switch property is proved here, including the well-formed control-history assumption described above. [Paper, Figs. 21–22](https://doi.org/10.1016/j.sysarc.2020.101729) |
| de Oliveira’s 2020 thesis · *Automata-based Formal Analysis and Verification of the Real-Time Linux Kernel*, ch. 6 | Start with Lemma 6 on interference-free scheduling latency. For Theorem 1, make explicit the assumptions under which the blocking and interrupt-interference equation has a least positive solution. [Thesis, §6.2](https://bristot.me/files/research/papers/thesis/thesis.pdf) |
| ECRTS 2024 · Castrovilli and Bini, *SlackCheck* | Formalize Theorem 2. For the paper’s unbounded schedule, the CPU-service bound holds on every interval iff slack is nonnegative at every sched-in. Equation (11) supplies the intermediate result for sched-out–to–sched-in intervals. [Paper, §§2–3](https://doi.org/10.4230/LIPIcs.ECRTS.2024.2) |
