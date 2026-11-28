import Definitions.Def_JSA2020_SyncModel
import LinuxRV.Parallel
import LinuxRV.Monitor

/-! Verification of the ISORC 2019 / JSA 2020 PREEMPT_RT thread-synchronization mission:
1. Wakeup and need-resched synchronization (`G06`, `S17`, `S02`).
2. Context-switch conditions under control pairing (`G06`, `S17`, `S07`, `S08`).
3. IRQ-locking and IRQ-handler exclusion (`S17`, `S12`, `S22`).
4. Unified seven-automaton composition, 18-state canonical collapse, and nonblocking property.
5. Published Linux kernel trace replays (JSA Figs. 28–29 and Fig. 32).
6. Main theorem combining all synchronization laws with SEFM 2019 table-monitor correctness. -/

namespace JSA2020

open RamadgeWonham.Shared CassandrasLafortune

private theorem runFrom_append {α : Type} (G : Generator α) (q : G.Q) (w s : List α) :
    G.runFrom q (w ++ s) = (G.runFrom q w).bind (fun r => G.runFrom r s) := by
  induction w generalizing q with
  | nil => rfl
  | cons a w ih =>
    rw [List.cons_append, runFrom_cons, runFrom_cons]
    cases G.δ a q with
    | none => rfl
    | some r => exact ih r

private theorem projected_cons {α ε : Type} (G : Generator α) (f : ε → Option α)
    (q : G.Q) (e : ε) (w : List ε) :
    G.runFrom q ((e :: w).filterMap f) =
      (localStep G q (f e)).bind (fun r => G.runFrom r (w.filterMap f)) := by
  cases h : f e <;> simp [h, localStep, runFrom_cons]

private theorem bind_eq_some_iff {α β : Type} (o : Option α) (f : α → Option β) (y : β) :
    o.bind f = some y ↔ ∃ x, o = some x ∧ f x = some y := by
  cases o <;> simp

private theorem map_eq_some_iff_inj {α β : Type} {f : α → β} (hf : Function.Injective f)
    (o : Option α) (x : α) :
    o.map f = some (f x) ↔ o = some x := by
  cases o with
  | none => simp
  | some a =>
    simp only [Option.map_some, Option.some.injEq]
    exact hf.eq_iff

/-! ### Milestone 1: Wakeup and need-resched synchronization (`G06`, `S17`, `S02`) -/

private theorem wakeup_step_agrees (q : WakeupControls) (e : WakeupSpecEvent) :
    wakeupProduct.δ e (withWakeupPhase q) = (wakeupGuarded.δ e q).map withWakeupPhase := by
  rcases q with ⟨p, i⟩
  cases e <;> rename_i a <;> cases a <;> cases p <;> cases i <;> rfl

theorem wakeup_run_agrees (w : List WakeupSpecEvent) :
    wakeupProduct.run w = (wakeupGuarded.run w).map withWakeupPhase := by
  suffices h : ∀ q : WakeupControls,
      wakeupProduct.runFrom (withWakeupPhase q) w =
        (wakeupGuarded.runFrom q w).map withWakeupPhase from
    h wakeupGuarded.q0
  induction w with
  | nil => exact fun _ => rfl
  | cons e w ih =>
    intro q
    erw [runFrom_cons wakeupProduct, runFrom_cons wakeupGuarded, wakeup_step_agrees]
    cases wakeupGuarded.δ e q with
    | none => rfl
    | some r => exact ih r

theorem wakeup_reached_iff (w : List WakeupSpecEvent) (q : WakeupControls) (s : Phase) :
    wakeupProduct.run w = some (q, s) ↔ wakeupGuarded.run w = some q ∧ wakeupPhaseOf q = s := by
  rw [wakeup_run_agrees]
  suffices aux : ∀ r : Option WakeupControls,
      r.map withWakeupPhase = some (q, s) ↔ r = some q ∧ wakeupPhaseOf q = s from
    aux (wakeupGuarded.run w)
  intro r
  cases r <;> simp [withWakeupPhase]
  intro h
  rw [h]

private def wakeupPreemptPrefix : PreemptState → List WakeupSpecEvent
  | .enabled => []
  | .disabled => [.preempt .disable]
  | .scheduling => [.preempt .disableSched]

private def wakeupIRQPrefix : IRQState → List WakeupSpecEvent
  | .noIRQ => []
  | .masked => [.irq .localDisable]
  | .handling => [.irq .hwDisable]

theorem wakeup_reachable_iff (q : WakeupControls) (s : Phase) :
    (∃ w, wakeupProduct.run w = some (q, s)) ↔ wakeupPhaseOf q = s := by
  constructor
  · rintro ⟨w, h⟩
    exact ((wakeup_reached_iff w q s).mp h).2
  · rintro rfl
    rcases q with ⟨p, i⟩
    exact ⟨wakeupPreemptPrefix p ++ wakeupIRQPrefix i, by cases p <;> cases i <;> rfl⟩

theorem wakeup_notification_iff (w : List WakeupSpecEvent) (q : WakeupControls) (s : Phase)
    (a : Notification) (h : wakeupProduct.run w = some (q, s)) :
    w ++ [.notify a] ∈ wakeupProduct.L ↔ q.1 ≠ .enabled ∧ q.2 ≠ .noIRQ := by
  have hq := ((wakeup_reached_iff w q s).mp h).1
  change (wakeupProduct.run (w ++ [.notify a])).isSome = true ↔ _
  erw [wakeup_run_agrees, run_append_event wakeupGuarded, hq]
  by_cases hg : q.1 ≠ .enabled ∧ q.2 ≠ .noIRQ <;> simp [wakeupGuarded, hg, Option.isSome]

/-- Milestone 1: exact characterization of the `G06 ‖ S17 ‖ S02` wakeup product (ISORC Figs.
10–12 / JSA Figs. 17–19), its 9 reachable states out of 27, the notification condition, and
counterexamples showing why both `S17` and `G06` are necessary. -/
theorem milestone1_wakeup_synchronization :
    (∀ w, wakeupProduct.run w = (wakeupGuarded.run w).map withWakeupPhase) ∧
    (∀ q s, (∃ w, wakeupProduct.run w = some (q, s)) ↔ wakeupPhaseOf q = s) ∧
    (∀ w q s a, wakeupProduct.run w = some (q, s) →
      (w ++ [.notify a] ∈ wakeupProduct.L ↔ q.1 ≠ .enabled ∧ q.2 ≠ .noIRQ)) ∧
    (∀ a : Notification,
      s02.run [.irq .localDisable, .irq .hwDisable, .notify a] = some .disabled ∧
      s17.run [.localDisable, .hwDisable] = none ∧
      s02.run [.preempt .disable, .preempt .disableSched, .notify a] = some .disabled ∧
      g06.run [.disable, .disableSched] = none) :=
  ⟨wakeup_run_agrees, wakeup_reachable_iff, wakeup_notification_iff,
    fun _ => ⟨rfl, rfl, rfl, rfl⟩⟩

/-! ### Milestone 2: Context-switch conditions (`G06`, `S17`, `S07`, `S08`) -/

theorem switchProduct_switch_iff (w : List SwitchTraceEvent) (k : SwitchEvent)
    (ph : Phase) (c : SchedContext) (h : switchProduct.run w = some (ph, c)) :
    w ++ [.shared k] ∈ switchProduct.L ↔ ph = .disabled ∧ c = .scheduler := by
  change (switchProduct.run (w ++ [.shared k])).isSome = true ↔ _
  rw [run_append_event, h]
  cases ph <;> cases c <;>
    simp [switchProduct, parallel, localStep, Event.left, Event.right, s07, s08]

private theorem switchWithControls_step_inv (q r : SwitchFullState) (e : SyncEvent)
    (hq : q.2.2.1 = switchPhaseOf (q.1, q.2.1))
    (hstep : switchWithControls.δ e q = some r) :
    r.2.2.1 = switchPhaseOf (r.1, r.2.1) := by
  rcases q with ⟨p, i, ph, c⟩
  dsimp only at hq
  subst hq
  cases e with
  | preempt a =>
    cases a <;> cases p <;> cases i <;>
      simp_all [switchWithControls, localStep, g06View, s17View, s07View, s08View,
        g06, s17, s07, disablePhase, enablePhase, switchPhaseOf, Option.bind] <;>
      subst hstep <;> rfl
  | irq a =>
    cases a <;> cases p <;> cases i <;>
      simp_all [switchWithControls, localStep, g06View, s17View, s07View, s08View,
        g06, s17, s07, disablePhase, enablePhase, switchPhaseOf, Option.bind] <;>
      subst hstep <;> rfl
  | notify _ =>
    simp_all [switchWithControls, localStep, g06View, s17View, s07View, s08View, Option.bind]
    subst hstep; rfl
  | scheduler a =>
    cases a <;> cases c <;>
      simp_all [switchWithControls, localStep, g06View, s17View, s07View, s08View,
        s08, Option.bind] <;>
      subst hstep <;> rfl
  | switch _ =>
    cases p <;> cases i <;> cases c <;>
      simp_all [switchWithControls, localStep, g06View, s17View, s07View, s08View,
        s07, s08, switchPhaseOf, Option.bind]
    subst hstep; rfl
  | taskState _ =>
    simp_all [switchWithControls, localStep, g06View, s17View, s07View, s08View, Option.bind]
    subst hstep; rfl
  | lock _ _ =>
    simp_all [switchWithControls, localStep, g06View, s17View, s07View, s08View, Option.bind]
    subst hstep; rfl

theorem switchWithControls_phase_inv (w : List SyncEvent) (p : PreemptState) (i : IRQState)
    (ph : Phase) (c : SchedContext)
    (h : switchWithControls.run w = some (p, i, ph, c)) :
    ph = switchPhaseOf (p, i) := by
  suffices aux : ∀ q : SwitchFullState, q.2.2.1 = switchPhaseOf (q.1, q.2.1) →
      switchWithControls.runFrom q w = some (p, i, ph, c) → ph = switchPhaseOf (p, i) from
    aux switchWithControls.q0 rfl h
  clear h
  induction w with
  | nil =>
    intro q hq hrun
    obtain rfl := Option.some.inj hrun
    exact hq
  | cons e w ih =>
    intro q hq hrun
    erw [runFrom_cons switchWithControls] at hrun
    cases hstep : switchWithControls.δ e q with
    | none => simp [hstep] at hrun
    | some r =>
      rw [hstep] at hrun
      exact ih r (switchWithControls_step_inv q r e hq hstep) hrun

theorem switchWithControls_switch_iff (w : List SyncEvent) (k : SwitchEvent)
    (p : PreemptState) (i : IRQState) (ph : Phase) (c : SchedContext)
    (h : switchWithControls.run w = some (p, i, ph, c)) :
    w ++ [.switch k] ∈ switchWithControls.L ↔
      p = .scheduling ∧ i = .masked ∧ c = .scheduler := by
  have hph := switchWithControls_phase_inv w p i ph c h
  subst hph
  change (switchWithControls.run (w ++ [.switch k])).isSome = true ↔ _
  rw [run_append_event, h]
  cases p <;> cases i <;> cases c <;>
    simp [switchWithControls, localStep, g06View, s17View, s07View, s08View,
      s07, s08, switchPhaseOf, Option.bind]

/-- Milestone 2: `S07 ‖ S08` alone permits repeated single-control disables, whereas
composing with `G06` and `S17` enforces exact switch conditions (`preempt_disable_sched`,
software `local_irq_disable`, and scheduler context) and separates switching from wakeup. -/
theorem milestone2_switch_synchronization :
    (∀ k : SwitchEvent,
      switchProduct.run
        [.rightOnly .scheduleEntry, .leftOnly .localIrqDisable,
         .leftOnly .localIrqDisable, .shared k] = some (.disabled, .scheduler) ∧
      switchProduct.run
        [.rightOnly .scheduleEntry, .leftOnly .preemptDisableSched,
         .leftOnly .preemptDisableSched, .shared k] = some (.disabled, .scheduler)) ∧
    (∀ w p i ph c, switchWithControls.run w = some (p, i, ph, c) →
      ph = switchPhaseOf (p, i)) ∧
    (∀ w k p i ph c, switchWithControls.run w = some (p, i, ph, c) →
      (w ++ [.switch k] ∈ switchWithControls.L ↔
        p = .scheduling ∧ i = .masked ∧ c = .scheduler)) ∧
    (∀ (a : Notification) (k : SwitchEvent),
      wakeupProduct.run [.preempt .disable, .irq .localDisable, .notify a] =
        some ((.disabled, .masked), .disabled) ∧
      switchWithControls.run
        [.scheduler .scheduleEntry, .preempt .disable, .irq .localDisable, .switch k] = none ∧
      wakeupProduct.run [.preempt .disableSched, .irq .hwDisable, .notify a] =
        some ((.scheduling, .handling), .disabled) ∧
      switchWithControls.run
        [.scheduler .scheduleEntry, .preempt .disableSched, .irq .hwDisable, .switch k] = none) :=
  ⟨fun _ => ⟨rfl, rfl⟩, switchWithControls_phase_inv, switchWithControls_switch_iff,
    fun _ _ => ⟨rfl, rfl, rfl, rfl⟩⟩

/-! ### Milestone 3: IRQ locking and IRQ-handler exclusion (`S17`, `S12`, `S22`) -/

private theorem irqLock_step_inv (active masked active' masked' : Bool) (e : IRQLockTraceEvent)
    (hinv : active = true → masked = true)
    (hstep : irqLockProduct.δ e (active, masked) = some (active', masked')) :
    active' = true → masked' = true := by
  cases e with
  | leftOnly _ =>
    cases active <;> cases masked <;>
      simp_all [irqLockProduct, parallel, localStep, Event.left, Event.right, s12, s22]
  | rightOnly a => exact Empty.elim a
  | shared c =>
    cases c with
    | irq a =>
      cases a <;> cases active <;> cases masked <;>
        simp_all [irqLockProduct, parallel, localStep, Event.left, Event.right, s12, s22]
    | lock _ _ =>
      cases active <;> cases masked <;>
        simp_all [irqLockProduct, parallel, localStep, Event.left, Event.right, s12, s22]

theorem irqLock_reachable_iff (active masked : Bool) :
    (∃ w, irqLockProduct.run w = some (active, masked)) ↔
      ∃ i : IRQState, active = irqActive i ∧ masked = irqMaskedOrActive i := by
  constructor
  · rintro ⟨w, h⟩
    have hinv : active = true → masked = true := by
      suffices aux : ∀ p : Bool × Bool, (p.1 = true → p.2 = true) →
          irqLockProduct.runFrom p w = some (active, masked) →
          (active = true → masked = true) from
        aux irqLockProduct.q0 (by simp [irqLockProduct, parallel, s12]) h
      clear h
      induction w with
      | nil =>
        intro p hp hrun
        obtain rfl := Option.some.inj hrun
        exact hp
      | cons e w ih =>
        intro p hp hrun
        erw [runFrom_cons irqLockProduct] at hrun
        cases hstep : irqLockProduct.δ e p with
        | none => simp [hstep] at hrun
        | some r =>
          rw [hstep] at hrun
          exact ih r (irqLock_step_inv p.1 p.2 r.1 r.2 e hp hstep) hrun
    cases active <;> cases masked
    · exact ⟨.noIRQ, rfl, rfl⟩
    · exact ⟨.masked, rfl, rfl⟩
    · exact False.elim (by cases hinv rfl)
    · exact ⟨.handling, rfl, rfl⟩
  · rintro ⟨i, rfl, rfl⟩
    cases i with
    | noIRQ => exact ⟨[], rfl⟩
    | masked => exact ⟨[.shared (.irq .localDisable)], rfl⟩
    | handling => exact ⟨[.shared (.irq .hwDisable)], rfl⟩

theorem irqLock_lock_iff (w : List IRQLockTraceEvent) (active masked : Bool)
    (k : LockKind) (a : LockAction) (h : irqLockProduct.run w = some (active, masked)) :
    w ++ [.shared (.lock k a)] ∈ irqLockProduct.L ↔ active = false ∧ masked = false := by
  change (irqLockProduct.run (w ++ [.shared (.lock k a)])).isSome = true ↔ _
  rw [run_append_event, h]
  cases active <;> cases masked <;>
    simp [irqLockProduct, parallel, localStep, Event.left, Event.right, s12, s22]

/-- Milestone 3: exact 3-state correspondence of `S12 ‖ S22` with `S17`, lock legality for
all twelve lock events, separation of `S22` from `S12` under software IRQ masking, and
`S12`'s full exclusion of scheduling, locking, and non-return IRQ events during IRQ handling. -/
theorem milestone3_irq_locking :
    (∀ active masked,
      (∃ w, irqLockProduct.run w = some (active, masked)) ↔
        ∃ i : IRQState, active = irqActive i ∧ masked = irqMaskedOrActive i) ∧
    (∀ w active masked k a, irqLockProduct.run w = some (active, masked) →
      (w ++ [.shared (.lock k a)] ∈ irqLockProduct.L ↔ active = false ∧ masked = false)) ∧
    (∀ k a,
      s12.run [.inr (.irq .localDisable), .inr (.lock k a)] = some false ∧
      irqLockProduct.run [.shared (.irq .localDisable), .shared (.lock k a)] = none) ∧
    ((∀ e : S12SchedulingEvent, s12.δ (.inl e) true = none) ∧
      (∀ k a, s12.δ (.inr (.lock k a)) true = none) ∧
      s12.δ (.inr (.irq .localDisable)) true = none ∧
      s12.δ (.inr (.irq .localEnable)) true = none ∧
      s12.δ (.inr (.irq .hwDisable)) true = none) :=
  ⟨irqLock_reachable_iff, irqLock_lock_iff, fun _ _ => ⟨rfl, rfl⟩,
    ⟨fun _ => rfl, fun _ _ => rfl, rfl, rfl, rfl⟩⟩

/-! ### Milestone 4: Unified seven-automaton product, 18 reachable states, and nonblocking -/

private theorem publishedSyncModel_step_eq_some_iff (e : SyncEvent) (r r' : SyncModelState) :
    publishedSyncModel.δ e r = some r' ↔
      localStep g06 r.1 (g06View e) = some r'.1 ∧
      localStep s17 r.2.1 (s17View e) = some r'.2.1 ∧
      localStep s02 r.2.2.1 (s02View e) = some r'.2.2.1 ∧
      localStep s07 r.2.2.2.1 (s07View e) = some r'.2.2.2.1 ∧
      localStep s08 r.2.2.2.2.1 (s08View e) = some r'.2.2.2.2.1 ∧
      localStep s12 r.2.2.2.2.2.1 (s12View e) = some r'.2.2.2.2.2.1 ∧
      localStep s22 r.2.2.2.2.2.2 (s22View e) = some r'.2.2.2.2.2.2 := by
  rcases r with ⟨r1, r2, r3, r4, r5, r6, r7⟩
  rcases r' with ⟨p', i', p02', p07', c', a12', m22'⟩
  dsimp only [publishedSyncModel]
  cases localStep g06 r1 (g06View e) with
  | none => simp [Option.bind]
  | some p =>
  cases localStep s17 r2 (s17View e) with
  | none => simp [Option.bind]
  | some i =>
  cases localStep s02 r3 (s02View e) with
  | none => simp [Option.bind]
  | some p02 =>
  cases localStep s07 r4 (s07View e) with
  | none => simp [Option.bind]
  | some p07 =>
  cases localStep s08 r5 (s08View e) with
  | none => simp [Option.bind]
  | some c =>
  cases localStep s12 r6 (s12View e) with
  | none => simp [Option.bind]
  | some a12 =>
  cases localStep s22 r7 (s22View e) with
  | none => simp [Option.bind]
  | some m22 =>
    constructor
    · intro h
      change some (p, i, p02, p07, c, a12, m22) = some (p', i', p02', p07', c', a12', m22') at h
      cases h
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · rintro ⟨h1, h2, h3, h4, h5, h6, h7⟩
      cases h1; cases h2; cases h3; cases h4; cases h5; cases h6; cases h7
      rfl

theorem publishedSyncModel_run_iff (w : List SyncEvent) (q : SyncModelState) :
    publishedSyncModel.run w = some q ↔
      g06.run (w.filterMap g06View) = some q.1 ∧
      s17.run (w.filterMap s17View) = some q.2.1 ∧
      s02.run (w.filterMap s02View) = some q.2.2.1 ∧
      s07.run (w.filterMap s07View) = some q.2.2.2.1 ∧
      s08.run (w.filterMap s08View) = some q.2.2.2.2.1 ∧
      s12.run (w.filterMap s12View) = some q.2.2.2.2.2.1 ∧
      s22.run (w.filterMap s22View) = some q.2.2.2.2.2.2 := by
  suffices aux : ∀ r : SyncModelState,
      publishedSyncModel.runFrom r w = some q ↔
        g06.runFrom r.1 (w.filterMap g06View) = some q.1 ∧
        s17.runFrom r.2.1 (w.filterMap s17View) = some q.2.1 ∧
        s02.runFrom r.2.2.1 (w.filterMap s02View) = some q.2.2.1 ∧
        s07.runFrom r.2.2.2.1 (w.filterMap s07View) = some q.2.2.2.1 ∧
        s08.runFrom r.2.2.2.2.1 (w.filterMap s08View) = some q.2.2.2.2.1 ∧
        s12.runFrom r.2.2.2.2.2.1 (w.filterMap s12View) = some q.2.2.2.2.2.1 ∧
        s22.runFrom r.2.2.2.2.2.2 (w.filterMap s22View) = some q.2.2.2.2.2.2 from
    aux publishedSyncModel.q0
  induction w with
  | nil =>
    intro r
    rcases r with ⟨r1, r2, r3, r4, r5, r6, r7⟩
    rcases q with ⟨q1, q2, q3, q4, q5, q6, q7⟩
    change some (r1, r2, r3, r4, r5, r6, r7) = some (q1, q2, q3, q4, q5, q6, q7) ↔
      some r1 = some q1 ∧ some r2 = some q2 ∧ some r3 = some q3 ∧ some r4 = some q4 ∧
      some r5 = some q5 ∧ some r6 = some q6 ∧ some r7 = some q7
    simp
  | cons e w ih =>
    intro r
    erw [runFrom_cons publishedSyncModel, bind_eq_some_iff,
      projected_cons g06, projected_cons s17, projected_cons s02, projected_cons s07,
      projected_cons s08, projected_cons s12, projected_cons s22,
      bind_eq_some_iff, bind_eq_some_iff, bind_eq_some_iff, bind_eq_some_iff,
      bind_eq_some_iff, bind_eq_some_iff, bind_eq_some_iff]
    constructor
    · rintro ⟨r', hstep, hrun⟩
      obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := (publishedSyncModel_step_eq_some_iff e r r').mp hstep
      obtain ⟨k1, k2, k3, k4, k5, k6, k7⟩ := (ih r').mp hrun
      exact ⟨⟨r'.1, h1, k1⟩, ⟨r'.2.1, h2, k2⟩, ⟨r'.2.2.1, h3, k3⟩, ⟨r'.2.2.2.1, h4, k4⟩,
        ⟨r'.2.2.2.2.1, h5, k5⟩, ⟨r'.2.2.2.2.2.1, h6, k6⟩, ⟨r'.2.2.2.2.2.2, h7, k7⟩⟩
    · rintro ⟨⟨r1, h1, k1⟩, ⟨r2, h2, k2⟩, ⟨r3, h3, k3⟩, ⟨r4, h4, k4⟩,
        ⟨r5, h5, k5⟩, ⟨r6, h6, k6⟩, ⟨r7, h7, k7⟩⟩
      refine ⟨(r1, r2, r3, r4, r5, r6, r7), ?_, ?_⟩
      · exact (publishedSyncModel_step_eq_some_iff e r (r1, r2, r3, r4, r5, r6, r7)).mpr
          ⟨h1, h2, h3, h4, h5, h6, h7⟩
      · exact (ih (r1, r2, r3, r4, r5, r6, r7)).mpr ⟨k1, k2, k3, k4, k5, k6, k7⟩

theorem publishedSyncModel_languages (w : List SyncEvent) :
    (w ∈ publishedSyncModel.L ↔
      w.filterMap g06View ∈ g06.L ∧
      w.filterMap s17View ∈ s17.L ∧
      w.filterMap s02View ∈ s02.L ∧
      w.filterMap s07View ∈ s07.L ∧
      w.filterMap s08View ∈ s08.L ∧
      w.filterMap s12View ∈ s12.L ∧
      w.filterMap s22View ∈ s22.L) ∧
    (w ∈ publishedSyncModel.Lm ↔
      w.filterMap g06View ∈ g06.Lm ∧
      w.filterMap s17View ∈ s17.Lm ∧
      w.filterMap s02View ∈ s02.Lm ∧
      w.filterMap s07View ∈ s07.Lm ∧
      w.filterMap s08View ∈ s08.Lm ∧
      w.filterMap s12View ∈ s12.Lm ∧
      w.filterMap s22View ∈ s22.Lm) := by
  constructor
  · simp only [Generator.L, Set.mem_ofPred_eq, Option.isSome_iff_exists]
    constructor
    · rintro ⟨q, h⟩
      obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := (publishedSyncModel_run_iff w q).mp h
      exact ⟨⟨_, h1⟩, ⟨_, h2⟩, ⟨_, h3⟩, ⟨_, h4⟩, ⟨_, h5⟩, ⟨_, h6⟩, ⟨_, h7⟩⟩
    · rintro ⟨⟨q1, h1⟩, ⟨q2, h2⟩, ⟨q3, h3⟩, ⟨q4, h4⟩, ⟨q5, h5⟩, ⟨q6, h6⟩, ⟨q7, h7⟩⟩
      exact ⟨(q1, q2, q3, q4, q5, q6, q7),
        (publishedSyncModel_run_iff w (q1, q2, q3, q4, q5, q6, q7)).mpr
          ⟨h1, h2, h3, h4, h5, h6, h7⟩⟩
  · constructor
    · rintro ⟨q, h, m1, m2, m3, m4, m5, m6, m7⟩
      obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := (publishedSyncModel_run_iff w q).mp h
      exact ⟨⟨_, h1, m1⟩, ⟨_, h2, m2⟩, ⟨_, h3, m3⟩, ⟨_, h4, m4⟩,
        ⟨_, h5, m5⟩, ⟨_, h6, m6⟩, ⟨_, h7, m7⟩⟩
    · rintro ⟨⟨q1, h1, m1⟩, ⟨q2, h2, m2⟩, ⟨q3, h3, m3⟩, ⟨q4, h4, m4⟩,
        ⟨q5, h5, m5⟩, ⟨q6, h6, m6⟩, ⟨q7, h7, m7⟩⟩
      exact ⟨(q1, q2, q3, q4, q5, q6, q7),
        (publishedSyncModel_run_iff w (q1, q2, q3, q4, q5, q6, q7)).mpr
          ⟨h1, h2, h3, h4, h5, h6, h7⟩,
        ⟨m1, m2, m3, m4, m5, m6, m7⟩⟩

private theorem localStep_eq_none_iff {α : Type} (G : Generator α) (q : G.Q) (o : Option α) :
    localStep G q o = none ↔ ∃ a, o = some a ∧ G.δ a q = none := by
  cases o with
  | none => simp [localStep]
  | some a => simp [localStep]

theorem publishedSyncModel_blocked_iff (q : SyncModelState) (e : SyncEvent) :
    publishedSyncModel.δ e q = none ↔ componentBlocked q e := by
  rcases q with ⟨q1, q2, q3, q4, q5, q6, q7⟩
  dsimp only [publishedSyncModel, componentBlocked]
  cases h1 : localStep g06 q1 (g06View e) with
  | none =>
    simp [Option.bind, (localStep_eq_none_iff g06 q1 (g06View e)).mp h1]
  | some p =>
  cases h2 : localStep s17 q2 (s17View e) with
  | none =>
    simp [Option.bind, (localStep_eq_none_iff s17 q2 (s17View e)).mp h2]
  | some i =>
  cases h3 : localStep s02 q3 (s02View e) with
  | none =>
    simp [Option.bind, (localStep_eq_none_iff s02 q3 (s02View e)).mp h3]
  | some p02 =>
  cases h4 : localStep s07 q4 (s07View e) with
  | none =>
    simp [Option.bind, (localStep_eq_none_iff s07 q4 (s07View e)).mp h4]
  | some p07 =>
  cases h5 : localStep s08 q5 (s08View e) with
  | none =>
    simp [Option.bind, (localStep_eq_none_iff s08 q5 (s08View e)).mp h5]
  | some c =>
  cases h6 : localStep s12 q6 (s12View e) with
  | none =>
    simp [Option.bind, (localStep_eq_none_iff s12 q6 (s12View e)).mp h6]
  | some a12 =>
  cases h7 : localStep s22 q7 (s22View e) with
  | none =>
    simp [Option.bind, (localStep_eq_none_iff s22 q7 (s22View e)).mp h7]
  | some m22 =>
    constructor
    · intro h
      change some (p, i, p02, p07, c, a12, m22) = none at h
      cases h
    · rintro (h | h | h | h | h | h | h)
      · exact absurd ((localStep_eq_none_iff g06 q1 (g06View e)).mpr h) (by rw [h1]; simp)
      · exact absurd ((localStep_eq_none_iff s17 q2 (s17View e)).mpr h) (by rw [h2]; simp)
      · exact absurd ((localStep_eq_none_iff s02 q3 (s02View e)).mpr h) (by rw [h3]; simp)
      · exact absurd ((localStep_eq_none_iff s07 q4 (s07View e)).mpr h) (by rw [h4]; simp)
      · exact absurd ((localStep_eq_none_iff s08 q5 (s08View e)).mpr h) (by rw [h5]; simp)
      · exact absurd ((localStep_eq_none_iff s12 q6 (s12View e)).mpr h) (by rw [h6]; simp)
      · exact absurd ((localStep_eq_none_iff s22 q7 (s22View e)).mpr h) (by rw [h7]; simp)

theorem embedCore_injective : Function.Injective embedCore := by
  rintro ⟨p1, i1, c1⟩ ⟨p2, i2, c2⟩ h
  simp only [embedCore, Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl, _, _, rfl, _, _⟩
  rfl

private theorem sync_step_agrees (s : CoreState) (e : SyncEvent) :
    publishedSyncModel.δ e (embedCore s) = (canonicalSyncModel.δ e s).map embedCore := by
  rcases s with ⟨p, i, c⟩
  cases e with
  | preempt a => cases a <;> cases p <;> cases i <;> rfl
  | irq a => cases a <;> cases p <;> cases i <;> rfl
  | notify _ => cases p <;> cases i <;> rfl
  | scheduler a => cases a <;> cases p <;> cases i <;> cases c <;> rfl
  | switch _ => cases p <;> cases i <;> cases c <;> rfl
  | taskState _ => cases p <;> cases i <;> rfl
  | lock _ _ => cases p <;> cases i <;> rfl

theorem sync_run_agrees (w : List SyncEvent) :
    publishedSyncModel.run w = (canonicalSyncModel.run w).map embedCore := by
  suffices h : ∀ s : CoreState,
      publishedSyncModel.runFrom (embedCore s) w =
        (canonicalSyncModel.runFrom s w).map embedCore from
    h canonicalSyncModel.q0
  induction w with
  | nil => exact fun _ => rfl
  | cons e w ih =>
    intro s
    erw [runFrom_cons publishedSyncModel, runFrom_cons canonicalSyncModel, sync_step_agrees]
    cases canonicalSyncModel.δ e s with
    | none => rfl
    | some r => exact ih r

private def corePrefix (s : CoreState) : List SyncEvent :=
  let (p, i, c) := s
  (match c with | .thread => [] | .scheduler => [.scheduler .scheduleEntry]) ++
  (match p with | .enabled => [] | .disabled => [.preempt .disable]
                | .scheduling => [.preempt .disableSched]) ++
  (match i with | .noIRQ => [] | .masked => [.irq .localDisable]
                | .handling => [.irq .hwDisable])

private def coreSuffix (s : CoreState) : List SyncEvent :=
  let (p, i, c) := s
  (match i with | .noIRQ => [] | .masked => [.irq .localEnable]
                | .handling => [.irq .hwEnable]) ++
  (match p with | .enabled => [] | .disabled => [.preempt .enable]
                | .scheduling => [.preempt .enableSched]) ++
  (match c with | .thread => [] | .scheduler => [.scheduler .scheduleExit])

theorem canonicalSyncModel_accessible : canonicalSyncModel.Accessible := by
  rintro ⟨p, i, c⟩
  refine ⟨corePrefix (p, i, c), ?_⟩
  cases p <;> cases i <;> cases c <;> rfl

theorem canonicalSyncModel_coAccessible : canonicalSyncModel.CoAccessible := by
  intro w hw
  obtain ⟨⟨p, i, c⟩, hrun⟩ := Option.isSome_iff_exists.mp hw
  refine ⟨coreSuffix (p, i, c), canonicalSyncModel.q0, ?_, rfl⟩
  change canonicalSyncModel.runFrom canonicalSyncModel.q0 (w ++ coreSuffix (p, i, c)) = _
  rw [runFrom_append]
  change canonicalSyncModel.runFrom canonicalSyncModel.q0 w = some (p, i, c) at hrun
  rw [hrun]
  cases p <;> cases i <;> cases c <;> rfl

theorem canonicalSyncModel_trim : canonicalSyncModel.IsTrim :=
  ⟨canonicalSyncModel_accessible, canonicalSyncModel_coAccessible⟩

theorem publishedSyncModel_nonblocking : publishedSyncModel.CoAccessible := by
  intro w hw
  have hcw : w ∈ canonicalSyncModel.L := by
    change (publishedSyncModel.run w).isSome = true at hw
    rw [sync_run_agrees] at hw
    cases hc : canonicalSyncModel.run w with
    | none =>
      rw [hc] at hw
      cases hw
    | some s =>
      change (canonicalSyncModel.run w).isSome = true
      rw [hc]
      rfl
  obtain ⟨s, q, hrun, hqm⟩ := canonicalSyncModel_coAccessible w hcw
  have hq0 : q = canonicalSyncModel.q0 := hqm
  subst hq0
  refine ⟨s, publishedSyncModel.q0, ?_, ?_⟩
  · rw [sync_run_agrees, hrun]
    rfl
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem publishedSyncModel_reachable_iff (q : SyncModelState) :
    (∃ w, publishedSyncModel.run w = some q) ↔ ∃ s : CoreState, q = embedCore s := by
  constructor
  · rintro ⟨w, h⟩
    rw [sync_run_agrees] at h
    cases hc : canonicalSyncModel.run w with
    | none =>
      rw [hc] at h
      cases h
    | some s =>
      rw [hc] at h
      exact ⟨s, (Option.some.inj h).symm⟩
  · rintro ⟨s, rfl⟩
    obtain ⟨w, hw⟩ := canonicalSyncModel_accessible s
    exact ⟨w, by rw [sync_run_agrees, hw]; rfl⟩

/-- Milestone 4: component-wise language projection, exact bisimulation collapsing the
648-state product to the 18-state trim canonical model, and Ramadge–Wonham nonblocking. -/
theorem milestone4_unified_composition :
    (∀ w q, publishedSyncModel.run w = some q ↔
      g06.run (w.filterMap g06View) = some q.1 ∧
      s17.run (w.filterMap s17View) = some q.2.1 ∧
      s02.run (w.filterMap s02View) = some q.2.2.1 ∧
      s07.run (w.filterMap s07View) = some q.2.2.2.1 ∧
      s08.run (w.filterMap s08View) = some q.2.2.2.2.1 ∧
      s12.run (w.filterMap s12View) = some q.2.2.2.2.2.1 ∧
      s22.run (w.filterMap s22View) = some q.2.2.2.2.2.2) ∧
    (∀ w, publishedSyncModel.run w = (canonicalSyncModel.run w).map embedCore) ∧
    (∀ q, (∃ w, publishedSyncModel.run w = some q) ↔ ∃ s : CoreState, q = embedCore s) ∧
    Function.Injective embedCore ∧
    canonicalSyncModel.IsTrim ∧
    publishedSyncModel.CoAccessible :=
  ⟨publishedSyncModel_run_iff, sync_run_agrees, publishedSyncModel_reachable_iff,
    embedCore_injective, canonicalSyncModel_trim, publishedSyncModel_nonblocking⟩

/-! ### Milestone 5: Published Linux kernel trace replays (JSA Figs. 28–29 and Fig. 32) -/

theorem figure29_monitor_replay :
    syncMonitor figure29Trace =
      .error (2, coreStateEnum (.enabled, .noIRQ, .thread), syncEventEnum (.notify .waking)) := by
  exact ((LinuxRV.monitor_correct canonicalSyncModel coreStateEnum syncEventEnum
      figure29Trace).2 2 (.enabled, .noIRQ, .thread) (.notify .waking)).mpr
    ⟨[.preempt .disable, .preempt .enable], [], rfl, rfl, rfl, rfl⟩

theorem figure32_monitor_replay :
    syncMonitor figure32RootedTrace =
      .error (4, coreStateEnum (.disabled, .handling, .thread),
        syncEventEnum (.lock .mutex .lock)) := by
  exact ((LinuxRV.monitor_correct canonicalSyncModel coreStateEnum syncEventEnum
      figure32RootedTrace).2 4 (.disabled, .handling, .thread) (.lock .mutex .lock)).mpr
    ⟨[.irq .localDisable, .preempt .disable, .irq .localEnable, .irq .hwDisable],
      [], rfl, rfl, rfl, rfl⟩

/-- Milestone 5: faithful replay of JSA §5.2.2 (Figures 28–29 wakeup rejection) and
JSA §5.2.3 (Figure 32 Linux `4.19-rt` timer-IRQ mutex rejection) through both the
seven-automaton product and the compiled SEFM 2019 table-driven monitor. -/
theorem milestone5_kernel_trace_replays :
    (publishedSyncModel.run (figure29Trace.take 2) = some publishedSyncModel.q0 ∧
      publishedSyncModel.run figure29Trace = none ∧
      s02.δ (.notify .waking) .enabled = none ∧
      syncMonitor figure29Trace =
        .error (2, coreStateEnum (.enabled, .noIRQ, .thread),
          syncEventEnum (.notify .waking))) ∧
    (publishedSyncModel.run [.irq .localDisable] =
        some (embedCore (.enabled, .masked, .thread)) ∧
      publishedSyncModel.runFrom (embedCore (.enabled, .masked, .thread))
        (figure32Trace.take 3) = some (embedCore (.disabled, .handling, .thread)) ∧
      publishedSyncModel.runFrom (embedCore (.enabled, .masked, .thread))
        figure32Trace = none ∧
      s12.δ (.inr (.lock .mutex .lock)) true = none ∧
      s22.δ (.inr (.lock .mutex .lock)) true = none ∧
      syncMonitor figure32RootedTrace =
        .error (4, coreStateEnum (.disabled, .handling, .thread),
          syncEventEnum (.lock .mutex .lock))) :=
  ⟨⟨rfl, rfl, rfl, figure29_monitor_replay⟩,
    ⟨rfl, rfl, rfl, rfl, rfl, figure32_monitor_replay⟩⟩

/-! ### Main Theorem: End-to-End ISORC 2019 / JSA 2020 Thread Synchronization Verification -/

private theorem published_step_mem_L_iff (w : List SyncEvent) (s : CoreState) (e : SyncEvent)
    (h : publishedSyncModel.run w = some (embedCore s)) :
    w ++ [e] ∈ publishedSyncModel.L ↔ (canonicalSyncModel.δ e s).isSome = true := by
  have hs : canonicalSyncModel.run w = some s := by
    rw [sync_run_agrees] at h
    exact (map_eq_some_iff_inj embedCore_injective (canonicalSyncModel.run w) s).mp h
  change (publishedSyncModel.run (w ++ [e])).isSome = true ↔ _
  rw [sync_run_agrees, run_append_event canonicalSyncModel, hs]
  change (Option.map embedCore (canonicalSyncModel.δ e s)).isSome = true ↔ _
  cases canonicalSyncModel.δ e s <;> rfl

theorem unified_synchronization_laws (w : List SyncEvent) (p : PreemptState)
    (i : IRQState) (c : SchedContext)
    (h : publishedSyncModel.run w = some (embedCore (p, i, c))) :
    (∀ a : Notification,
      w ++ [.notify a] ∈ publishedSyncModel.L ↔ p ≠ .enabled ∧ i ≠ .noIRQ) ∧
    (∀ k : SwitchEvent,
      w ++ [.switch k] ∈ publishedSyncModel.L ↔
        p = .scheduling ∧ i = .masked ∧ c = .scheduler) ∧
    (∀ k a,
      w ++ [.lock k a] ∈ publishedSyncModel.L ↔ i = .noIRQ) ∧
    (w ++ [.scheduler .scheduleEntry] ∈ publishedSyncModel.L ↔
      c = .thread ∧ i ≠ .handling) ∧
    (w ++ [.scheduler .scheduleExit] ∈ publishedSyncModel.L ↔
      c = .scheduler ∧ i ≠ .handling) ∧
    (w ++ [.preempt .enableSched] ∈ publishedSyncModel.L ↔
      p = .scheduling ∧ i ≠ .handling) ∧
    (∀ t : TaskStateEvent,
      w ++ [.taskState t] ∈ publishedSyncModel.L ↔ i ≠ .handling) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a
    rw [published_step_mem_L_iff w (p, i, c) (.notify a) h]
    cases p <;> cases i <;> simp [canonicalSyncModel]
  · intro k
    rw [published_step_mem_L_iff w (p, i, c) (.switch k) h]
    cases p <;> cases i <;> cases c <;> simp [canonicalSyncModel]
  · intro k a
    rw [published_step_mem_L_iff w (p, i, c) (.lock k a) h]
    cases i <;> simp [canonicalSyncModel]
  · rw [published_step_mem_L_iff w (p, i, c) (.scheduler .scheduleEntry) h]
    cases c <;> cases i <;> simp [canonicalSyncModel]
  · rw [published_step_mem_L_iff w (p, i, c) (.scheduler .scheduleExit) h]
    cases c <;> cases i <;> simp [canonicalSyncModel]
  · rw [published_step_mem_L_iff w (p, i, c) (.preempt .enableSched) h]
    cases p <;> cases i <;> simp [canonicalSyncModel]
  · intro t
    rw [published_step_mem_L_iff w (p, i, c) (.taskState t) h]
    cases i <;> simp [canonicalSyncModel]

/-- Main mission theorem for ISORC 2019 / JSA 2020 PREEMPT_RT thread synchronization:
1. The seven-automaton product `publishedSyncModel` is Ramadge–Wonham nonblocking and
   exact-bisimilar to the 18-state trim `canonicalSyncModel`.
2. After every legal prefix, wakeup/need-resched, context-switch, IRQ-locking, and
   IRQ-handler exclusion obey their exact semantic characterizations.
3. For every finite trace, the compiled SEFM 2019 table-driven monitor accepts iff all
   seven component projections accept, and on rejection identifies the exact zero-based
   position, core state, and event where at least one participating component has no
   defined transition. -/
theorem jsa2020_thread_sync_main :
    (publishedSyncModel.CoAccessible ∧
      canonicalSyncModel.IsTrim ∧
      ∀ w, publishedSyncModel.run w = (canonicalSyncModel.run w).map embedCore) ∧
    (∀ w p i c, publishedSyncModel.run w = some (embedCore (p, i, c)) →
      (∀ a : Notification,
        w ++ [.notify a] ∈ publishedSyncModel.L ↔ p ≠ .enabled ∧ i ≠ .noIRQ) ∧
      (∀ k : SwitchEvent,
        w ++ [.switch k] ∈ publishedSyncModel.L ↔
          p = .scheduling ∧ i = .masked ∧ c = .scheduler) ∧
      (∀ k a,
        w ++ [.lock k a] ∈ publishedSyncModel.L ↔ i = .noIRQ) ∧
      (w ++ [.scheduler .scheduleEntry] ∈ publishedSyncModel.L ↔
        c = .thread ∧ i ≠ .handling) ∧
      (w ++ [.scheduler .scheduleExit] ∈ publishedSyncModel.L ↔
        c = .scheduler ∧ i ≠ .handling) ∧
      (w ++ [.preempt .enableSched] ∈ publishedSyncModel.L ↔
        p = .scheduling ∧ i ≠ .handling) ∧
      (∀ t : TaskStateEvent,
        w ++ [.taskState t] ∈ publishedSyncModel.L ↔ i ≠ .handling)) ∧
    (∀ w : List SyncEvent,
      (∀ s, syncMonitor w = .ok (coreStateEnum s) ↔
        publishedSyncModel.run w = some (embedCore s)) ∧
      (∀ idx s e, syncMonitor w = .error (idx, coreStateEnum s, syncEventEnum e) ↔
        ∃ pre post, w = pre ++ e :: post ∧ pre.length = idx ∧
          publishedSyncModel.run pre = some (embedCore s) ∧
          componentBlocked (embedCore s) e)) := by
  refine ⟨⟨publishedSyncModel_nonblocking, canonicalSyncModel_trim, sync_run_agrees⟩,
    unified_synchronization_laws, fun w => ?_⟩
  obtain ⟨hok, herr⟩ :=
    LinuxRV.monitor_correct canonicalSyncModel coreStateEnum syncEventEnum w
  constructor
  · intro s
    erw [syncMonitor, hok s, sync_run_agrees,
      map_eq_some_iff_inj embedCore_injective (canonicalSyncModel.run w) s]
    rfl
  · intro idx s e
    erw [syncMonitor, herr idx s e]
    constructor
    · rintro ⟨pre, post, hw, hlen, hrun, hnone⟩
      refine ⟨pre, post, hw, hlen, ?_, ?_⟩
      · rw [sync_run_agrees, hrun]; rfl
      · rw [← publishedSyncModel_blocked_iff, sync_step_agrees, hnone]; rfl
    · rintro ⟨pre, post, hw, hlen, hrun, hblk⟩
      refine ⟨pre, post, hw, hlen, ?_, ?_⟩
      · rw [sync_run_agrees] at hrun
        exact (map_eq_some_iff_inj embedCore_injective (canonicalSyncModel.run pre) s).mp hrun
      · rw [← publishedSyncModel_blocked_iff, sync_step_agrees] at hblk
        cases hδ : canonicalSyncModel.δ e s with
        | none => rfl
        | some r =>
          rw [hδ] at hblk
          cases hblk

end JSA2020
