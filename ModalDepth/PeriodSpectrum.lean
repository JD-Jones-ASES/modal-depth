module

public import ModalDepth.Substitution
public import ModalDepth.Transfer
public import ModalDepth.Craig

@[expose] public section

namespace ModalDepth

variable {α β C : Type}

/-- Every multiple of a positive-depth period is again a period. The period
itself may be zero; only the depths at which it is tested must be positive. -/
theorem PositivePeriodic.mul {n : ℕ} {c : ℕ → C}
    (hc : PositivePeriodic n c) (t : ℕ) : PositivePeriodic (n * t) c := by
  intro k hk
  exact hc.add_mul hk t

/-- Divisibility propagates positive-depth periodicity. -/
theorem PositivePeriodic.of_dvd {n m : ℕ} {c : ℕ → C}
    (hc : PositivePeriodic n c) (hnm : n ∣ m) : PositivePeriodic m c := by
  obtain ⟨t, rfl⟩ := hnm
  exact hc.mul t

/-- The remainder of two positive-depth periods is again a period. -/
theorem PositivePeriodic.mod {a b : ℕ} {c : ℕ → C}
    (ha : PositivePeriodic a c) (hb : PositivePeriodic b c) :
    PositivePeriodic (a % b) c := by
  intro k hk
  have hr := hb.add_mul (k := k + a % b) (by omega) (a / b)
  rw [show k + a % b + b * (a / b) = k + a by
    have := Nat.mod_add_div a b
    omega] at hr
  exact hr.symm.trans (ha k hk)

/-- The greatest common divisor of two periods is a period, even though the
label at depth zero is unconstrained. -/
theorem PositivePeriodic.gcd {a b : ℕ} {c : ℕ → C}
    (ha : PositivePeriodic a c) (hb : PositivePeriodic b c) :
    PositivePeriodic (Nat.gcd a b) c := by
  induction a using Nat.strong_induction_on generalizing b with
  | h a ih =>
    by_cases hzero : a = 0
    · subst a
      simpa using hb
    · rw [Nat.gcd_rec]
      exact ih (b % a) (Nat.mod_lt b (Nat.pos_of_ne_zero hzero))
        (hb.mod ha) ha

/-- A common labeling for two periods is exactly a labeling for their gcd. -/
theorem positivePeriodic_gcd_iff (a b : ℕ) (c : ℕ → C) :
    PositivePeriodic a c ∧ PositivePeriodic b c ↔
      PositivePeriodic (Nat.gcd a b) c := by
  constructor
  · rintro ⟨ha, hb⟩
    exact ha.gcd hb
  · intro h
    exact ⟨h.of_dvd (Nat.gcd_dvd_left a b), h.of_dvd (Nat.gcd_dvd_right a b)⟩

/-- The least positive period describes the repeating labels at positive
depths. It imposes no condition at depth zero. -/
def IsLeastPositivePeriod (c : ℕ → C) (p : ℕ) : Prop :=
  0 < p ∧ PositivePeriodic p c ∧
    ∀ q : ℕ, 0 < q → PositivePeriodic q c → p ≤ q

/-- A labeling admitting any positive period has a least positive period. -/
theorem leastPositivePeriod_exists (c : ℕ → C)
    (h : ∃ p : ℕ, 0 < p ∧ PositivePeriodic p c) :
    ∃ p : ℕ, IsLeastPositivePeriod c p := by
  classical
  refine ⟨Nat.find h, (Nat.find_spec h).1, (Nat.find_spec h).2, ?_⟩
  intro q hq hp
  exact Nat.find_min' h ⟨hq, hp⟩

/-- The least positive period divides every period; conversely, each multiple
is a period. This also holds for the vacuous zero period. -/
theorem IsLeastPositivePeriod.period_iff {c : ℕ → C} {p : ℕ}
    (hp : IsLeastPositivePeriod c p) (n : ℕ) :
    PositivePeriodic n c ↔ p ∣ n := by
  constructor
  · intro hn
    have hr : PositivePeriodic (n % p) c := hn.mod hp.2.1
    have he : n % p = 0 := by
      by_contra hne
      have hlo := hp.2.2 (n % p) (Nat.pos_of_ne_zero hne) hr
      have hhi := Nat.mod_lt n hp.1
      omega
    exact Nat.dvd_of_mod_eq_zero he
  · exact hp.2.1.of_dvd

/-- Any two least positive periods agree. -/
theorem IsLeastPositivePeriod.unique {c : ℕ → C} {p q : ℕ}
    (hp : IsLeastPositivePeriod c p) (hq : IsLeastPositivePeriod c q) : p = q :=
  Nat.le_antisymm (hp.2.2 q hq.1 hq.2.1) (hq.2.2 p hp.1 hp.2.1)

/-- A labeling with a positive period has a positive integer whose multiples
are exactly its periods. Least-period uniqueness is proved separately. -/
theorem positivePeriodic_spectrum (c : ℕ → C)
    (h : ∃ p : ℕ, 0 < p ∧ PositivePeriodic p c) :
    ∃ p : ℕ, 0 < p ∧ ∀ n : ℕ, PositivePeriodic n c ↔ p ∣ n := by
  obtain ⟨p, hp⟩ := leastPositivePeriod_exists c h
  exact ⟨p, hp.1, hp.period_iff⟩

/-- One substitution scheme works for both logics exactly when its labels
have the gcd period. This concerns each logic separately. -/
theorem depthSubstitution_pair_iff (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (c : ℕ → C) [Nonempty α] :
    DepthSubstitution a c α β ∧ DepthSubstitution b c α β ↔
      PositivePeriodic (Nat.gcd a b) c := by
  rw [depthSubstitution_iff a ha c, depthSubstitution_iff b hb c,
    positivePeriodic_gcd_iff]

/-- The exact spectrum of Sacchetti parameters for a fixed substitution
scheme is the positive multiples of its least positive-depth period. -/
theorem depthSubstitution_spectrum {c : ℕ → C} {p : ℕ}
    (hp : IsLeastPositivePeriod c p) (n : ℕ) (hn : 0 < n) [Nonempty α] :
    DepthSubstitution n c α β ↔ p ∣ n := by
  rw [depthSubstitution_iff n hn c, hp.period_iff]

/-- Uniform signed interpolation has the same arithmetic spectrum, with the
ordinary interpolation property retained explicitly. -/
theorem uniformSigned_spectrum {c : ℕ → C} {p : ℕ}
    (hp : IsLeastPositivePeriod c p) (n : ℕ) (hn : 0 < n) :
    UniformSigned n c ℕ ↔ SourceULI n ℕ ∧ p ∣ n := by
  rw [uniformSigned_iff n hn c, hp.period_iff]

/-- Signed Craig interpolation has the same least-period spectrum. -/
theorem signedCraig_spectrum {c : ℕ → C} {p : ℕ}
    (hp : IsLeastPositivePeriod c p) (n : ℕ) (hn : 0 < n) :
    SignedCraig n c ℕ ↔ OrdinaryLyndon n ℕ ∧ p ∣ n := by
  rw [signedCraig_iff n hn c, hp.period_iff]

/-- Unsigned Craig interpolation has the same least-period spectrum. -/
theorem unsignedCraig_spectrum {c : ℕ → C} {p : ℕ}
    (hp : IsLeastPositivePeriod c p) (n : ℕ) (hn : 0 < n) :
    UnsignedCraig n c ℕ ↔ OrdinaryCraig n ℕ ∧ p ∣ n := by
  rw [unsignedCraig_iff n hn c, hp.period_iff]

/-- Inclusion between the admissible-label families recovers divisibility of
the logic parameters. Natural-number labels already detect the inclusion. -/
theorem positivePeriodic_inclusion_iff (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    (∀ c : ℕ → ℕ, PositivePeriodic a c → PositivePeriodic b c) ↔ a ∣ b := by
  constructor
  · intro h
    exact (positivePeriodic_mod_iff b a hb ha).mp
      (h (fun d => d % a)
        ((positivePeriodic_mod_iff a a ha ha).mpr (dvd_refl a)))
  · intro hab c hc
    exact hc.of_dvd hab

end ModalDepth
