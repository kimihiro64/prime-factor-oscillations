import PrimeFactorOscillations.Definitions.GapFrequency
import PrimeFactorOscillations.Helpers.ReversalCount
import PrimeFactorOscillations.Proof.Lower.BroadBandWindowReversals

/-! # Actual bounded-gap counts supply separated reversal families -/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations

open PrimeFactorUnimodality

/-- Convert the actual consecutive-gap count on an arbitrary endpoint into
reversals. Only the initial X possible indices and a fixed factorial-cell
multiplicity are lost. The full prime band includes the right endpoint H. -/
theorem both_reversal_counts_of_gap_frequency_band
    (H L : Nat) (u v : Real) (hu : 0 < u)
    (hmargin : ((H : Real) + 1) * v < 1)
    (hL : 2 / u < (L : Real)) (hHL : H + 1 <= L) :
    exists K : Nat, 4 <= K /\ forall k : Nat, K <= k -> forall X Y : Nat,
      Nat.factorial L + 2 <= X ->
      (forall p : Nat, X <= p -> p <= Y + H ->
        u * k <= Real.log (Real.log (p - 1 : Nat)) /\
          Real.log (Real.log (p - 1 : Nat)) <= v * k) ->
      exists m : Nat,
        primeGapFrequencyCount H Y <= X + 2 * (Nat.factorial L + H) * (m + 1) /\
        HasAtLeastReversals (ordinaryDensity k) m /\
        HasAtLeastReversals (genericOddDensity k) m := by
  classical
  choose K hK using both_reversal_counts_of_prime_windows_broad H L u v hu hmargin hL hHL
  refine Exists.intro K (And.intro hK.1 ?_)
  intro k hk X Y hX hband
  let F := (Finset.range Y).filter (fun i => primeAt i <= Y /\ primeGap i <= H)
  let G := F.filter (fun i => X <= primeAt i)
  let S := G.image primeAt
  have hcover : forall i : Nat, Membership.mem F i ->
      Membership.mem (Union.union (Finset.range X) G) i := by
    intro i hi
    by_cases hXi : X <= primeAt i
    next => exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr (And.intro hi hXi)))
    next =>
      have hbase : i + 2 <= primeAt i := Nat.add_two_le_nth_prime i
      exact Finset.mem_union.mpr (Or.inl (Finset.mem_range.mpr (by omega)))
  have hcard : F.card <= X + S.card := by
    have h1 := Finset.card_le_card hcover
    have h2 := Finset.card_union_le (Finset.range X) G
    have himage : S.card = G.card := Finset.card_image_of_injective G primeAt_strictMono.injective
    rw [Finset.card_range] at h2
    omega
  by_cases hS : S.Nonempty
  next =>
    have hrange : forall n, Membership.mem S n -> X <= n /\ n + H <= Y + H := by
      intro n hn
      choose i hi using Finset.mem_image.mp hn
      have hiG := Finset.mem_filter.mp hi.1
      have hiF := (Finset.mem_filter.mp hiG.1).2
      rw [<- hi.2]
      exact And.intro hiG.2 (Nat.add_le_add_right hiF.1 H)
    have hwindows : forall n, Membership.mem S n ->
        2 <= ((Finset.Icc n (n + H)).filter Nat.Prime).card := by
      intro n hn
      choose i hi using Finset.mem_image.mp hn
      have hiG := Finset.mem_filter.mp hi.1
      have hiF := (Finset.mem_filter.mp hiG.1).2
      have hpq : primeAt i < primeAt (i + 1) := primeAt_strictMono (Nat.lt_succ_self i)
      have hgap : primeAt (i + 1) <= primeAt i + H := by
        have hg := hiF.2
        change primeAt (i + 1) - primeAt i <= H at hg
        omega
      rw [<- hi.2]
      let P : Finset Nat := {primeAt i, primeAt (i + 1)}
      have hsub : forall p : Nat, Membership.mem P p ->
          Membership.mem ((Finset.Icc (primeAt i) (primeAt i + H)).filter Nat.Prime) p := by
        intro p hp
        have hpCases : p = primeAt i \/ p = primeAt (i + 1) := by simpa only [P, Finset.mem_insert,
          Finset.mem_singleton] using hp
        rcases hpCases with hp0 | hp1
        next =>
          rw [hp0]
          exact Finset.mem_filter.mpr (And.intro
            (Finset.mem_Icc.mpr (And.intro (le_refl _) (Nat.le_add_right _ _)))
            (prime_primeAt i))
        next =>
          rw [hp1]
          exact Finset.mem_filter.mpr (And.intro
            (Finset.mem_Icc.mpr (And.intro hpq.le hgap)) (prime_primeAt (i + 1)))
      have hP : P.card = 2 := by simp [P, ne_of_lt hpq]
      have hcount := Finset.card_le_card hsub
      rwa [hP] at hcount
    choose m hm using hK.2 k hk X (Y + H) S hS hX hrange hwindows hband
    refine Exists.intro m (And.intro ?_ hm.2)
    change F.card <= _
    omega
  next =>
    have hzero : S.card = 0 := by
      by_contra hn
      exact hS (Finset.card_pos.mp (by omega))
    refine Exists.intro 0 (And.intro ?_ (And.intro
      (hasAtLeastReversals_zero _) (hasAtLeastReversals_zero _)))
    change F.card <= _
    omega

end PrimeFactorOscillations
