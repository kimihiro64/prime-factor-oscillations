import PrimeFactorOscillations.Definitions.GapFrequency
import PrimeFactorOscillations.Helpers.PrimeConsecutive
import PrimeFactorOscillations.Helpers.PrimeWindowTransfer
import PrimeFactorOscillations.Helpers.ReciprocalSmoothBands
import PrimeFactorOscillations.Helpers.ReversalCount

/-! # Actual separated reversal counts from arbitrary short-prime windows -/

set_option autoImplicit false
set_option Elab.async false

open Filter PrimeFactorUnimodality

namespace PrimeFactorOscillations.ReciprocalSmoothLaw

/-- Every sufficiently late collection of short-prime windows in a sharp rank
band gives a quantitatively controlled family of separated real-density reversals.
The collection can be irregular; no dyadic prime-distribution assumption occurs. -/
theorem reversal_counts_of_prime_windows_broad
    (law : ReciprocalSmoothLaw) (H D : Nat) (u v : Real)
    (hu : 0 < u) (hv : 0 < v)
    (hmargin : ((H : Real) + law.nu) * v < 1)
    (hD : 2 / u < (D : Real)) (hHD : H + 1 <= D) :
    exists P : Nat, Filter.Eventually (fun k : Nat => forall X Y : Nat,
      forall S : Finset Nat, S.Nonempty -> P <= X -> Nat.factorial D + 2 <= X ->
      (forall n, Membership.mem S n -> X <= n /\ n + H <= Y) ->
      (forall n, Membership.mem S n ->
        2 <= ((Finset.Icc n (n + H)).filter Nat.Prime).card) ->
      (forall p : Nat, X <= p -> p <= Y ->
        u * k <= Real.log (Real.log (p - 1 : Nat)) /\
          Real.log (Real.log (p - 1 : Nat)) <= v * k) ->
      exists m : Nat, S.card <= 2 * (Nat.factorial D + H) * (m + 1) /\
        HasAtLeastReversals (law.rankDensity k) m) Filter.atTop := by
  choose P hP using law.rank_density_gap_signs_on_broad_band H D u v hu hv hmargin hD
  refine Exists.intro P ?_
  filter_upwards [hP] with k hk
  intro X Y S hS hPX hlarge hrange hwindows hband
  choose m d a hcount hprops hsep using prime_windows_separated_gap_pairs S hS
    (L := D) (H := H) (X := X) (Y := Y) hHD hlarge hrange hwindows
  have hX : 3 <= X := by
    have h := Nat.factorial_pos D
    omega
  have hsigns (i : Nat) (hlo : X <= primeAt i) (hhi : primeAt i <= Y) :
      (primeAt (i + 1) <= primeAt i + H ->
        law.rankDensity k i < law.rankDensity k (i + 1)) /\
      (primeAt i + D <= primeAt (i + 1) ->
        law.rankDensity k (i + 1) < law.rankDensity k i) := by
    have hb := hband (primeAt i) hlo hhi
    exact hk (primeAt i) (primeAt (i + 1)) (hX.trans hlo) (hPX.trans hlo)
      (prime_primeAt i) (prime_primeAt (i + 1))
      (primeAt_strictMono (Nat.lt_succ_self i))
      (fun t htlo hthi => no_prime_between_consecutive_indexed i t htlo hthi) hb.1 hb.2
  have hwitness : forall j : Fin m, IsReversal (law.rankDensity k) (d j) (a j) := by
    intro j
    have hd : d j < a j := (hprops j).1
    have hDX : X <= primeAt (d j) := (hprops j).2.2.2.1
    have hAY : primeAt (a j + 1) <= Y := (hprops j).2.2.2.2
    have hDY : primeAt (d j) <= Y :=
      (primeAt_strictMono.monotone (show d j <= a j + 1 by omega)).trans hAY
    have hAX : X <= primeAt (a j) := hDX.trans (primeAt_strictMono.monotone hd.le)
    have hAY' : primeAt (a j) <= Y :=
      (primeAt_strictMono.monotone (Nat.le_succ (a j))).trans hAY
    have hdesc := (hsigns (d j) hDX hDY).2 (hprops j).2.1
    have hasc := (hsigns (a j) hAX hAY').1 (hprops j).2.2.1
    exact And.intro hd (And.intro hdesc hasc)
  exact Exists.intro m (And.intro hcount
    (Exists.intro d (Exists.intro a (And.intro hwitness hsep))))

/-- The actual cumulative short-gap count loses at most X initial indices and
a fixed factorial-cell multiplicity when converted into separated reversals.
The full upper prime endpoint is Y+H, including the second prime of a short gap. -/
theorem reversal_counts_of_gap_frequency_band
    (law : ReciprocalSmoothLaw) (H D : Nat) (u v : Real)
    (hu : 0 < u) (hv : 0 < v)
    (hmargin : ((H : Real) + law.nu) * v < 1)
    (hD : 2 / u < (D : Real)) (hHD : H + 1 <= D) :
    exists P : Nat, Filter.Eventually (fun k : Nat => forall X Y : Nat,
      P <= X -> Nat.factorial D + 2 <= X ->
      (forall p : Nat, X <= p -> p <= Y + H ->
        u * k <= Real.log (Real.log (p - 1 : Nat)) /\
          Real.log (Real.log (p - 1 : Nat)) <= v * k) ->
      exists m : Nat,
        primeGapFrequencyCount H Y <= X + 2 * (Nat.factorial D + H) * (m + 1) /\
        HasAtLeastReversals (law.rankDensity k) m) Filter.atTop := by
  classical
  choose P hP using law.reversal_counts_of_prime_windows_broad H D u v hu hv hmargin hD hHD
  refine Exists.intro P ?_
  filter_upwards [hP] with k hk
  intro X Y hPX hX hband
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
      let E : Finset Nat := {primeAt i, primeAt (i + 1)}
      have hsub : forall p : Nat, Membership.mem E p ->
          Membership.mem ((Finset.Icc (primeAt i) (primeAt i + H)).filter Nat.Prime) p := by
        intro p hp
        have hpCases : p = primeAt i \/ p = primeAt (i + 1) := by
          simpa only [E, Finset.mem_insert, Finset.mem_singleton] using hp
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
      have hE : E.card = 2 := by simp [E, ne_of_lt hpq]
      have hcount := Finset.card_le_card hsub
      rwa [hE] at hcount
    choose m hm using hk X (Y + H) S hS hPX hX hrange hwindows hband
    refine Exists.intro m (And.intro ?_ hm.2)
    change F.card <= _
    omega
  next =>
    have hzero : S.card = 0 := by
      by_contra hn
      exact hS (Finset.card_pos.mp (by omega))
    refine Exists.intro 0 (And.intro ?_ (hasAtLeastReversals_zero _))
    change F.card <= _
    omega


end PrimeFactorOscillations.ReciprocalSmoothLaw
