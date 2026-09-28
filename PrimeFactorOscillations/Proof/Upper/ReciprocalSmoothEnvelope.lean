import PrimeFactorOscillations.Helpers.PrimeConsecutive
import PrimeFactorOscillations.Helpers.ReciprocalSmoothBands
import PrimeFactorOscillations.Helpers.ReversalGapEnvelope

/-! # Simultaneous sharp gap cutoffs for real local-law reversal counts -/

set_option autoImplicit false
set_option Elab.async false

open PrimeFactorUnimodality

namespace PrimeFactorOscillations.ReciprocalSmoothLaw

private theorem indexed_descent_above_gap_scale
    (law : ReciprocalSmoothLaw) (H : Nat) (a : Real)
    (ha : 1 / ((H : Real) + law.nu) < a) :
    exists K Q : Nat, 2 <= K /\ 3 <= Q /\
      forall k : Nat, K <= k -> forall i : Nat, Q <= primeAt i ->
      primeAt i + H <= primeAt (i + 1) ->
      a * k <= Real.log (Real.log (primeAt i - 1 : Nat)) ->
      law.rankDensity k (i + 1) < law.rankDensity k i := by
  have hd : 0 < (H : Real) + law.nu :=
    add_pos_of_nonneg_of_pos (Nat.cast_nonneg H) law.nu_pos
  have ha0 : 0 < a := (div_pos (by norm_num) hd).trans ha
  have hm := mul_lt_mul_of_pos_right ha hd
  have hc : (1 / ((H : Real) + law.nu)) * ((H : Real) + law.nu) = (1 : Real) := by
    field_simp
  rw [hc] at hm
  have hmargin : 1 < ((H : Real) + law.nu) * a := by simpa only [mul_comm] using hm
  choose P hP using law.rank_density_descent_beyond_gap_scale H a ha0 hmargin
  choose K hK using Filter.eventually_atTop.mp hP
  refine Exists.intro (max K 2) (Exists.intro (max P 3)
    (And.intro (le_max_right _ _) (And.intro (le_max_right _ _) ?_)))
  intro k hk i hi hgap hscale
  have hk0 : K <= k := (le_max_left K 2).trans hk
  have hp : P <= primeAt i := (le_max_left P 3).trans hi
  have hp3 : 3 <= primeAt i := (le_max_right P 3).trans hi
  exact hK k hk0 (primeAt i) (primeAt (i + 1)) hp3 hp
    (prime_primeAt i) (prime_primeAt (i + 1))
    (primeAt_strictMono (Nat.lt_succ_self i))
    (fun t htlo hthi => no_prime_between_consecutive_indexed i t htlo hthi) hgap hscale

/-- Every gap retains its own H+nu cutoff before the finite count is summed.
Exceptional cutoffs are made uniform only over the fixed finite gap range. -/
theorem reversal_count_le_sharp_gap_envelope
    (law : ReciprocalSmoothLaw) (J : Nat) (u epsilon : Real)
    (hu : 1 / ((J : Real) + 1 + law.nu) < u) (he : 0 < epsilon) :
    exists K Q : Nat, 2 <= K /\ 3 <= Q /\
      forall k : Nat, K <= k -> forall T : Nat, Q <= T ->
      u * k <= Real.log (Real.log (T - 1 : Nat)) ->
      forall U : Nat -> Nat,
      (forall g : Nat, g <= J -> Q <= U g /\
        (1 / ((g : Real) + law.nu) + epsilon) * k <=
          Real.log (Real.log (U g - 1 : Nat))) ->
      forall m : Nat, HasAtLeastReversals (law.rankDensity k) m ->
        m <= T + Finset.sum (Finset.range (J + 1))
          (fun g => ((Finset.range (U g)).filter
            (fun i => primeAt i <= U g /\ primeGap i <= g)).card) := by
  choose K0 Q0 h0 using indexed_descent_above_gap_scale law (J + 1) u
    (by simpa only [Nat.cast_add, Nat.cast_one] using hu)
  choose Ks Qs hs using (fun g : Nat => indexed_descent_above_gap_scale law g
    (1 / ((g : Real) + law.nu) + epsilon) (by linarith only [he]))
  let K := max K0 ((Finset.range (J + 1)).sup Ks)
  let Q := max Q0 ((Finset.range (J + 1)).sup Qs)
  have hK0 : K0 <= K := le_max_left _ _
  have hQ0 : Q0 <= Q := le_max_left _ _
  have hK : 2 <= K := h0.1.trans hK0
  have hQ : 3 <= Q := h0.2.1.trans hQ0
  refine Exists.intro K (Exists.intro Q (And.intro hK (And.intro hQ ?_)))
  intro k hk T hQT hscale U hU m hm
  have hcover : forall i : Nat, law.rankDensity k i < law.rankDensity k (i + 1) ->
      primeAt i <= T \/ exists g : Nat, g <= J /\
        primeAt i <= U g /\ primeGap i <= g := by
    intro i ha
    by_cases hpT : primeAt i <= T
    next => exact Or.inl hpT
    next =>
      have hTp : T <= primeAt i := by omega
      have hpQ : Q <= primeAt i := hQT.trans hTp
      have hmonoLog : forall N : Nat, 3 <= N -> N <= primeAt i ->
          Real.log (Real.log (N - 1 : Nat)) <=
            Real.log (Real.log (primeAt i - 1 : Nat)) := by
        intro N hN hNp
        have hNpos : (1 : Real) < ((N - 1 : Nat) : Real) := by
          exact_mod_cast (show 1 < N - 1 by omega)
        have hpref : ((N - 1 : Nat) : Real) <= ((primeAt i - 1 : Nat) : Real) := by
          exact_mod_cast Nat.sub_le_sub_right hNp 1
        exact Real.log_le_log (Real.log_pos hNpos)
          (Real.log_le_log (lt_trans (by norm_num) hNpos) hpref)
      have hscaleP := hscale.trans (hmonoLog T (hQ.trans hQT) hTp)
      have hsmall : primeGap i <= J := by
        by_contra hn
        have hbig : primeAt i + (J + 1) <= primeAt (i + 1) := by
          have hpq : primeAt i <= primeAt (i + 1) :=
            (primeAt_strictMono (Nat.lt_succ_self i)).le
          change Not (primeAt (i + 1) - primeAt i <= J) at hn
          omega
        have hd := h0.2.2 k (hK0.trans hk) i (hQ0.trans hpQ) hbig hscaleP
        exact (not_lt_of_ge hd.le) ha
      let g := primeGap i
      have hg : g <= J := hsmall
      have hgmem : Membership.mem (Finset.range (J + 1)) g :=
        Finset.mem_range.mpr (by omega)
      have hgK : Ks g <= K :=
        (Finset.le_sup (f := Ks) hgmem).trans (le_max_right _ _)
      have hgQ : Qs g <= Q :=
        (Finset.le_sup (f := Qs) hgmem).trans (le_max_right _ _)
      have hpU : primeAt i <= U g := by
        by_contra hn
        have hUp : U g <= primeAt i := by omega
        have hband := (hU g hg).2.trans (hmonoLog (U g) (hQ.trans (hU g hg).1) hUp)
        have hbig : primeAt i + g <= primeAt (i + 1) := by
          have hpq : primeAt i <= primeAt (i + 1) :=
            (primeAt_strictMono (Nat.lt_succ_self i)).le
          change primeAt i + (primeAt (i + 1) - primeAt i) <= primeAt (i + 1)
          omega
        have hd := (hs g).2.2 k (hgK.trans hk) i (hgQ.trans hpQ) hbig hband
        exact (not_lt_of_ge hd.le) ha
      exact Or.inr (Exists.intro g (And.intro hg (And.intro hpU (le_refl _))))
  exact PrimeFactorOscillations.reversal_count_le_gap_envelope
    (law.rankDensity k) T J m U hcover hm

end PrimeFactorOscillations.ReciprocalSmoothLaw
