import PrimeFactorOscillations.Helpers.ReversalGapEnvelope
import PrimeFactorOscillations.Proof.Upper.GapScaleCutoff

/-! # Simultaneous sharp prime-gap cutoffs for reversal counting -/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations

open PrimeFactorUnimodality

/-- Keep every gap's own sharp cutoff before summing the finite frequency
envelope. All exceptional cutoffs are uniform over the fixed finite gap range. -/
theorem both_reversal_count_le_sharp_gap_envelope
    (J : Nat) (u epsilon : Real)
    (hu : 1 / ((J : Real) + 2) < u) (he : 0 < epsilon) :
    exists K Q : Nat, 2 <= K /\ 3 <= Q /\
      forall k : Nat, K <= k -> forall T : Nat, Q <= T ->
      u * k <= Real.log (Real.log (T - 1 : Nat)) ->
      forall U : Nat -> Nat,
      (forall g : Nat, g <= J -> Q <= U g /\
        (1 / ((g : Real) + 1) + epsilon) * k <=
          Real.log (Real.log (U g - 1 : Nat))) ->
      forall m : Nat,
        (HasAtLeastReversals (ordinaryDensity k) m \/
          HasAtLeastReversals (genericOddDensity k) m) ->
        m <= T + Finset.sum (Finset.range (J + 1))
          (fun g => ((Finset.range (U g)).filter
            (fun i => primeAt i <= U g /\ primeGap i <= g)).card) := by
  choose K0 Q0 h0 using both_densities_eventually_descend_above_gap_scale (J + 1) u
    (by simpa only [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using hu)
  choose Ks Qs hs using (fun g : Nat =>
    both_densities_eventually_descend_above_gap_scale g
      (1 / ((g : Real) + 1) + epsilon) (by linarith))
  let K := max K0 ((Finset.range (J + 1)).sup Ks)
  let Q := max Q0 ((Finset.range (J + 1)).sup Qs)
  have hK0 : K0 <= K := le_max_left _ _
  have hQ0 : Q0 <= Q := le_max_left _ _
  have hK : 2 <= K := h0.1.trans hK0
  have hQ : 3 <= Q := h0.2.1.trans hQ0
  refine Exists.intro K (Exists.intro Q (And.intro hK (And.intro hQ ?_)))
  intro k hk T hQT hscale U hU m hm
  have hcover : forall i : Nat,
      (ordinaryDensity k i < ordinaryDensity k (i + 1) \/
        genericOddDensity k i < genericOddDensity k (i + 1)) ->
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
        rcases ha with ho | hg
        next => exact (not_lt_of_ge hd.2.le) ho
        next => exact (not_lt_of_ge hd.1.le) hg
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
        rcases ha with ho | hgeneric
        next => exact (not_lt_of_ge hd.2.le) ho
        next => exact (not_lt_of_ge hd.1.le) hgeneric
      exact Or.inr (Exists.intro g (And.intro hg (And.intro hpU (le_refl _))))
  rcases hm with ho | hg
  next =>
    exact reversal_count_le_gap_envelope (ordinaryDensity k) T J m U
      (fun i hi => hcover i (Or.inl hi)) ho
  next =>
    exact reversal_count_le_gap_envelope (genericOddDensity k) T J m U
      (fun i hi => hcover i (Or.inr hi)) hg

end PrimeFactorOscillations
