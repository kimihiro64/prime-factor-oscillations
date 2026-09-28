import PrimeFactorOscillations.Helpers.PrimeWindowTransfer
import PrimeFactorOscillations.Proof.Lower.AdditiveBandSigns

/-! # Finite separated reversals on sharp rank bands -/

/-! # Finite prime-window counts produce actual separated density reversals -/

namespace PrimeFactorOscillations

open PrimeFactorUnimodality

/-- Actual prime-window counts yield reversal families for both density laws. -/
theorem both_reversal_counts_of_prime_windows_additive (H : Nat) (b : Real)
    (hb : 1 / (2 * ((H : Real) + 1)) < b)
    (hmargin : ((H : Real) + 1) * b < 1) :
    exists K : Nat, 4 <= K /\ forall k : Nat, K <= k -> forall X Y : Nat,
      forall S : Finset Nat, S.Nonempty -> Nat.factorial (4 * (H + 1)) + 2 <= X ->
      (forall n, Membership.mem S n -> X <= n /\ n + H <= Y) ->
      (forall n, Membership.mem S n ->
        2 <= ((Finset.Icc n (n + H)).filter Nat.Prime).card) ->
      (forall p : Nat, X <= p -> p <= Y ->
        b * k - Real.log 2 <=
            Real.log (Real.log (p - 1 : Nat)) /\
          Real.log (Real.log (p - 1 : Nat)) <=
            b * k + Real.log 2) ->
      exists m : Nat, S.card <= 2 * (Nat.factorial (4 * (H + 1)) + H) * (m + 1) /\
        HasAtLeastReversals (ordinaryDensity k) m /\
        HasAtLeastReversals (genericOddDensity k) m := by
  choose K hK using both_density_gap_signs_eventually_on_additive_band H b hb hmargin
  refine Exists.intro K (And.intro hK.1 ?_)
  intro k hk X Y S hS hlarge hrange hwindows hband
  have hgaps := prime_windows_separated_gap_pairs S hS
    (L := 4 * (H + 1)) (H := H) (X := X) (Y := Y)
    (by omega) hlarge hrange hwindows
  choose m d a hcount hprops hsep using hgaps
  have hX : 2 < X := by
    have hfac := Nat.factorial_pos (4 * (H + 1))
    omega
  have hwitness : forall i : Fin m,
      IsReversal (ordinaryDensity k) (d i) (a i) /\
        IsReversal (genericOddDensity k) (d i) (a i) := by
    intro i
    have hd : d i < a i := (hprops i).1
    have hDX : X <= primeAt (d i) := (hprops i).2.2.2.1
    have hAY : primeAt (a i + 1) <= Y := (hprops i).2.2.2.2
    have hDY : primeAt (d i) <= Y :=
      (primeAt_strictMono.monotone (show d i <= a i + 1 by omega)).trans hAY
    have hAX : X <= primeAt (a i) :=
      hDX.trans (primeAt_strictMono.monotone hd.le)
    have hAY' : primeAt (a i) <= Y :=
      (primeAt_strictMono.monotone (Nat.le_succ (a i))).trans hAY
    have hbandD := hband (primeAt (d i)) hDX hDY
    have hbandA := hband (primeAt (a i)) hAX hAY'
    have hdesc := (hK.2 k hk (d i) (hX.trans_le hDX) hbandD.1 hbandD.2).2
      (hprops i).2.1
    have hasc := (hK.2 k hk (a i) (hX.trans_le hAX) hbandA.1 hbandA.2).1
      (hprops i).2.2.1
    exact And.intro (And.intro hd (And.intro hdesc.2 hasc.2))
      (And.intro hd (And.intro hdesc.1 hasc.1))
  exact Exists.intro m (And.intro hcount (And.intro
    (Exists.intro d (Exists.intro a (And.intro (fun i => (hwitness i).1) hsep)))
    (Exists.intro d (Exists.intro a (And.intro (fun i => (hwitness i).2) hsep)))))

end PrimeFactorOscillations
