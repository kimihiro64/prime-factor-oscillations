import PrimeFactorOscillations.Helpers.PrimeWindowTransfer
import PrimeFactorOscillations.Proof.Lower.BroadBandSigns

/-! # Arbitrary-interval prime-window counts give separated broad-band reversals -/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations

open PrimeFactorUnimodality

/-- An irregular collection of short prime windows on a broad rank band gives
actual separated reversal families. No dyadic distribution hypothesis is used. -/
theorem both_reversal_counts_of_prime_windows_broad
    (H L : Nat) (u v : Real) (hu : 0 < u)
    (hmargin : ((H : Real) + 1) * v < 1)
    (hL : 2 / u < (L : Real)) (hHL : H + 1 <= L) :
    exists K : Nat, 4 <= K /\ forall k : Nat, K <= k -> forall X Y : Nat,
      forall S : Finset Nat, S.Nonempty -> Nat.factorial L + 2 <= X ->
      (forall n, Membership.mem S n -> X <= n /\ n + H <= Y) ->
      (forall n, Membership.mem S n ->
        2 <= ((Finset.Icc n (n + H)).filter Nat.Prime).card) ->
      (forall p : Nat, X <= p -> p <= Y ->
        u * k <= Real.log (Real.log (p - 1 : Nat)) /\
          Real.log (Real.log (p - 1 : Nat)) <= v * k) ->
      exists m : Nat, S.card <= 2 * (Nat.factorial L + H) * (m + 1) /\
        HasAtLeastReversals (ordinaryDensity k) m /\
        HasAtLeastReversals (genericOddDensity k) m := by
  choose K hK using both_density_gap_signs_eventually_on_broad_band H L u v hu hmargin hL
  refine Exists.intro K (And.intro hK.1 ?_)
  intro k hk X Y S hS hlarge hrange hwindows hband
  have hgaps := prime_windows_separated_gap_pairs S hS
    (L := L) (H := H) (X := X) (Y := Y)
    hHL hlarge hrange hwindows
  choose m d a hcount hprops hsep using hgaps
  have hX : 2 < X := by
    have hfac := Nat.factorial_pos L
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
