import PrimeFactorOscillations
import PrimeFactorOscillations.Helpers.BoundaryDensity

set_option autoImplicit false

/-! # Kernel-checked implementation of the public Mathlib-only statement -/

/-- The public statement, with the actual unconditional proof. -/
theorem PrimeFactorOscillations.publicDoubleExponentialReversalBounds :
    let density := fun (eta : Nat -> Rat) (k i : Nat) =>
      let p := Nat.nth Nat.Prime i
      eta p * ((Finset.filter Nat.Prime (Finset.range p)).sort
        (fun a b => a <= b)).foldr
          (fun ell (f : Nat -> Rat) => Nat.rec ((1 - eta ell) * f 0)
            (fun j _ => (1 - eta ell) * f (j + 1) + eta ell * f j))
          (Nat.rec (1 : Rat) (fun _ _ => 0)) (k - 1)
    let ordinary := density (fun p => 1 / (p : Rat))
    let odd := density (fun p => if p = 2 then 0 else
      ((p : Rat) - 2) / ((p : Rat) - 1) ^ 2)
    let witnesses := fun (f : Nat -> Rat) (m : Nat) =>
      exists descent ascent : Fin m -> Nat,
        (forall j, descent j < ascent j /\
          f (descent j + 1) < f (descent j) /\ f (ascent j) < f (ascent j + 1)) /\
        (forall i j, i < j -> ascent i + 1 < descent j)
    let maximum := fun (f : Nat -> Rat) (N : Nat) =>
      witnesses f N /\ forall m, witnesses f m -> m <= N
    let bounds := fun (f : Nat -> Rat) (k : Nat) (a epsilon : Real) =>
      exists N : Nat, maximum f N /\
        Real.exp (Real.exp (a * (k : Real))) <= (N : Real) /\
        (N : Real) <= Real.exp (Real.exp (((1 : Real) / 3 + epsilon) * (k : Real)))
    exists a : Real, 0 < a /\
      forall epsilon : Real, 0 < epsilon ->
        exists K : Nat, 1 <= K /\ forall k : Nat, K <= k ->
          bounds (ordinary k) k a epsilon /\ bounds (odd k) k a epsilon := by
  have h := PrimeFactorOscillations.doubleExponentialReversalBounds
  unfold PrimeFactorOscillations.DoubleExponentialReversalBounds
    PrimeFactorOscillations.ReversalBoundsAt PrimeFactorOscillations.HasReversalNumber
    PrimeFactorOscillations.HasAtLeastReversals PrimeFactorOscillations.IsReversal at h
  simpa only [PrimeFactorOscillations.ordinaryDensity_eq_localRankDensity,
    PrimeFactorOscillations.genericOddDensity, PrimeFactorOscillations.localRankDensity_eq_public,
    PrimeFactorOscillations.genericOddEta] using h

open scoped Classical

/-- Actual affine prime-pair density limits and the exact positive reversal spectrum. -/
theorem PrimeFactorOscillations.publicAffinePrimePairSpectrum :
    let prime := fun i : Nat => Nat.nth Nat.Prime i
    let gapCount := fun H X : Nat =>
      ((Finset.range X).filter (fun i : Nat =>
        prime i <= X /\ prime (i + 1) - prime i <= H)).card
    let gamma := fun H : Nat => Filter.limsup (fun X : Nat =>
      Real.log (Real.log (3 + (gapCount H X : Real))) /
        Real.log (Real.log (X : Real))) Filter.atTop
    let witnesses := fun (f : Nat -> Real) (j : Nat) =>
      exists descent ascent : Fin j -> Nat,
        (forall t, descent t < ascent t /\
          f (descent t + 1) < f (descent t) /\ f (ascent t) < f (ascent t + 1)) /\
        (forall s t, s < t -> ascent s + 1 < descent t)
    let maximum := fun (f : Nat -> Real) (j : Nat) =>
      witnesses f j /\ forall h, witnesses f h -> h <= j
    forall m : Nat, 0 < m -> forall c shift : Fin m -> Int,
      (forall j : Fin m, 0 < c j) ->
      (forall i j : Fin m, Not (i = j) -> Not (c i * shift j = c j * shift i)) ->
      let value := fun a b : Nat =>
        Finset.univ.prod (fun j : Fin m => c j * ((a : Int) + b) + shift j)
      exists density : Nat -> Nat -> Real, exists counts : Nat -> Nat,
        (forall k : Nat, 1 <= k -> forall i : Nat,
          Filter.Tendsto (fun X : Nat =>
            (((SProd.sprod (Nat.primesLE X) (Nat.primesLE X)).filter
              (fun ab : Prod Nat Nat =>
                Nat.Prime (prime i) /\ Dvd.dvd (prime i) (value ab.1 ab.2).natAbs /\
                  Not ((value ab.1 ab.2).natAbs = 0) /\
                  (((value ab.1 ab.2).natAbs.primeFactors).filter
                    (fun ell : Nat => ell < prime i)).card = k - 1)).card : Real) /
              (Nat.primeCounting X : Real) ^ 2)
            Filter.atTop (nhds (density k i))) /\
        (forall k : Nat, 1 <= k -> maximum (density k) (counts k)) /\
        Filter.limsup (fun k : Nat =>
          Real.log (Real.log (3 + (counts k : Real))) / k) Filter.atTop =
          sSup (Set.range (fun j : Nat => gamma (j + 2) / ((j : Real) + 2 + m))) /\
        0 < sSup (Set.range (fun j : Nat => gamma (j + 2) / ((j : Real) + 2 + m))) := by
  intro prime gapCount gamma witnesses maximum m hm c shift hc hd value
  have normalize (s : Finset Nat) (P : Nat -> Prop) (d : DecidablePred P) :
      @Finset.filter Nat P d s =
        @Finset.filter Nat P (fun a => Classical.propDecidable (P a)) s :=
    @Finset.filter_congr_decidable Nat s P d (fun a => Classical.propDecidable (P a))
  let F : PrimeFactorOscillations.AffineSumFamily :=
    { arity := m, arity_pos := hm, coeff := c, shift := shift,
      coeff_pos := hc, distinct_roots := hd }
  have hcount (H X : Nat) : PrimeFactorOscillations.primeGapFrequencyCount H X = gapCount H X := by
    unfold PrimeFactorOscillations.primeGapFrequencyCount
    apply congrArg Finset.card
    apply Finset.filter_congr
    intro i hi
    rfl
  have hgamma (H : Nat) : PrimeFactorOscillations.primeGapFrequencyExponent H = gamma H := by
    unfold PrimeFactorOscillations.primeGapFrequencyExponent
    simp only [hcount]
    rfl
  have hspectrum : PrimeFactorOscillations.primeGapSpectrum m =
      sSup (Set.range (fun j : Nat => gamma (j + 2) / ((j : Real) + 2 + m))) := by
    unfold PrimeFactorOscillations.primeGapSpectrum
    simp only [hgamma]
  choose density counts hlim hmax hrate hpos using
    F.exists_sharp_arithmetic_reversal_rate_all_ranks
  refine Exists.intro density (Exists.intro counts
    (And.intro ?_ (And.intro ?_ (And.intro ?_ ?_))))
  intro k hk i
  simpa only [PrimeFactorOscillations.primePairProbability,
    PrimeFactorOscillations.primePairs, PrimeFactorUnimodality.IsKthDistinctPrimeFactor,
    PrimeFactorOscillations.AffineSumFamily.value, PrimeFactorOscillations.AffineSumFamily.eval,
    PrimeFactorUnimodality.primeAt, F, Int.cast_id, value, prime, ne_eq] using hlim k i
  intro k hk
  simpa only [PrimeFactorOscillations.HasReversalNumber,
    PrimeFactorOscillations.HasAtLeastReversals, PrimeFactorOscillations.IsReversal,
    maximum, witnesses] using hmax k
  exact hrate.trans hspectrum
  rw [<- hspectrum]
  exact hpos
