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

/-- The actual theta-centered moving-rank criterion, with both directions proved. -/
theorem PrimeFactorOscillations.publicMovingRankRHCriterion
    (alpha : Real) (ha : 0 < alpha) :
    RiemannHypothesis <-> Filter.Eventually (fun N : Nat =>
      let L := Real.eulerMascheroniConstant +
        Real.log (Real.log (Chebyshev.theta (N : Real)))
      let r := Nat.floor (alpha * L)
      (PrimeFactorUnimodality.densityRatio
        (PrimeFactorUnimodality.primesBelow (N + 1)) r : Real) <
        Nat.factorialConvolution primeProfileRealCoefficient (r - 1) L /
          Nat.factorialConvolution primeProfileRealCoefficient r L) Filter.atTop := by
  exact PrimeFactorOscillations.riemannHypothesis_iff_eventually_densityRatio_thetaClock_lt_reference
    alpha ha

/-- RH characterized by the actual corrected theta-tail integral. -/
theorem PrimeFactorOscillations.publicThetaTailRHCriterion :
    RiemannHypothesis <-> Filter.Eventually (fun x : Real =>
      MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Ioi x)) (fun t : Real =>
        (Chebyshev.theta t - t) *
          ((1 / Real.log t + 1 / (Real.log t) ^ 2) / t ^ 2)) < 0) Filter.atTop := by
  exact PrimeFactorOscillations.riemannHypothesis_iff_eventually_thetaTailIntegral_neg

/-- RH characterized by the clock of the actual finite prime product. -/
theorem PrimeFactorOscillations.publicPrimeProductClockRHCriterion :
    RiemannHypothesis <-> Filter.Eventually (fun x : Real =>
      Chebyshev.theta x <
        Real.exp (Real.exp (-Real.eulerMascheroniConstant) /
          (Nat.primesLE (Nat.floor x)).prod (fun p => 1 - 1 / (p : Real))))
      Filter.atTop := by
  simpa only [PrimeFactorOscillations.nicolasPrimeProductClock,
    Robin1984.nicolasMertensProduct] using
    PrimeFactorOscillations.riemannHypothesis_iff_eventually_theta_lt_primeProductClock

/-- Uniform full-profile linearization for the actual density ratio at real cutoffs. -/
theorem PrimeFactorOscillations.publicDensityRatioLinearization
    (b : Real) (hb : 0 < b) :
    exists r0 : Nat, exists K : Real, 0 < r0 /\ 0 <= K /\
      Filter.Eventually (fun x : Real =>
        let L := Real.eulerMascheroniConstant + Real.log (Real.log (Chebyshev.theta x))
        let F := Robin1984.nicolasLogMertensOscillation x
        1 < Chebyshev.theta x /\ 2 <= L /\
        forall r : Nat, r0 <= r -> (r : Real) / L <= b ->
          0 < (PrimeFactorUnimodality.weightEsymm
            (PrimeFactorUnimodality.primesBelow (Nat.floor x + 1)) r : Real) /\
          0 < Nat.factorialConvolution primeProfileRealCoefficient r L /\
          abs ((PrimeFactorUnimodality.densityRatio
              (PrimeFactorUnimodality.primesBelow (Nat.floor x + 1)) r : Real) -
            Nat.factorialConvolution primeProfileRealCoefficient (r - 1) L /
              Nat.factorialConvolution primeProfileRealCoefficient r L -
            ((r : Real) / L ^ 2) * F) <=
              K * (abs F / L ^ 2 + 1 / ((r : Real) * x))) Filter.atTop := by
  exact PrimeFactorOscillations.exists_eventually_densityRatio_real_thetaClock_linearization b hb

/-- Under RH, every sufficiently late compact-band ascent meets its actual gap threshold. -/
theorem PrimeFactorOscillations.publicRHAscentReferenceBound
    (hRH : RiemannHypothesis) (a b : Real) (ha : 0 < a) (hab : a <= b) :
    exists Q : Nat, 3 <= Q /\ forall i : Nat,
      Q <= PrimeFactorUnimodality.primeAt i ->
      let L := Real.eulerMascheroniConstant +
        Real.log (Real.log (Chebyshev.theta
          ((PrimeFactorUnimodality.primeAt i - 1 : Nat) : Real)))
      forall k : Nat, a <= ((k - 1 : Nat) : Real) / L ->
        ((k - 1 : Nat) : Real) / L <= b ->
        ordinaryDensity k i < ordinaryDensity k (i + 1) ->
        (PrimeFactorUnimodality.primeGap i : Real) + 1 <
          Nat.factorialConvolution primeProfileRealCoefficient (k - 2) L /
            Nat.factorialConvolution primeProfileRealCoefficient (k - 1) L := by
  exact PrimeFactorOscillations.ordinary_ascent_reference_gap_bound_of_RH hRH a b ha hab

/-- Each positive reference level has a unique crossing within a fixed distance of rank/level. -/
theorem PrimeFactorOscillations.publicReferenceCrossing (s : Real) (hs : 0 < s) :
    exists (A : Real) (r0 : Nat), 0 < A /\ 0 < r0 /\
      forall r : Nat, r0 <= r ->
        ExistsUnique (fun u : Real =>
          Set.Icc ((r : Real) / s - A) ((r : Real) / s + A) u /\
          Nat.factorialConvolution primeProfileRealCoefficient (r - 1) u /
            Nat.factorialConvolution primeProfileRealCoefficient r u = s) := by
  choose A r0 hA hr0 hroot using
    PrimeFactorOscillations.exists_primeProfile_reference_local_crossing s hs
  refine Exists.intro A (Exists.intro r0 (And.intro hA (And.intro hr0 ?_)))
  intro r hr
  choose u hu heq hunique using (hroot r hr).2
  refine ExistsUnique.intro u (And.intro (And.intro hu.1.le hu.2.le) heq) ?_
  intro v hv
  exact hunique v hv.1 hv.2

/-- Under RH, the reference crossing bounds every ordinary ascent at large rank. -/
theorem PrimeFactorOscillations.publicRHAllAscentEnvelope (hRH : RiemannHypothesis) :
    exists (A : Real) (K : Nat), 0 < A /\ 2 <= K /\
      forall k : Nat, K <= k -> exists u : Real,
        Set.Ioo (((k - 1 : Nat) : Real) / 3 - A)
          (((k - 1 : Nat) : Real) / 3 + A) u /\
        Nat.factorialConvolution primeProfileRealCoefficient (k - 2) u /
          Nat.factorialConvolution primeProfileRealCoefficient (k - 1) u = 3 /\
        forall i : Nat, ordinaryDensity k i < ordinaryDensity k (i + 1) ->
          Chebyshev.theta ((PrimeFactorUnimodality.primeAt i - 1 : Nat) : Real) <
            Real.exp (Real.exp (u - Real.eulerMascheroniConstant)) := by
  exact PrimeFactorOscillations.exists_ordinary_ascent_theta_envelope_of_RH hRH

/-- The actual last ordinary ascent and reversal maximum obey the RH reference capacity. -/
theorem PrimeFactorOscillations.publicRHLastAscentAndCapacity (hRH : RiemannHypothesis) :
    exists (c A : Real) (K : Nat), 0 < c /\ 0 < A /\ 2 <= K /\
      forall k : Nat, K <= k -> exists N i : Nat, exists u : Real,
        HasReversalNumber (ordinaryDensity k) N /\
        Real.exp (Real.exp (c * (k : Real))) <= (N : Real) /\
        ordinaryDensity k i < ordinaryDensity k (i + 1) /\
        (forall j : Nat, ordinaryDensity k j < ordinaryDensity k (j + 1) -> j <= i) /\
        Set.Ioo (((k - 1 : Nat) : Real) / 3 - A)
          (((k - 1 : Nat) : Real) / 3 + A) u /\
        Nat.factorialConvolution primeProfileRealCoefficient (k - 2) u /
          Nat.factorialConvolution primeProfileRealCoefficient (k - 1) u = 3 /\
        Chebyshev.theta ((PrimeFactorUnimodality.primeAt i - 1 : Nat) : Real) <
          Real.exp (Real.exp (u - Real.eulerMascheroniConstant)) /\
        N <= Nat.primeCounting (PrimeFactorUnimodality.primeAt i) /\
        Nat.primeCounting (PrimeFactorUnimodality.primeAt i) <=
          primeThetaEndpointCount (Real.exp (Real.exp (u - Real.eulerMascheroniConstant))) := by
  exact PrimeFactorOscillations.exists_ordinary_last_ascent_and_capacity_of_RH hRH

/-- The actual last-ascent lower location estimate is unconditional. -/
theorem PrimeFactorOscillations.publicLastAscentLowerLocation :
    exists c : Real, 0 < c /\ forall epsilon : Real, 0 < epsilon ->
      exists K : Nat, 2 <= K /\ forall k : Nat, K <= k ->
        exists N i : Nat,
          HasReversalNumber (ordinaryDensity k) N /\
          Real.exp (Real.exp (c * (k : Real))) <= (N : Real) /\
          ordinaryDensity k i < ordinaryDensity k (i + 1) /\
          (forall j : Nat, ordinaryDensity k j < ordinaryDensity k (j + 1) -> j <= i) /\
          N <= Nat.primeCounting (PrimeFactorUnimodality.primeAt i) /\
          (1 - epsilon) * (N : Real) * Real.log (N : Real) <=
            Chebyshev.theta ((PrimeFactorUnimodality.primeAt i - 1 : Nat) : Real) := by
  exact PrimeFactorOscillations.ordinary_eventually_last_ascent_lower_location

/-- The actual last ordinary ascent lies between the PNT lower location and the RH reference. -/
theorem PrimeFactorOscillations.publicRHLastAscentLocationSandwich (hRH : RiemannHypothesis) :
    exists c A : Real, 0 < c /\ 0 < A /\
      forall epsilon : Real, 0 < epsilon -> exists K : Nat, 2 <= K /\
        forall k : Nat, K <= k -> exists N i : Nat, exists u : Real,
          HasReversalNumber (ordinaryDensity k) N /\
          Real.exp (Real.exp (c * (k : Real))) <= (N : Real) /\
          ordinaryDensity k i < ordinaryDensity k (i + 1) /\
          (forall j : Nat, ordinaryDensity k j < ordinaryDensity k (j + 1) -> j <= i) /\
          Set.Ioo (((k - 1 : Nat) : Real) / 3 - A)
            (((k - 1 : Nat) : Real) / 3 + A) u /\
          Nat.factorialConvolution primeProfileRealCoefficient (k - 2) u /
            Nat.factorialConvolution primeProfileRealCoefficient (k - 1) u = 3 /\
          (1 - epsilon) * (N : Real) * Real.log (N : Real) <=
            Chebyshev.theta ((PrimeFactorUnimodality.primeAt i - 1 : Nat) : Real) /\
          Chebyshev.theta ((PrimeFactorUnimodality.primeAt i - 1 : Nat) : Real) <
            Real.exp (Real.exp (u - Real.eulerMascheroniConstant)) /\
          N <= Nat.primeCounting (PrimeFactorUnimodality.primeAt i) /\
          Nat.primeCounting (PrimeFactorUnimodality.primeAt i) <=
            primeThetaEndpointCount (Real.exp (Real.exp (u - Real.eulerMascheroniConstant))) := by
  exact PrimeFactorOscillations.exists_ordinary_last_ascent_location_sandwich_of_RH hRH

/-- The actual reversal maximum satisfies the PNT-normalized RH endpoint capacity. -/
theorem PrimeFactorOscillations.publicRHLastAscentAsymptoticCapacity (hRH : RiemannHypothesis) :
    exists c A : Real, 0 < c /\ 0 < A /\
      forall epsilon : Real, 0 < epsilon -> exists K : Nat, 2 <= K /\
        forall k : Nat, K <= k -> exists N i : Nat, exists u : Real,
          HasReversalNumber (ordinaryDensity k) N /\
          Real.exp (Real.exp (c * (k : Real))) <= (N : Real) /\
          ordinaryDensity k i < ordinaryDensity k (i + 1) /\
          (forall j : Nat, ordinaryDensity k j < ordinaryDensity k (j + 1) -> j <= i) /\
          Set.Ioo (((k - 1 : Nat) : Real) / 3 - A)
            (((k - 1 : Nat) : Real) / 3 + A) u /\
          Nat.factorialConvolution primeProfileRealCoefficient (k - 2) u /
            Nat.factorialConvolution primeProfileRealCoefficient (k - 1) u = 3 /\
          (1 - epsilon) * (N : Real) * Real.log (N : Real) <=
            Chebyshev.theta ((PrimeFactorUnimodality.primeAt i - 1 : Nat) : Real) /\
          Chebyshev.theta ((PrimeFactorUnimodality.primeAt i - 1 : Nat) : Real) <
            Real.exp (Real.exp (u - Real.eulerMascheroniConstant)) /\
          N <= Nat.primeCounting (PrimeFactorUnimodality.primeAt i) /\
          Nat.primeCounting (PrimeFactorUnimodality.primeAt i) <=
            primeThetaEndpointCount (Real.exp (Real.exp (u - Real.eulerMascheroniConstant))) /\
          (N : Real) <= (1 + epsilon) *
            (Real.exp (Real.exp (u - Real.eulerMascheroniConstant)) /
              Real.log (Real.exp (Real.exp (u - Real.eulerMascheroniConstant)))) := by
  exact PrimeFactorOscillations.exists_ordinary_last_ascent_asymptotic_capacity_of_RH hRH

/-- Each fixed positive reference level has the actual logarithmic-derivative root shift. -/
theorem PrimeFactorOscillations.publicSharpReferenceCrossing (s : Real) (hs : 0 < s) :
    exists (A C : Real) (r0 : Nat), 0 < A /\ 0 <= C /\ 0 < r0 /\
      forall r : Nat, r0 <= r -> exists u : Real,
        Set.Ioo ((r : Real) / s - A) ((r : Real) / s + A) u /\
        Nat.factorialConvolution primeProfileRealCoefficient (r - 1) u /
          Nat.factorialConvolution primeProfileRealCoefficient r u = s /\
        abs (u - (r : Real) / s +
          deriv (fun x : Real => (primeProfile (x : Complex)).re) s /
            (primeProfile (s : Complex)).re) <= C / (r : Real) /\
        forall v : Real, Set.Icc ((r : Real) / s - A) ((r : Real) / s + A) v ->
          Nat.factorialConvolution primeProfileRealCoefficient (r - 1) v /
            Nat.factorialConvolution primeProfileRealCoefficient r v = s -> v = u := by
  exact PrimeFactorOscillations.exists_primeProfile_reference_sharp_crossing s hs

/-- The same actual last-ascent RH envelope retains the sharp reference-root displacement. -/
theorem PrimeFactorOscillations.publicRHLastAscentSharpReference (hRH : RiemannHypothesis) :
    exists c A C : Real, 0 < c /\ 0 < A /\ 0 <= C /\
      forall epsilon : Real, 0 < epsilon -> exists K : Nat, 2 <= K /\
        forall k : Nat, K <= k -> exists N i : Nat, exists u : Real,
          HasReversalNumber (ordinaryDensity k) N /\
          Real.exp (Real.exp (c * (k : Real))) <= (N : Real) /\
          ordinaryDensity k i < ordinaryDensity k (i + 1) /\
          (forall j : Nat, ordinaryDensity k j < ordinaryDensity k (j + 1) -> j <= i) /\
          Set.Ioo (((k - 1 : Nat) : Real) / 3 - A)
            (((k - 1 : Nat) : Real) / 3 + A) u /\
          Nat.factorialConvolution primeProfileRealCoefficient (k - 2) u /
            Nat.factorialConvolution primeProfileRealCoefficient (k - 1) u = 3 /\
          (1 - epsilon) * (N : Real) * Real.log (N : Real) <=
            Chebyshev.theta ((PrimeFactorUnimodality.primeAt i - 1 : Nat) : Real) /\
          Chebyshev.theta ((PrimeFactorUnimodality.primeAt i - 1 : Nat) : Real) <
            Real.exp (Real.exp (u - Real.eulerMascheroniConstant)) /\
          N <= Nat.primeCounting (PrimeFactorUnimodality.primeAt i) /\
          Nat.primeCounting (PrimeFactorUnimodality.primeAt i) <=
            primeThetaEndpointCount (Real.exp (Real.exp (u - Real.eulerMascheroniConstant))) /\
          (N : Real) <= (1 + epsilon) *
            (Real.exp (Real.exp (u - Real.eulerMascheroniConstant)) /
              Real.log (Real.exp (Real.exp (u - Real.eulerMascheroniConstant)))) /\
          abs (u - ((k - 1 : Nat) : Real) / 3 +
            deriv (fun x : Real => (primeProfile (x : Complex)).re) 3 /
              (primeProfile (3 : Complex)).re) <= C / ((k - 1 : Nat) : Real) := by
  exact PrimeFactorOscillations.exists_ordinary_last_ascent_sharp_reference_of_RH hRH

/-- Uniform second-order expansion of the actual prime-profile coefficients. -/
theorem PrimeFactorOscillations.publicPrimeProfileSecondOrderExpansion (b : Real) (hb : 0 <= b) :
    exists C : Real, 0 <= C /\
      forall r : Nat, 0 < r -> forall t : Real, 0 <= t -> t <= b ->
        abs (Nat.normalizedDescFactorialPolynomial primeProfileRealCoefficient r t -
          (primeProfile (t : Complex)).re +
          (t ^ 2 * deriv (deriv (fun x : Real => (primeProfile (x : Complex)).re)) t) /
            (2 * r)) <= C / (r : Real) ^ 2 := by
  exact PrimeFactorOscillations.exists_primeProfile_normalized_secondOrder_error b hb

/-- The actual prime endpoint capacity has the sharp reference normalization at every positive level. -/
theorem PrimeFactorOscillations.publicReferenceLogCapacity (s : Real) (hs : 0 < s) :
    exists (A C : Real) (r0 : Nat), 0 < A /\ 0 <= C /\ 0 < r0 /\
      forall r : Nat, r0 <= r -> exists u : Real,
        Set.Ioo ((r : Real) / s - A) ((r : Real) / s + A) u /\
        Nat.factorialConvolution primeProfileRealCoefficient (r - 1) u /
          Nat.factorialConvolution primeProfileRealCoefficient r u = s /\
        abs (u - (r : Real) / s +
          deriv (fun x : Real => (primeProfile (x : Complex)).re) s /
            (primeProfile (s : Complex)).re) <= C / (r : Real) /\
        1 < (primeThetaEndpointCount
          (Real.exp (Real.exp (u - Real.eulerMascheroniConstant))) : Real) /\
        abs (Real.log (Real.log (primeThetaEndpointCount
          (Real.exp (Real.exp (u - Real.eulerMascheroniConstant))) : Real)) -
            ((r : Real) / s - Real.eulerMascheroniConstant -
              deriv (fun x : Real => (primeProfile (x : Complex)).re) s /
                (primeProfile (s : Complex)).re)) <= (C + 32 * s) / (r : Real) /\
        forall v : Real, Set.Icc ((r : Real) / s - A) ((r : Real) / s + A) v ->
          Nat.factorialConvolution primeProfileRealCoefficient (r - 1) v /
            Nat.factorialConvolution primeProfileRealCoefficient r v = s -> v = u := by
  exact PrimeFactorOscillations.exists_primeProfile_reference_loglog_capacity s hs

/-- Under RH the actual attained reversal maximum obeys the sharp second-log bound. -/
theorem PrimeFactorOscillations.publicRHReversalCountLogBound (hRH : RiemannHypothesis) :
    exists c D : Real, 0 < c /\ 0 <= D /\ exists K : Nat, 2 <= K /\
      forall k : Nat, K <= k -> exists N : Nat,
        HasReversalNumber (ordinaryDensity k) N /\
        Real.exp (Real.exp (c * (k : Real))) <= (N : Real) /\
        Real.log (Real.log (N : Real)) <=
          ((k - 1 : Nat) : Real) / 3 - Real.eulerMascheroniConstant -
            deriv (fun x : Real => (primeProfile (x : Complex)).re) 3 /
              (primeProfile (3 : Complex)).re + D / ((k - 1 : Nat) : Real) := by
  choose c A C hc hA hC hbase using
    PrimeFactorOscillations.exists_ordinary_last_ascent_loglog_capacity_of_RH hRH
  choose K hK hdata using hbase 1 (by norm_num)
  refine Exists.intro c (Exists.intro (C + 96)
    (And.intro hc (And.intro (by linarith) (Exists.intro K (And.intro hK ?_)))))
  intro k hk
  choose N i u hN hlo hi hlast hu heq hLower htheta hcount hcapacity hupper hshift hBerror hNbound
    using hdata k hk
  exact Exists.intro N (And.intro hN (And.intro hlo hNbound))

/-- Under RH, the exact eligible-gap count accommodates every reversal and the lower supply. -/
theorem PrimeFactorOscillations.publicRHGapFilteredCounts (hRH : RiemannHypothesis) :
    exists c : Real, 0 < c /\ forall a : Real, 0 < a -> a < c ->
      exists K : Nat, 2 <= K /\ forall k : Nat, K <= k ->
        0 < ordinaryReferenceEligibleCount k (Real.exp (Real.exp (a * (k : Real))))
          (Nat.ceil (Real.exp (Real.exp ((k : Real) / 2))) + 1) /\
        Real.exp (Real.exp (c * (k : Real))) - Real.exp (Real.exp (a * (k : Real))) <=
          (ordinaryReferenceEligibleCount k (Real.exp (Real.exp (a * (k : Real))))
            (Nat.ceil (Real.exp (Real.exp ((k : Real) / 2))) + 1) : Real) /\
        forall m : Nat, HasAtLeastReversals (ordinaryDensity k) m ->
          m <= Nat.primeCounting (Nat.floor (Real.exp (Real.exp (a * (k : Real))))) +
            ordinaryReferenceEligibleCount k (Real.exp (Real.exp (a * (k : Real))))
              (Nat.ceil (Real.exp (Real.exp ((k : Real) / 2))) + 1) := by
  choose c hc hsupply using
    PrimeFactorOscillations.ordinary_reference_eligible_supply_of_RH hRH
  refine Exists.intro c (And.intro hc ?_)
  intro a ha hac
  choose K0 hK0 h0 using hsupply a ha hac
  choose K1 hK1 h1 using
    PrimeFactorOscillations.ordinary_reversal_count_reference_bound_of_RH hRH a ha
  refine Exists.intro (max K0 K1) (And.intro (hK0.trans (le_max_left _ _)) ?_)
  intro k hk
  have hlate := h0 k ((le_max_left _ _).trans hk)
  exact And.intro hlate.1 (And.intro hlate.2 (h1 k ((le_max_right _ _).trans hk)))

/-- The full weighted-psi spectral expansion, with an explicit uniform remainder. -/
theorem PrimeFactorOscillations.publicRHSpectralPsiExpansion (hRH : RiemannHypothesis)
    {x : Real} (hx : max 3 (Real.exp 1) <= x) :
    nicolasZeroWave x =
      (tsum (fun p : RiemannXiDivisorZeroIndex =>
        (x : Complex) ^ ((riemannXiDivisorZeroValue p).im * Complex.I) /
          (riemannXiDivisorZeroValue p * (1 - riemannXiDivisorZeroValue p)))).re /\
    abs (nicolasZeroWave x) <= Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi) /\
    abs (Robin1984.nicolasJ x + nicolasZeroWave x /
        (x ^ (1 / 2 : Real) * Real.log x)) <=
      (5 * (Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi)) +
        2 * Real.log (2 * Real.pi)) *
          x ^ (-(1 / 2 : Real)) * Inv.inv ((Real.log x) ^ 2) := by
  have hx3 : 3 <= x := (le_max_left _ _).trans hx
  have hx1 : 1 < x := by linarith
  have hlog : 1 <= Real.log x := by
    have h := Real.log_le_log (Real.exp_pos 1) ((le_max_right _ _).trans hx)
    simpa only [Real.log_exp] using h
  exact And.intro (PrimeFactorOscillations.nicolasZeroWave_eq_spectral_sum hRH hx1)
    (And.intro (PrimeFactorOscillations.abs_nicolasZeroWave_le hRH hx1)
      (PrimeFactorOscillations.nicolasJ_wave_uniform_error hRH hx3 hlog))

/-- RH gives the full theta-tail spectral term, including the prime-square constant two. -/
theorem PrimeFactorOscillations.publicRHThetaSpectralExpansion (hRH : RiemannHypothesis)
    {x : Real} (hx : max 4 (Real.exp 1) <= x) :
    nicolasZeroWave x =
      (tsum (fun p : RiemannXiDivisorZeroIndex =>
        (x : Complex) ^ ((riemannXiDivisorZeroValue p).im * Complex.I) /
          (riemannXiDivisorZeroValue p * (1 - riemannXiDivisorZeroValue p)))).re /\
    abs (nicolasZeroWave x) <= Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi) /\
    abs (Robin1984.nicolasK x + (2 + nicolasZeroWave x) /
        (x ^ (1 / 2 : Real) * Real.log x)) <=
      (10 + 45 * (Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi)) +
        4 * Real.log (2 * Real.pi) + (Real.log 4 + 4) * (79 / 3 : Real)) *
          x ^ (-(1 / 2 : Real)) * Inv.inv ((Real.log x) ^ 2) := by
  have hx4 : 4 <= x := (le_max_left _ _).trans hx
  have hx1 : 1 < x := by linarith
  have hlog : 1 <= Real.log x := by
    have h := Real.log_le_log (Real.exp_pos 1) ((le_max_right _ _).trans hx)
    simpa only [Real.log_exp] using h
  exact And.intro (PrimeFactorOscillations.nicolasZeroWave_eq_spectral_sum hRH hx1)
    (And.intro (PrimeFactorOscillations.abs_nicolasZeroWave_le hRH hx1)
      (PrimeFactorOscillations.nicolasK_wave_uniform_error hRH hx4 hlog))

/-- One constant controls every degree of the weighted psi error under RH. -/
theorem PrimeFactorOscillations.publicRHDegreeErrorBound (hRH : RiemannHypothesis)
    {n : Nat} (hn : 2 <= n) {x : Real} (hx : max 2 (Real.exp 1) <= x) :
    abs (Robin1984.robinPsiWeightedErrorIntegral n x) <=
      nicolasDegreeErrorConstant * Real.sqrt (n : Real) *
        (x ^ ((1 / 2 : Real) - n) * Inv.inv (Real.log x)) := by
  have hlog : 1 <= Real.log x := by
    have h := Real.log_le_log (Real.exp_pos 1) ((le_max_right _ _).trans hx)
    simpa only [Real.log_exp] using h
  exact PrimeFactorOscillations.abs_nicolasDegreeError_le hRH hn
    ((le_max_left _ _).trans hx) hlog

/-- RH gives pointwise power-saving control sufficient for the nonlinear log-log correction. -/
theorem PrimeFactorOscillations.publicRHPointwisePowerBound (hRH : RiemannHypothesis)
    {x : Real} (hx : max 4 (2 * Real.exp 1) <= x) :
    abs (Chebyshev.psi x - x) <=
        (1 + 12 * (abs nicolasDegreeErrorConstant + 1)) * x ^ (2 / 3 : Real) /\
    abs (Chebyshev.theta x - x) <=
        (13 + 12 * (abs nicolasDegreeErrorConstant + 1)) * x ^ (2 / 3 : Real) := by
  have hx4 : 4 <= x := (le_max_left _ _).trans hx
  have hhalf : Real.exp 1 <= x / 2 := by
    have h := (le_max_right 4 (2 * Real.exp 1)).trans hx
    linarith only [h]
  have hL : 1 <= Real.log (x / 2) := by
    have h := Real.log_le_log (Real.exp_pos 1) hhalf
    simpa only [Real.log_exp] using h
  exact And.intro (PrimeFactorOscillations.abs_nicolasPsiError_le_two_thirds hRH hx4 hL)
    (PrimeFactorOscillations.abs_nicolasThetaError_le_two_thirds hRH hx4 hL)

/-- The full finite Nicolas logarithm has the same canonical spectral wave under RH. -/
theorem PrimeFactorOscillations.publicRHLogSpectralExpansion (hRH : RiemannHypothesis) :
    exists C : Real, 0 < C /\ exists X : Real, forall x : Real, X <= x ->
      nicolasZeroWave x =
        (tsum (fun p : RiemannXiDivisorZeroIndex =>
          (x : Complex) ^ ((riemannXiDivisorZeroValue p).im * Complex.I) /
            (riemannXiDivisorZeroValue p * (1 - riemannXiDivisorZeroValue p)))).re /\
      abs (nicolasZeroWave x) <= Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi) /\
      abs (Robin1984.nicolasLogMertensOscillation x + (2 + nicolasZeroWave x) /
        (x ^ (1 / 2 : Real) * Real.log x)) <=
          C * x ^ (-(1 / 2 : Real)) * Inv.inv ((Real.log x) ^ 2) := by
  choose X hX using Filter.eventually_atTop.mp
    (PrimeFactorOscillations.eventually_nicolasLog_wave_uniform_error hRH)
  refine Exists.intro nicolasLogSpectralConstant
    (And.intro PrimeFactorOscillations.nicolasLogSpectralConstant_pos
      (Exists.intro (max X 2) ?_))
  intro x hx
  have hx1 : 1 < x := by
    have h := (le_max_right X 2).trans hx
    linarith
  exact And.intro (PrimeFactorOscillations.nicolasZeroWave_eq_spectral_sum hRH hx1)
    (And.intro (PrimeFactorOscillations.abs_nicolasZeroWave_le hRH hx1)
      (hX x ((le_max_left _ _).trans hx)))

/-- RH locates the actual prime-product clock about theta on the square-root scale. -/
theorem PrimeFactorOscillations.publicRHSpatialClockExpansion (hRH : RiemannHypothesis) :
    Filter.Tendsto (fun x : Real =>
      (nicolasPrimeProductClock x - Chebyshev.theta x) / x ^ (1 / 2 : Real) -
        (2 + nicolasZeroWave x)) Filter.atTop (nhds 0) /\
    forall epsilon : Real, 0 < epsilon -> exists X : Real, forall x : Real, X <= x ->
      (2 - (Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi)) - epsilon) *
          x ^ (1 / 2 : Real) <= nicolasPrimeProductClock x - Chebyshev.theta x /\
      nicolasPrimeProductClock x - Chebyshev.theta x <=
        (2 + (Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi)) + epsilon) *
          x ^ (1 / 2 : Real) := by
  have hLimit := PrimeFactorOscillations.tendsto_nicolasPrimeProductClock_normalized_error hRH
  refine And.intro hLimit ?_
  intro epsilon he
  have hSmall : Filter.Eventually (fun x : Real =>
      abs ((nicolasPrimeProductClock x - Chebyshev.theta x) / x ^ (1 / 2 : Real) -
        (2 + nicolasZeroWave x)) < epsilon) Filter.atTop := by
    filter_upwards [hLimit.eventually (Metric.ball_mem_nhds (0 : Real) he)] with x hx
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hx
  have hBands : Filter.Eventually (fun x : Real =>
      (2 - (Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi)) - epsilon) *
          x ^ (1 / 2 : Real) <= nicolasPrimeProductClock x - Chebyshev.theta x /\
      nicolasPrimeProductClock x - Chebyshev.theta x <=
        (2 + (Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi)) + epsilon) *
          x ^ (1 / 2 : Real)) Filter.atTop := by
    filter_upwards [hSmall, Filter.eventually_ge_atTop (2 : Real)] with x hx hx2
    have hx1 : 1 < x := by linarith
    have hRoot : 0 < x ^ (1 / 2 : Real) := Real.rpow_pos_of_pos (by linarith) _
    have hWave := PrimeFactorOscillations.abs_nicolasZeroWave_le hRH hx1
    have hLower :
        2 - (Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi)) - epsilon <=
          (nicolasPrimeProductClock x - Chebyshev.theta x) / x ^ (1 / 2 : Real) := by
      linarith only [(abs_le.mp hx.le).1, (abs_le.mp hWave).1]
    have hUpper :
        (nicolasPrimeProductClock x - Chebyshev.theta x) / x ^ (1 / 2 : Real) <=
          2 + (Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi)) + epsilon := by
      linarith only [(abs_le.mp hx.le).2, (abs_le.mp hWave).2]
    have hCancel : (nicolasPrimeProductClock x - Chebyshev.theta x) /
        x ^ (1 / 2 : Real) * x ^ (1 / 2 : Real) =
          nicolasPrimeProductClock x - Chebyshev.theta x := by field_simp
    have hlo := mul_le_mul_of_nonneg_right hLower hRoot.le
    have hhi := mul_le_mul_of_nonneg_right hUpper hRoot.le
    rw [hCancel] at hlo hhi
    exact And.intro hlo hhi
  exact Filter.eventually_atTop.mp hBands


/-- Spatial sign tests at the unique local reference crossing for width h. -/
theorem PrimeFactorOscillations.publicLocalDensityRatioThreshold
    (h : Nat) (D : Real) (hD : 1 <= D) :
    exists A : Real, exists r0 N0 : Nat, exists K : Real,
      0 < A /\ 0 < r0 /\ 2 <= N0 /\ 0 <= K /\
      forall r : Nat, r0 <= r -> exists L : Real,
        Set.Ioo ((r : Real) / ((h : Real) + 1) - A) ((r : Real) / ((h : Real) + 1) + A) L /\
        Nat.factorialConvolution primeProfileRealCoefficient (r - 1) L /
          Nat.factorialConvolution primeProfileRealCoefficient r L = ((h : Real) + 1) /\
        (forall v : Real,
          Set.Icc ((r : Real) / ((h : Real) + 1) - A) ((r : Real) / ((h : Real) + 1) + A) v ->
          Nat.factorialConvolution primeProfileRealCoefficient (r - 1) v /
            Nat.factorialConvolution primeProfileRealCoefficient r v = ((h : Real) + 1) -> v = L) /\
        forall N : Nat, N0 <= N ->
          let B := (primeProfilePrefixSet N).sum
            (fun p => Real.log (1 + primeProfileWeight (p : Nat)))
          Set.Icc ((r : Real) / ((h : Real) + 1) - A) ((r : Real) / ((h : Real) + 1) + A) B ->
          nicolasPrimeProductClock (N : Real) <= D * (N : Real) ->
          Real.exp (Real.exp (L - Real.eulerMascheroniConstant)) <= D * (N : Real) ->
          0 < (PrimeFactorUnimodality.weightEsymm
            (PrimeFactorUnimodality.primesBelow (N + 1)) r : Real) /\
          (K * Real.log (N : Real) <
              Real.exp (Real.exp (L - Real.eulerMascheroniConstant)) -
                nicolasPrimeProductClock (N : Real) ->
            ((h : Real) + 1) < (PrimeFactorUnimodality.densityRatio
              (PrimeFactorUnimodality.primesBelow (N + 1)) r : Real)) /\
          (K * Real.log (N : Real) <
              nicolasPrimeProductClock (N : Real) -
                Real.exp (Real.exp (L - Real.eulerMascheroniConstant)) ->
            (PrimeFactorUnimodality.densityRatio
              (PrimeFactorUnimodality.primesBelow (N + 1)) r : Real) < ((h : Real) + 1)) := by
  exact PrimeFactorOscillations.exists_densityRatio_local_spatial_threshold
    ((h : Real) + 1) D (by positivity) hD


/-- Every fixed positive theta-centered prime-product tilt has the RH criterion. -/
theorem PrimeFactorOscillations.publicTiltedPrimeProductCriterion
    (z : Real) (hz : 0 < z) :
    RiemannHypothesis <-> Filter.Eventually (fun x : Real =>
      Real.exp (z * Real.eulerMascheroniConstant + Real.log (primeProfile (z : Complex)).re) *
        (Real.log (Chebyshev.theta x)) ^ z /
          (primeProfilePrefixSet (Nat.floor x)).prod
            (fun p => 1 + primeProfileWeight (p : Nat) * z) < 1) Filter.atTop := by
  exact PrimeFactorOscillations.riemannHypothesis_iff_eventually_nicolasTiltedProduct_lt_one z hz


/-- One eventual cutoff works simultaneously for every positive tilt. -/
theorem PrimeFactorOscillations.publicAllPositiveTiltedPrimeProductCriterion :
    RiemannHypothesis <-> Filter.Eventually (fun x : Real =>
      forall z : Real, 0 < z ->
        Real.exp (z * Real.eulerMascheroniConstant + Real.log (primeProfile (z : Complex)).re) *
          (Real.log (Chebyshev.theta x)) ^ z /
            (primeProfilePrefixSet (Nat.floor x)).prod
              (fun p => 1 + primeProfileWeight (p : Nat) * z) < 1) Filter.atTop := by
  exact PrimeFactorOscillations.riemannHypothesis_iff_eventually_all_positive_tiltedProducts_lt_one


/-- Exact tilted logarithmic tail and both signs, with the inclusive prime cutoff. -/
theorem PrimeFactorOscillations.publicTiltedLogTail
    (N : Nat) (z : Real) (hz : 0 <= z)
    (hTheta : 1 < Chebyshev.theta (N : Real)) :
    nicolasTiltedLog z (N : Real) =
      z * Robin1984.nicolasLogMertensOscillation (N : Real) +
        tsum (fun p : {p : Nat.Primes // N < (p : Nat)} =>
          Real.log (1 + primeProfileWeight (p.val : Nat) * z) -
            Real.log (1 + primeProfileWeight (p.val : Nat)) * z) /\
    (z <= 1 -> z * Robin1984.nicolasLogMertensOscillation (N : Real) <=
      nicolasTiltedLog z (N : Real)) /\
    (1 <= z -> nicolasTiltedLog z (N : Real) <=
      z * Robin1984.nicolasLogMertensOscillation (N : Real)) := by
  have hId := PrimeFactorOscillations.nicolasTiltedLog_nat_eq_components z hz N hTheta
  refine And.intro ?_ (And.intro ?_ ?_)
  . exact hId.trans (congrArg
      (fun u : Real => z * Robin1984.nicolasLogMertensOscillation (N : Real) + u)
      (PrimeFactorOscillations.primeProfile_log_tail_eq_tsum N z hz))
  . intro hzOne
    have h := PrimeFactorOscillations.primeProfile_log_tail_nonneg N z hz hzOne
    linarith only [hId, h]
  . intro hzOne
    have h := PrimeFactorOscillations.primeProfile_log_tail_nonpos N z hzOne
    linarith only [hId, h]

/-- Exact positive tilted kernel, with an explicit integrable difference. -/
theorem PrimeFactorOscillations.publicTiltedKernelComparison
    (z t : Real) (hz : 0 <= z) (ht : 2 <= t) (hlog : 1 <= Real.log t) :
    HasDerivAt (fun s : Real => Real.log (1 + z / (s - 1)) / Real.log s)
      (-nicolasTiltedKernel z t) t /\
    (0 < z -> 0 < nicolasTiltedKernel z t) /\
    |nicolasTiltedKernel z t - z * Robin1984.nicolasTailKernel t| <=
      14 * (z + z ^ 2) / (t ^ 3 * Real.log t) := by
  exact And.intro (hasDerivAt_nicolasTiltedWeight hz (by linarith))
    (And.intro (fun h => nicolasTiltedKernel_pos h (by linarith))
      (nicolasTiltedKernel_error hz ht hlog))

/-- The explicit weighted integral has the fixed-positive-tilt RH criterion. -/
theorem PrimeFactorOscillations.publicTiltedIntegralCriterion
    (z : Real) (hz : 0 < z) :
    let I : Real -> Real := fun x =>
      MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Ioi x)) (fun t : Real =>
        (Chebyshev.theta t - t) *
          (z / ((t - 1) * (t - 1 + z) * Real.log t) +
            Real.log (1 + z / (t - 1)) / (t * (Real.log t) ^ 2)))
    (forall x : Real, 3 <= x ->
      |I x - z * Robin1984.nicolasK x| <=
        (Real.log 4 + 5) * 14 * (z + z ^ 2) / (x * Real.log x)) /\
    (RiemannHypothesis <-> Filter.Eventually (fun x : Real => I x < 0) Filter.atTop) := by
  change (forall x : Real, 3 <= x ->
    |nicolasTiltedIntegral z x - z * Robin1984.nicolasK x| <=
      nicolasTiltedIntegralErrorConstant z / (x * Real.log x)) /\
    (RiemannHypothesis <-> Filter.Eventually
      (fun x : Real => nicolasTiltedIntegral z x < 0) Filter.atTop)
  exact And.intro (fun _ hx => nicolasTiltedIntegral_error hz.le hx)
    (riemannHypothesis_iff_eventually_nicolasTiltedIntegral_neg z hz)

/-- The complete tilted integral inherits the prime-square bias and zero wave. -/
theorem PrimeFactorOscillations.publicTiltedIntegralSpectralExpansion
    (hRH : RiemannHypothesis) (z : Real) (hz : 0 <= z) :
    (forall x : Real, 4 <= x -> 1 <= Real.log x ->
      |nicolasTiltedIntegral z x * (x ^ (1 / 2 : Real) * Real.log x) +
        z * (2 + nicolasZeroWave x)| <=
          nicolasTiltedIntegralErrorConstant z * x ^ (-(1 / 2 : Real)) +
            z * nicolasThetaWaveErrorConstant / Real.log x) /\
    Filter.Tendsto (fun x : Real =>
      nicolasTiltedIntegral z x * (x ^ (1 / 2 : Real) * Real.log x) +
        z * (2 + nicolasZeroWave x)) Filter.atTop (nhds 0) := by
  exact And.intro (fun _ hx hlog =>
    nicolasTiltedIntegral_wave_normalized_error hRH hz hx hlog)
      (tendsto_nicolasTiltedIntegral_wave_error hRH z hz)

/-- The complete prime-power tail has leading coefficient two without RH. -/
theorem PrimeFactorOscillations.publicPrimePowerTailAsymptotic :
    Filter.Tendsto (fun x : Real =>
      (MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Ioi x)) (fun t : Real =>
        (Chebyshev.psi t - Chebyshev.theta t) *
          ((1 / Real.log t + 1 / (Real.log t) ^ 2) / t ^ 2))) *
        (x ^ (1 / 2 : Real) * Real.log x)) Filter.atTop (nhds 2) := by
  exact PrimeFactorOscillations.tendsto_nicolasPrimePowerTail_scaled

/-- Every admissible zero-dependent exponent has both signed integral excursions. -/
theorem PrimeFactorOscillations.publicZeroDependentIntegralExcursions
    (rho : Complex) (hZero : riemannZeta rho = 0)
    (hHalf : (1 / 2 : Real) < rho.re) (hOne : rho.re < 1)
    (b : Real) (hLower : 1 - rho.re < b) (hbHalf : b <= 1 / 2)
    (z : Real) (hz : 0 < z) :
    forall X A : Real,
      (exists x : Real, max X 3 < x /\ A * x ^ (-b) < Robin1984.nicolasJ x) /\
      (exists x : Real, max X 3 < x /\ A * x ^ (-b) < -Robin1984.nicolasJ x) /\
      (exists x : Real, max X 3 < x /\ A * x ^ (-b) < Robin1984.nicolasK x) /\
      (exists x : Real, max X 3 < x /\ A * x ^ (-b) < -Robin1984.nicolasK x) /\
      (exists x : Real, max X 3 < x /\ A * x ^ (-b) < nicolasTiltedIntegral z x) /\
      (exists x : Real, max X 3 < x /\ A * x ^ (-b) < -nicolasTiltedIntegral z x) := by
  intro X A
  have hK := nicolasK_two_sided_power_excursions_of_zero hZero hHalf hOne hLower hbHalf X A
  have hI := nicolasTiltedIntegral_two_sided_power_excursions_of_zero
    hZero hHalf hOne hLower hbHalf z hz X A
  exact And.intro (nicolasJ_arbitrary_positive_excursions_of_zero
    hZero hHalf hOne hLower hbHalf X A)
    (And.intro (nicolasJ_arbitrary_negative_excursions_of_zero
      hZero hHalf hOne hLower hbHalf X A)
      (And.intro hK.1 (And.intro hK.2 hI)))

/-- False RH supplies one exponent for every fixed positive tilted integral. -/
theorem PrimeFactorOscillations.publicFalseRHWeightedIntegralExcursions
    (hNotRH : Not RiemannHypothesis) :
    exists b : Real, 0 < b /\ b < 1 / 2 /\
      forall z : Real, 0 < z -> forall X A : Real,
        (exists x : Real, max X 3 < x /\ A * x ^ (-b) < nicolasTiltedIntegral z x) /\
        (exists x : Real, max X 3 < x /\ A * x ^ (-b) < -nicolasTiltedIntegral z x) := by
  choose rho hZero hHalf hOne using
    Robin1984.exists_riemannZeta_zero_re_gt_half_of_not_riemannHypothesis hNotRH
  let b : Real := ((1 - rho.re) + 1 / 2) / 2
  have hb : 0 < b := by dsimp [b]; linarith
  have hbHalf : b < 1 / 2 := by dsimp [b]; linarith
  have hLower : 1 - rho.re < b := by dsimp [b]; linarith
  refine Exists.intro b (And.intro hb (And.intro hbHalf ?_))
  intro z hz X A
  exact nicolasTiltedIntegral_two_sided_power_excursions_of_zero
    hZero hHalf hOne hLower hbHalf.le z hz X A

/-- The canonical xi function has a fixed logarithmic growth bound, without RH. -/
theorem PrimeFactorOscillations.publicXiLogarithmicGrowth :
    Exists fun C : Real => And (0 < C) (forall z : Complex,
      Real.log (1 + norm (Complex.riemannXi z)) <=
        C * (1 + norm z) * Real.log (2 + norm z)) := by
  exact PrimeFactorOscillations.nicolasXi_log_growth

/-- The multiplicity-indexed xi zeros have an unconditional logarithmic count. -/
theorem PrimeFactorOscillations.publicXiZeroCounting :
    Exists fun C : Real => And (0 < C) (forall R : Real, 1 <= R ->
      And (Finite {p : RiemannXiDivisorZeroIndex //
        norm (riemannXiDivisorZeroValue p) <= R})
      ((Nat.card {p : RiemannXiDivisorZeroIndex //
        norm (riemannXiDivisorZeroValue p) <= R} : Real) <=
          C * R * Real.log (R + 2))) := by
  choose C hC hCount using nicolasXi_zero_count_logarithmic
  exact Exists.intro C (And.intro hC (fun R hR =>
    And.intro (nicolasXi_finite_zero_ball R) (hCount R hR)))

/-- The full multiplicity-indexed degree coefficient has a uniform RH bound. -/
theorem PrimeFactorOscillations.publicRHWeightedZeroCoefficientBound
    (hRH : RiemannHypothesis) :
    Exists fun C : Real => And (0 < C) (forall n : Nat, 2 <= n ->
      tsum (fun p : RiemannXiDivisorZeroIndex =>
        (n : Real) / (norm (riemannXiDivisorZeroValue p) *
          norm ((n : Complex) - riemannXiDivisorZeroValue p))) <=
        C * (Real.log ((n : Real) + 2)) ^ (2 : Nat)) := by
  choose C hC hBound using exists_nicolasZeroCoefficient_log_bound hRH
  refine Exists.intro C (And.intro hC ?_)
  intro n hn
  have h := hBound n hn
  have hEq :
      tsum (fun p : RiemannXiDivisorZeroIndex =>
        norm (((n : Complex) / ((n : Complex) - riemannXiDivisorZeroValue p)) /
          riemannXiDivisorZeroValue p)) =
        tsum (fun p : RiemannXiDivisorZeroIndex =>
          (n : Real) / (norm (riemannXiDivisorZeroValue p) *
            norm ((n : Complex) - riemannXiDivisorZeroValue p))) := by
    apply tsum_congr
    intro p
    rw [norm_div, norm_div, Complex.norm_natCast]
    ring
  rwa [hEq] at h

/-- Both classical RH pointwise error bounds, with a common endpoint constant. -/
theorem PrimeFactorOscillations.publicRHPointwiseLogarithmicBound
    (hRH : RiemannHypothesis) :
    Exists fun C : Real => And (0 < C) (forall x : Real, 4 <= x ->
      1 <= Real.log (x / 2) ->
      abs (Chebyshev.psi x - x) <= C * Real.sqrt x * (Real.log x) ^ (2 : Nat) /\
      abs (Chebyshev.theta x - x) <= C * Real.sqrt x * (Real.log x) ^ (2 : Nat)) := by
  choose C hC hPsi using exists_nicolasPsiError_le_sqrt_log_sq hRH
  choose D hD hTheta using exists_nicolasThetaError_le_sqrt_log_sq hRH
  refine Exists.intro (C + D) (And.intro (by linarith) ?_)
  intro x hx hL
  have hFactor : 0 <= Real.sqrt x * (Real.log x) ^ (2 : Nat) := by positivity
  have hP := mul_le_mul_of_nonneg_right (show C <= C + D by linarith) hFactor
  have hT := mul_le_mul_of_nonneg_right (show D <= C + D by linarith) hFactor
  exact And.intro (by nlinarith only [hPsi x hx hL, hP])
    (by nlinarith only [hTheta x hx hL, hT])

/-- RH controls the actual signed endpoint correction and the finite-product
difference from its theta integral at the logarithm-cubed over endpoint scale. -/
theorem PrimeFactorOscillations.publicRHLogarithmicCorrection
    (hRH : RiemannHypothesis) :
    (Exists fun C : Real => And (0 < C)
      (Filter.Eventually (fun x : Real =>
        0 <= nicolasHeightTangentError x /\
        nicolasHeightTangentError x <= C * (Real.log x) ^ (3 : Nat) / x) Filter.atTop)) /\
    (Exists fun C : Real => And (0 < C)
      (Filter.Eventually (fun x : Real =>
        abs (Robin1984.nicolasLogMertensOscillation x - Robin1984.nicolasK x) <=
          C * (Real.log x) ^ (3 : Nat) / x) Filter.atTop)) := by
  exact And.intro (exists_eventually_nicolasHeightTangentError_log_bound hRH)
    (exists_eventually_nicolasLog_sub_K_le_log_cube hRH)

/-- Every admissible zero-dependent exponent gives both signs for the actual
finite-product logarithm, including its nonlinear endpoint correction. -/
theorem PrimeFactorOscillations.publicZeroDependentLogarithmExcursions
    (rho : Complex) (hZero : riemannZeta rho = 0)
    (hHalf : (1 / 2 : Real) < rho.re) (hOne : rho.re < 1)
    (b : Real) (hLower : 1 - rho.re < b) (hbHalf : b <= 1 / 2) :
    forall X A : Real,
      (exists x : Real, max X 3 < x /\
        A * x ^ (-b) < Robin1984.nicolasLogMertensOscillation x) /\
      (exists x : Real, max X 3 < x /\
        A * x ^ (-b) < -Robin1984.nicolasLogMertensOscillation x) := by
  exact nicolasLog_two_sided_power_excursions_of_zero hZero hHalf hOne hLower hbHalf

/-- False RH yields a common exponent for the two signs of the corrected
finite-product logarithm; the witnessing endpoints can be different. -/
theorem PrimeFactorOscillations.publicFalseRHLogarithmExcursions
    (hNotRH : Not RiemannHypothesis) :
    exists b : Real, 0 < b /\ b < 1 / 2 /\
      forall X A : Real,
        (exists x : Real, max X 3 < x /\
          A * x ^ (-b) < Robin1984.nicolasLogMertensOscillation x) /\
        (exists x : Real, max X 3 < x /\
          A * x ^ (-b) < -Robin1984.nicolasLogMertensOscillation x) := by
  exact exists_nicolasLog_two_sided_power_excursions_of_not_RH hNotRH

/-- False RH gives one exponent for both signs of every fixed positive
moving-rank parameter, with actual denominator positivity at the witnesses. -/
theorem PrimeFactorOscillations.publicFalseRHMovingRankPowerExcursions
    (hNotRH : Not RiemannHypothesis) :
    exists b : Real, 0 < b /\ b < 1 / 2 /\
      forall alpha : Real, 0 < alpha ->
        let L : Real -> Real := fun x =>
          Real.eulerMascheroniConstant + Real.log (Real.log (Chebyshev.theta x))
        let r : Real -> Nat := fun x => Nat.floor (alpha * L x)
        let E : Real -> Real := fun x => L x *
          ((PrimeFactorUnimodality.densityRatio
            (PrimeFactorUnimodality.primesBelow (Nat.floor x + 1)) (r x) : Real) -
            Nat.factorialConvolution primeProfileRealCoefficient (r x - 1) (L x) /
              Nat.factorialConvolution primeProfileRealCoefficient (r x) (L x))
        let V : Real -> Prop := fun x =>
          1 < Chebyshev.theta x /\ 2 <= L x /\
          0 < (PrimeFactorUnimodality.weightEsymm
            (PrimeFactorUnimodality.primesBelow (Nat.floor x + 1)) (r x) : Real) /\
          0 < Nat.factorialConvolution primeProfileRealCoefficient (r x) (L x)
        forall X A : Real,
          (exists x : Real, max X 3 < x /\ V x /\ A * x ^ (-b) < E x) /\
          (exists x : Real, max X 3 < x /\ V x /\ A * x ^ (-b) < -E x) := by
  choose rho hZero hHalf hOne using
    Robin1984.exists_riemannZeta_zero_re_gt_half_of_not_riemannHypothesis hNotRH
  let b : Real := ((1 - rho.re) + 1 / 2) / 2
  have hb : 0 < b := by dsimp [b]; linarith
  have hbHalf : b < 1 / 2 := by dsimp [b]; linarith
  have hLower : 1 - rho.re < b := by dsimp [b]; linarith
  refine Exists.intro b (And.intro hb (And.intro hbHalf ?_))
  intro alpha ha
  exact densityRatio_thetaClock_two_sided_power_excursions_of_zero
    hZero hHalf hOne hLower hbHalf.le alpha ha
