import PrimeFactorOscillations.Helpers.PeakDensityModel

/-!
# Suppression of both outer ranges for prime-density peaks

Suppression of both outer ranges for prime-density peaks for the peak-height comparison of regular prime Bernoulli laws.
-/

set_option autoImplicit false
set_option Elab.async false

open Filter Topology

namespace PrimeFactorOscillations

theorem regularPrimeLaw_left_outer_suppression
    (P : Nat) (hP : 2 <= P) (eta : Nat -> Real) (front : List Real)
    (hf : forall a, List.Mem a front -> 0 <= a /\ a <= 1) (hA : 0 < front.prod)
    (nu K c alpha : Real) (hnu : 0 < nu) (hK : 0 <= K) (hc : 0 < c)
    (halpha : 0 < alpha) (halpha1 : alpha < 1)
    (hunit : forall p, Nat.Prime p -> P < p -> 0 <= eta p /\ eta p < 1)
    (hlower : forall p, Nat.Prime p -> P < p -> c / (p : Real) <= eta p)
    (hupper : forall p, Nat.Prime p -> P < p ->
      eta p / (1 - eta p) <= 2 * nu / (p : Real))
    (herror : forall p, Nat.Prime p -> P < p ->
      abs (eta p / (1 - eta p) - nu / (p : Real)) <= K / (p : Real) ^ 2) :
    Filter.Eventually (fun k : Nat =>
      exists q : Nat, Nat.Prime q /\ P < q /\
        forall p : Nat, Nat.Prime p -> P < p ->
          Real.log (Real.log (p : Real)) <= alpha * Real.log (k : Real) ->
            primeTailDensityWithFront P eta front k p <
              primeTailDensityWithFront P eta front k q) atTop := by
  classical
  let gamma := (alpha + 1) / 2
  let rho := (alpha + gamma) / 2
  let a := (alpha + rho) / 2
  have hg : 0 < gamma := by dsimp [gamma]; linarith only [halpha]
  have hg1 : gamma < 1 := by dsimp [gamma]; linarith only [halpha1]
  have hrho : 0 < rho := by dsimp [rho]; linarith only [halpha, hg]
  have hrg : rho < gamma := by dsimp [rho, gamma]; linarith only [halpha1]
  have ha : 0 < a := by dsimp [a]; linarith only [halpha, hrho]
  have har : a < rho := by dsimp [a, rho, gamma]; linarith only [halpha1]
  have haa : alpha < a := by dsimp [a, rho, gamma]; linarith only [halpha1]
  let E := primeTailOddsMertensError P nu K
  let A := front.prod * c
  have hAc : 0 < A := mul_pos hA hc
  have hb := regularPrimeLaw_interior_benchmark P (by omega) eta nu K gamma rho
    hnu hK hg hrho hrg hg1 hunit hupper herror
  have hs := Real.eventually_peak_left_power_separation nu a rho A (E + Real.log 4)
    gamma front.length hnu ha har hAc hg1
  have he := Real.eventually_loglog_allowance E 0 (nu * (a - alpha))
    (mul_pos hnu (sub_pos.mpr haa))
  have hbase := Real.eventually_loglog_allowance 1 0 (nu * a) (mul_pos hnu ha)
  let tail := fun x : Nat =>
    (x.primesBelow \ (P + 1).primesBelow).toList.map eta
  have ht (x : Nat) : forall b, List.Mem b (tail x) -> 0 <= b /\ b < 1 := by
    intro b hb
    have hh := List.mem_map.mp hb
    choose p hp using hh
    have hm := Finset.mem_sdiff.mp (Finset.mem_toList.mp hp.1)
    have hn := Nat.mem_primesBelow.mp hm.1
    have hPp : P < p := by
      by_contra hnot
      exact hm.2 (Nat.mem_primesBelow.mpr (And.intro (by omega) hn.2))
    rw [<- hp.2]
    exact hunit p hn.2 hPp
  filter_upwards [hb, hs, he, hbase, eventually_ge_atTop P] with k hkbench hksep hkE hkbase hkP
  simp only [zero_mul, add_zero] at hkE hkbase
  choose q hq using hkbench.2
  have hPq : P < q := by
    have hk2 := hkbench.1
    have hkk : k <= k ^ 2 := by nlinarith only [hk2]
    omega
  refine Exists.intro q (And.intro hq.1 (And.intro hPq ?_))
  intro p hp hPp hleft
  let L := nu * a * Real.log (k : Real)
  let B := nu * rho * Real.log (k : Real)
  let U := nu * (Real.log (k : Real) + Real.log 2) + E
  let t := (k : Real) ^ gamma
  let r := k - front.length
  let F := (r.factorial : Real)
  have hF : 0 < F := by dsimp [F]; exact_mod_cast Nat.factorial_pos r
  have hL : 1 <= L := by dsimp [L]; nlinarith only [hkbase]
  have hklog : 0 <= Real.log (k : Real) :=
    Real.log_nonneg (by exact_mod_cast (show 1 <= k by have hh := hkbench.1; omega))
  have hB : 0 <= B := mul_nonneg (mul_pos hnu hrho).le hklog
  have htail := hq.2.2.2.2 r (by dsimp [r]; omega)
  have hlead := List.bernoulliMass_append_leading_lower front (tail q) hf
    (fun b hb => And.intro (ht q b hb).1 (ht q b hb).2.le) r
  have hidx : front.length + r = k := by dsimp [r]; omega
  rw [hidx] at hlead
  have hmass :
      front.prod * (Real.exp (-U) * (B ^ r / F)) <=
        List.bernoulliMass (front ++ tail q) k :=
    (mul_le_mul_of_nonneg_left htail hA.le).trans hlead
  have hqpos : 0 < (q : Real) := by exact_mod_cast hq.1.pos
  have hqexp : (q : Real) <= Real.exp (t + Real.log 4) := by
    have hh := Real.exp_le_exp.mpr hq.2.2.2.1
    rwa [Real.exp_log hqpos] at hh
  have hterm : c * Real.exp (-(t + Real.log 4)) <= eta q := by
    have hh := div_le_div_of_nonneg_left hc.le hqpos hqexp
    have hid : c / Real.exp (t + Real.log 4) =
        c * Real.exp (-(t + Real.log 4)) := by
      rw [Real.exp_neg, div_eq_mul_inv]
    rw [hid] at hh
    exact hh.trans (hlower q hq.1 hPq)
  have hmain : A * Real.exp (-(t + U + Real.log 4)) * (B ^ r / F) <=
      primeTailDensityWithFront P eta front k q := by
    have hprod := mul_le_mul hterm hmass
      (mul_nonneg hA.le (mul_nonneg (Real.exp_pos _).le
        (div_nonneg (pow_nonneg hB r) hF.le))) (hunit q hq.1 hPq).1
    have hid : Real.exp (-(t + U + Real.log 4)) =
        Real.exp (-(t + Real.log 4)) * Real.exp (-U) := by
      rw [<- Real.exp_add]
      congr 1
      ring
    dsimp only [primeTailDensityWithFront]
    change _ <= eta q * List.bernoulliMass (front ++ tail q) k
    calc
      _ = (c * Real.exp (-(t + Real.log 4))) *
          (front.prod * (Real.exp (-U) * (B ^ r / F))) := by rw [hid]; dsimp [A]; ring
      _ <= _ := hprod
  have hn2 : 2 <= p - 1 := by omega
  have hPn : P <= p - 1 := by omega
  have hnp : 0 < ((p - 1 : Nat) : Real) := by exact_mod_cast (show 0 < p - 1 by omega)
  have hnlt : ((p - 1 : Nat) : Real) <= (p : Real) := by
    exact_mod_cast (show p - 1 <= p by omega)
  have hlogn : 0 < Real.log ((p - 1 : Nat) : Real) :=
    Real.log_pos (by exact_mod_cast (show 1 < p - 1 by omega))
  have hLL : Real.log (Real.log ((p - 1 : Nat) : Real)) <=
      alpha * Real.log (k : Real) :=
    (Real.log_le_log hlogn (Real.log_le_log hnp hnlt)).trans hleft
  have hm := tailPrimeOdds_uniform_logLog_error (p - 1) P hn2 (by omega) hPn
    (fun p => eta p / (1 - eta p)) nu K hnu.le hK
    (fun p hp hPp _ => herror p hp hPp)
  have hpe : p - 1 + 1 = p := by omega
  rw [hpe] at hm
  have hsum : ((tail p).map (fun b => b / (1 - b))).sum <= L := by
    have hh : abs (((tail p).map (fun b => b / (1 - b))).sum -
        nu * Real.log (Real.log ((p - 1 : Nat) : Real))) <= E := by
      simpa [tail, E, primeTailOddsMertensError, Function.comp_def] using hm
    have hmult := mul_le_mul_of_nonneg_left hLL hnu.le
    dsimp [L]
    nlinarith only [(abs_le.mp hh).2, hmult, hkE]
  have huppermass := List.bernoulliMass_append_power_upper front (tail p) k L hf (ht p) hL hsum
  have hfull : forall b, List.Mem b (front ++ tail p) -> 0 <= b /\ b <= 1 := by
    intro b hb
    cases List.mem_append.mp hb with
    | inl hb => exact hf b hb
    | inr hb => exact And.intro (ht p b hb).1 (ht p b hb).2.le
  have hmass0 := List.bernoulliMass_nonneg (front ++ tail p) hfull k
  have htop : primeTailDensityWithFront P eta front k p <= L ^ k / F := by
    change eta p * List.bernoulliMass (front ++ tail p) k <= _
    have hh : eta p * List.bernoulliMass (front ++ tail p) k <=
        List.bernoulliMass (front ++ tail p) k := by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right (hunit p hp hPp).2.le hmass0
    exact hh.trans huppermass
  have hsep : L ^ k < A * Real.exp (-(t + U + Real.log 4)) * B ^ r := by
    have hh := hksep.2
    change L ^ k < A * Real.exp (-(t +
      nu * (Real.log (k : Real) + Real.log 2) + (E + Real.log 4))) * B ^ r at hh
    have hid : t + nu * (Real.log (k : Real) + Real.log 2) + (E + Real.log 4) =
        t + U + Real.log 4 := by dsimp [U]; ring
    rwa [hid] at hh
  have hdivide := (div_lt_div_iff_of_pos_right hF).mpr hsep
  have hrearr : (A * Real.exp (-(t + U + Real.log 4)) * B ^ r) / F =
      A * Real.exp (-(t + U + Real.log 4)) * (B ^ r / F) := by ring
  rw [hrearr] at hdivide
  exact (htop.trans_lt hdivide).trans_le hmain

end PrimeFactorOscillations
namespace PrimeFactorOscillations

theorem regularPrimeLaw_right_outer_suppression
    (P : Nat) (hP : 2 <= P) (eta : Nat -> Real) (front : List Real)
    (hf : forall a, List.Mem a front -> 0 <= a /\ a <= 1) (hA : 0 < front.prod)
    (nu K c C beta : Real) (hnu : 0 < nu) (hK : 0 <= K) (hc : 0 < c)
    (hC : 0 < C) (hbeta : 1 < beta)
    (hunit : forall p, Nat.Prime p -> P < p -> 0 <= eta p /\ eta p < 1)
    (hlower : forall p, Nat.Prime p -> P < p -> c / (p : Real) <= eta p)
    (hterminal : forall p, Nat.Prime p -> P < p -> eta p <= C / (p : Real))
    (hupper : forall p, Nat.Prime p -> P < p ->
      eta p / (1 - eta p) <= 2 * nu / (p : Real))
    (herror : forall p, Nat.Prime p -> P < p ->
      abs (eta p / (1 - eta p) - nu / (p : Real)) <= K / (p : Real) ^ 2) :
    Filter.Eventually (fun k : Nat =>
      exists q : Nat, Nat.Prime q /\ P < q /\
        0 < primeTailDensityWithFront P eta front k q /\
        forall p : Nat, Nat.Prime p -> P < p ->
          (k : Real) ^ beta <= Real.log (p : Real) ->
            primeTailDensityWithFront P eta front k p <
              primeTailDensityWithFront P eta front k q) atTop := by
  classical
  let E := primeTailOddsMertensError P nu K
  let A := front.prod * c
  have hAc : 0 < A := mul_pos hA hc
  have hb := regularPrimeLaw_interior_benchmark P (by omega) eta nu K
    (1 / 2) (1 / 4) hnu hK (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hunit hupper herror
  have hs := Real.eventually_peak_right_power_separation A C nu (E + Real.log 4)
    (1 / 2) beta hAc hC (by norm_num) hbeta
  have hbase := Real.eventually_loglog_allowance 1 0 (nu * (1 / 4))
    (mul_pos hnu (by norm_num))
  let tail := fun x : Nat =>
    (x.primesBelow \ (P + 1).primesBelow).toList.map eta
  have ht (x : Nat) : forall b, List.Mem b (tail x) -> 0 <= b /\ b < 1 := by
    intro b hb
    have hh := List.mem_map.mp hb
    choose p hp using hh
    have hm := Finset.mem_sdiff.mp (Finset.mem_toList.mp hp.1)
    have hn := Nat.mem_primesBelow.mp hm.1
    have hPp : P < p := by
      by_contra hnot
      exact hm.2 (Nat.mem_primesBelow.mpr (And.intro (by omega) hn.2))
    rw [<- hp.2]
    exact hunit p hn.2 hPp
  filter_upwards [hb, hs, hbase, eventually_ge_atTop (max P front.length)] with
    k hkbench hksep hkbase hk
  simp only [zero_mul, add_zero] at hkbase
  have hkP : P <= k := (le_max_left _ _).trans hk
  have hks : front.length <= k := (le_max_right _ _).trans hk
  have hk2 := hkbench.1
  have hkone : 1 <= (k : Real) := by exact_mod_cast (show 1 <= k by omega)
  have hkp : 0 < (k : Real) := zero_lt_one.trans_le hkone
  choose q hq using hkbench.2
  have hPq : P < q := by
    have hkk : k <= k ^ 2 := by nlinarith only [hk2]
    omega
  let B := nu * (1 / 4) * Real.log (k : Real)
  let U := nu * (Real.log (k : Real) + Real.log 2) + E
  let t := (k : Real) ^ (1 / 2 : Real)
  let r := k - front.length
  let F := (r.factorial : Real)
  have hF : 0 < F := by dsimp [F]; exact_mod_cast Nat.factorial_pos r
  have hB : 1 <= B := by dsimp [B]; nlinarith only [hkbase]
  have hB0 : 0 <= B := zero_le_one.trans hB
  have htail := hq.2.2.2.2 r (by dsimp [r]; omega)
  have hlead := List.bernoulliMass_append_leading_lower front (tail q) hf
    (fun b hb => And.intro (ht q b hb).1 (ht q b hb).2.le) r
  have hidx : front.length + r = k := by dsimp [r]; omega
  rw [hidx] at hlead
  have hmass :
      front.prod * (Real.exp (-U) * (B ^ r / F)) <=
        List.bernoulliMass (front ++ tail q) k :=
    (mul_le_mul_of_nonneg_left htail hA.le).trans hlead
  have hqpos : 0 < (q : Real) := by exact_mod_cast hq.1.pos
  have hqexp : (q : Real) <= Real.exp (t + Real.log 4) := by
    have hh := Real.exp_le_exp.mpr hq.2.2.2.1
    rwa [Real.exp_log hqpos] at hh
  have hterm : c * Real.exp (-(t + Real.log 4)) <= eta q := by
    have hh := div_le_div_of_nonneg_left hc.le hqpos hqexp
    have hid : c / Real.exp (t + Real.log 4) =
        c * Real.exp (-(t + Real.log 4)) := by rw [Real.exp_neg, div_eq_mul_inv]
    rw [hid] at hh
    exact hh.trans (hlower q hq.1 hPq)
  have hmain : A * Real.exp (-(t + U + Real.log 4)) * (B ^ r / F) <=
      primeTailDensityWithFront P eta front k q := by
    have hprod := mul_le_mul hterm hmass
      (mul_nonneg hA.le (mul_nonneg (Real.exp_pos _).le
        (div_nonneg (pow_nonneg hB0 r) hF.le))) (hunit q hq.1 hPq).1
    have hid : Real.exp (-(t + U + Real.log 4)) =
        Real.exp (-(t + Real.log 4)) * Real.exp (-U) := by
      rw [<- Real.exp_add]
      congr 1
      ring
    change _ <= eta q * List.bernoulliMass (front ++ tail q) k
    calc
      _ = (c * Real.exp (-(t + Real.log 4))) *
          (front.prod * (Real.exp (-U) * (B ^ r / F))) := by rw [hid]; dsimp [A]; ring
      _ <= _ := hprod
  have hpowB : forall j : Nat, 1 <= B ^ j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
        rw [pow_succ]
        have hh := mul_le_mul ih hB (by norm_num : (0 : Real) <= 1)
          (pow_nonneg hB0 j)
        simpa only [one_mul] using hh
  have hfact : F <= (k : Real) ^ k := by
    have hrk : r <= k := by dsimp [r]; omega
    have hh : (r.factorial : Real) <= (k.factorial : Real) := by
      exact_mod_cast Nat.factorial_le hrk
    exact hh.trans (Real.factorial_le_fixed_base_power k k (le_refl k))
  have hfrac : 1 / (k : Real) ^ k <= B ^ r / F :=
    (div_le_div_of_nonneg_left (by norm_num) hF hfact).trans
      (div_le_div_of_nonneg_right (hpowB r) hF.le)
  have hbench : A * Real.exp (-(t + U + Real.log 4)) / (k : Real) ^ k <=
      primeTailDensityWithFront P eta front k q := by
    have hh := mul_le_mul_of_nonneg_left hfrac
      (mul_pos hAc (Real.exp_pos (-(t + U + Real.log 4)))).le
    have he : A * Real.exp (-(t + U + Real.log 4)) * (1 / (k : Real) ^ k) =
        A * Real.exp (-(t + U + Real.log 4)) / (k : Real) ^ k := by ring
    rw [he] at hh
    exact hh.trans hmain
  have hpositive : 0 < primeTailDensityWithFront P eta front k q :=
    (div_pos (mul_pos hAc (Real.exp_pos _)) (pow_pos hkp k)).trans_le hbench
  refine Exists.intro q (And.intro hq.1 (And.intro hPq (And.intro hpositive ?_)))
  intro p hp hPp hright
  have hfull : forall b, List.Mem b (front ++ tail p) -> 0 <= b /\ b <= 1 := by
    intro b hb
    cases List.mem_append.mp hb with
    | inl hb => exact hf b hb
    | inr hb => exact And.intro (ht p b hb).1 (ht p b hb).2.le
  have htop : primeTailDensityWithFront P eta front k p <= C / (p : Real) := by
    have hh := mul_le_mul_of_nonneg_left
      (List.bernoulliMass_le_one (front ++ tail p) hfull k) (hunit p hp hPp).1
    simp only [mul_one] at hh
    exact hh.trans (hterminal p hp hPp)
  have hppos : 0 < (p : Real) := by exact_mod_cast hp.pos
  have hpexp : Real.exp ((k : Real) ^ beta) <= (p : Real) := by
    have hh := Real.exp_le_exp.mpr hright
    rwa [Real.exp_log hppos] at hh
  have hpdecay : C / (p : Real) <= C * Real.exp (-((k : Real) ^ beta)) := by
    have hh := div_le_div_of_nonneg_left hC.le (Real.exp_pos _) hpexp
    rw [Real.exp_neg, <- div_eq_mul_inv]
    exact hh
  have hsep : C * Real.exp (-((k : Real) ^ beta)) <
      A * Real.exp (-(t + U + Real.log 4)) / (k : Real) ^ k := by
    have hh := hksep
    change C * Real.exp (-((k : Real) ^ beta)) <
      A * Real.exp (-(t + nu * (Real.log (k : Real) + Real.log 2) +
        (E + Real.log 4))) / (k : Real) ^ k at hh
    have hid : t + nu * (Real.log (k : Real) + Real.log 2) + (E + Real.log 4) =
        t + U + Real.log 4 := by dsimp [U]; ring
    rwa [hid] at hh
  exact ((htop.trans hpdecay).trans_lt hsep).trans_le hbench

end PrimeFactorOscillations

