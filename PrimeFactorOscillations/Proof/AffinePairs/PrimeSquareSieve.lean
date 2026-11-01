import PrimeFactorOscillations.Proof.AffinePairs.MarginalLimits

/-! # Prime-relative square sparsity from independent local tests

The auxiliary primes and their product stay fixed in every input-cutoff
limit. The number of tests is chosen only through the final epsilon argument.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations

open scoped Classical
attribute [local instance] Classical.propDecidable

theorem tendsto_prime_square_values_zero_of_unit_tests
    (f : Nat -> Int) (g : forall ell : Nat, ZMod ell -> ZMod ell) (B : Nat)
    (hcast : forall ell n : Nat, (Int.cast (f n) : ZMod ell) = g ell (n : ZMod ell))
    (hlocal : forall ell : Nat, Nat.Prime ell -> B <= ell ->
      4 * Nat.card {u : Units (ZMod ell) // IsSquare (g ell (u : ZMod ell))} <=
        3 * ell.totient) :
    Filter.Tendsto (fun N : Nat =>
      (((Nat.primesLE N).filter (fun n => IsSquare (f n))).card : Real) /
        (Nat.primeCounting N : Real)) Filter.atTop (nhds 0) := by
  have hinf : Set.Infinite {ell : Nat | Nat.Prime ell /\ B <= ell} := by
    apply Set.infinite_of_forall_exists_gt
    intro a
    choose ell hell hprime using Nat.exists_infinite_primes (max B (a + 1))
    exact Exists.intro ell (And.intro
      (And.intro hprime ((le_max_left B (a + 1)).trans hell)) (by omega))
  let e := Set.Infinite.natEmbedding {ell : Nat | Nat.Prime ell /\ B <= ell} hinf
  apply Metric.tendsto_atTop.mpr
  intro epsilon hepsilon
  have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : (0 : Real) <= 3 / 4) (by norm_num : (3 / 4 : Real) < 1)
  choose k hk using (hpow.eventually_lt_const (half_pos hepsilon)).exists
  let m : Fin k -> Nat := fun i => (e i.val).val
  have hm (i : Fin k) : Nat.Prime (m i) /\ B <= m i := (e i.val).property
  have : forall i : Fin k, NeZero (m i) := fun i => NeZero.mk (hm i).1.ne_zero
  have hprodpos : 0 < Finset.univ.prod m :=
    Finset.prod_pos (fun i _ => (hm i).1.pos)
  have : NeZero (Finset.univ.prod m) := NeZero.mk (Nat.ne_of_gt hprodpos)
  have hc : Pairwise (fun i j : Fin k => (m i).Coprime (m j)) := by
    intro i j hij
    apply (hm i).1.coprime_iff_not_dvd.mpr
    intro hd
    have heq : m i = m j := by
      rcases (Nat.dvd_prime (hm j).1).mp hd with hone | heq
      exact False.elim ((hm i).1.ne_one hone)
      exact heq
    apply hij
    apply Fin.ext
    apply e.injective
    exact Subtype.ext heq
  let w : Fin k -> Real := fun i =>
    (Nat.card {u : Units (ZMod (m i)) // IsSquare (g (m i) (u : ZMod (m i)))} : Real) /
      ((m i).totient : Real)
  have hw0 (i : Fin k) : 0 <= w i := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hw (i : Fin k) : w i <= (3 / 4 : Real) := by
    have hfour : 4 * (Nat.card {u : Units (ZMod (m i)) //
        IsSquare (g (m i) (u : ZMod (m i)))} : Real) <=
          3 * ((m i).totient : Real) := by
      exact_mod_cast hlocal (m i) (hm i).1 (hm i).2
    have ht : (0 : Real) < (m i).totient := by
      exact_mod_cast Nat.totient_pos.mpr (hm i).1.pos
    change _ / ((m i).totient : Real) <= _
    calc
      _ <= (3 * ((m i).totient : Real) / 4) / ((m i).totient : Real) :=
        div_le_div_of_nonneg_right (by linarith only [hfour]) ht.le
      _ = 3 / 4 := by field_simp
  have hproducts (s : Finset (Fin k)) :
      0 <= s.prod w /\ s.prod w <= (3 / 4 : Real) ^ s.card := by
    induction s using Finset.induction_on with
    | empty => norm_num
    | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.card_insert_of_notMem hi, pow_succ]
      refine And.intro (mul_nonneg (hw0 i) ih.1) ?_
      calc
        _ <= (3 / 4 : Real) * s.prod w := mul_le_mul_of_nonneg_right (hw i) ih.1
        _ <= (3 / 4 : Real) * (3 / 4 : Real) ^ s.card :=
          mul_le_mul_of_nonneg_left ih.2 (by norm_num)
        _ = _ := by ring
  have hsmall : Finset.univ.prod w < epsilon := by
    have hbound := (hproducts Finset.univ).2
    simp only [Finset.card_univ, Fintype.card_fin] at hbound
    linarith only [hbound, hk, hepsilon]
  have hlimit := tendsto_prime_crt_pattern_probability m hc
    (fun i x => IsSquare (g (m i) x))
  have hevent := hlimit.eventually_lt_const hsmall
  choose K hK using Filter.eventually_atTop.mp hevent
  refine Exists.intro K ?_
  intro N hN
  have hsubset :
      (Nat.primesLE N).filter (fun n => IsSquare (f n)) <=
      (Nat.primesLE N).filter (fun (n : Nat) => forall i : Fin k,
        IsSquare (g (m i)
          ((ZMod.prodEquivPi m hc (n : ZMod (Finset.univ.prod m))) i))) := by
    intro n hn
    have hn' := Finset.mem_filter.mp hn
    apply Finset.mem_filter.mpr
    refine And.intro hn'.1 ?_
    intro i
    have hs := hn'.2.map (Int.castRingHom (ZMod (m i)))
    change IsSquare (Int.cast (f n) : ZMod (m i)) at hs
    rw [hcast] at hs
    have hcoord :
        ((ZMod.prodEquivPi m hc (n : ZMod (Finset.univ.prod m))) i) =
          (n : ZMod (m i)) := by
      have hh := congrFun (map_natCast (ZMod.prodEquivPi m hc) n) i
      exact hh
    rw [hcoord]
    exact hs
  have hcard : (((Nat.primesLE N).filter (fun n => IsSquare (f n))).card : Real) <=
      (((Nat.primesLE N).filter (fun (n : Nat) => forall i : Fin k,
        IsSquare (g (m i)
          ((ZMod.prodEquivPi m hc (n : ZMod (Finset.univ.prod m))) i)))).card : Real) := by
    exact_mod_cast Finset.card_le_card hsubset
  have hratio := div_le_div_of_nonneg_right hcard
    (Nat.cast_nonneg (Nat.primeCounting N) : (0 : Real) <= Nat.primeCounting N)
  have hnonneg : (0 : Real) <=
      (((Nat.primesLE N).filter (fun n => IsSquare (f n))).card : Real) /
        (Nat.primeCounting N : Real) :=
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have htest :
      (((Nat.primesLE N).filter (fun (n : Nat) => forall i : Fin k,
        IsSquare (g (m i)
          ((ZMod.prodEquivPi m hc (n : ZMod (Finset.univ.prod m))) i)))).card : Real) /
            (Nat.primeCounting N : Real) < epsilon := by
    convert hK N hN using 1
    apply congrArg (fun z : Nat => (z : Real) / (Nat.primeCounting N : Real))
    apply congrArg Finset.card
    apply Finset.ext
    intro n
    simp only [Finset.mem_filter]
  simpa only [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg] using
    lt_of_le_of_lt hratio htest

end PrimeFactorOscillations
