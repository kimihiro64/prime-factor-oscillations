import PrimeFactorOscillations.Proof.AffinePairs.CRTLimits

/-! # First-coordinate prime marginals and fixed-modulus CRT laws

The second sampled prime is marginalized exactly. Every CRT modulus is fixed
before the prime cutoff tends to infinity.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations

open scoped Classical
attribute [local instance] Classical.propDecidable

theorem prime_pair_probability_first_marginal (N : Nat) (P : Nat -> Prop) :
    primePairProbability N (fun ab => P ab.1) =
      (((Nat.primesLE N).filter P).card : Real) / (Nat.primeCounting N : Real) := by
  have heq : (primePairs N).filter (fun ab => P ab.1) =
      SProd.sprod ((Nat.primesLE N).filter P) (Nat.primesLE N) := by
    apply Finset.ext
    intro ab
    simp only [primePairs, Finset.mem_filter, Finset.mem_product]
    constructor <;> intro hab
    all_goals exact And.intro (And.intro hab.1.1 hab.2) hab.1.2
  have hcard : ((primePairs N).filter (fun ab => P ab.1)).card =
      ((Nat.primesLE N).filter P).card * Nat.primeCounting N := by
    rw [heq, Finset.card_product, Nat.primesLE_card_eq_primeCounting]
  unfold primePairProbability
  rw [hcard, Nat.cast_mul]
  by_cases hn : (Nat.primeCounting N : Real) = 0
  case pos =>
    simp only [hn, mul_zero, zero_pow (by decide : Not (2 = 0)), div_zero]
  case neg =>
    field_simp

theorem tendsto_prime_crt_pattern_probability {I : Type*} [Fintype I]
    (m : I -> Nat) [forall i : I, NeZero (m i)] [NeZero (Finset.univ.prod m)]
    (hc : Pairwise (fun i j : I => (m i).Coprime (m j)))
    (P : forall i : I, ZMod (m i) -> Prop) :
    Filter.Tendsto (fun N : Nat =>
      (((Nat.primesLE N).filter (fun (p : Nat) => forall i : I,
        P i ((ZMod.prodEquivPi m hc (p : ZMod (Finset.univ.prod m))) i))).card : Real) /
          (Nat.primeCounting N : Real))
      Filter.atTop (nhds (Finset.univ.prod (fun i : I =>
        (Nat.card {a : Units (ZMod (m i)) // P i (a : ZMod (m i))} : Real) /
          ((m i).totient : Real)))) := by
  have hscalar : forall i : I,
      (Nat.card {ab : Prod (Units (ZMod (m i))) (Units (ZMod (m i))) //
        P i (ab.1 : ZMod (m i))} : Real) / ((m i).totient : Real) ^ 2 =
      (Nat.card {a : Units (ZMod (m i)) // P i (a : ZMod (m i))} : Real) /
        ((m i).totient : Real) := by
    intro i
    let e : Equiv
        {ab : Prod (Units (ZMod (m i))) (Units (ZMod (m i))) //
          P i (ab.1 : ZMod (m i))}
        (Prod {a : Units (ZMod (m i)) // P i (a : ZMod (m i))}
          (Units (ZMod (m i)))) :=
      { toFun := fun ab => (Subtype.mk ab.val.1 ab.property, ab.val.2)
        invFun := fun ab => Subtype.mk (ab.1.val, ab.2) ab.1.property
        left_inv := by intro ab; rfl
        right_inv := by intro ab; rfl }
    have hu : Nat.card (Units (ZMod (m i))) = (m i).totient := by
      rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
    have hcard := Nat.card_congr e
    rw [Nat.card_prod, hu] at hcard
    rw [hcard, Nat.cast_mul]
    have hf : Not (((m i).totient : Real) = 0) := by
      exact_mod_cast Nat.ne_of_gt (Nat.totient_pos.mpr (NeZero.pos (m i)))
    field_simp
  have hlimit := tendsto_prime_pair_crt_pattern_probability m hc
    (fun i ab => P i ab.1)
  have hprod :
      Finset.univ.prod (fun i : I =>
        (Nat.card {ab : Prod (Units (ZMod (m i))) (Units (ZMod (m i))) //
          P i (ab.1 : ZMod (m i))} : Real) / ((m i).totient : Real) ^ 2) =
      Finset.univ.prod (fun i : I =>
        (Nat.card {a : Units (ZMod (m i)) // P i (a : ZMod (m i))} : Real) /
          ((m i).totient : Real)) := by
    exact Finset.prod_congr rfl (fun i _ => hscalar i)
  rw [hprod] at hlimit
  refine Filter.Tendsto.congr' (Filter.Eventually.of_forall (fun N => ?_)) hlimit
  unfold primePairResidueEventProbability
  convert prime_pair_probability_first_marginal N (fun (p : Nat) => forall i : I,
    P i ((ZMod.prodEquivPi m hc (p : ZMod (Finset.univ.prod m))) i)) using 1
  all_goals
    apply congrArg (fun z : Nat => (z : Real) / (Nat.primeCounting N : Real))
    apply congrArg Finset.card
    apply Finset.ext
    intro n
    simp only [Finset.mem_filter]

end PrimeFactorOscillations
