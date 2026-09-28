import PrimeFactorOscillations.Helpers.AffineUnitProbabilities
import PrimeFactorOscillations.Proof.AffinePairs.CRTLimits

/-! # Exact affine prime-pair divisibility pattern limits -/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.AffineSumFamily

open scoped Classical

theorem tendsto_prime_divisibility_pattern (F : AffineSumFamily)
    {I : Type*} [Fintype I] (m : I -> Nat)
    (hp : forall i : I, Nat.Prime (m i))
    (hc : Pairwise (fun i j : I => (m i).Coprime (m j)))
    (b : I -> Prop) [DecidablePred b] :
    Filter.Tendsto (fun N : Nat => primePairProbability N (fun ab => forall i : I,
      if b i then Dvd.dvd (m i : Int) (F.value ab.1 ab.2)
      else Not (Dvd.dvd (m i : Int) (F.value ab.1 ab.2)))) Filter.atTop
      (nhds (Finset.univ.prod (fun i : I =>
        if b i then F.localProbability (m i) else 1 - F.localProbability (m i)))) := by
  let : forall i : I, NeZero (m i) := fun i => NeZero.mk (hp i).ne_zero
  let : NeZero (Finset.univ.prod m) := NeZero.mk
    (Finset.prod_ne_zero_iff.mpr (fun i _ => (hp i).ne_zero))
  let P : forall i : I, Prod (ZMod (m i)) (ZMod (m i)) -> Prop := fun i ab =>
    if b i then F.eval (ab.1 + ab.2) = 0 else Not (F.eval (ab.1 + ab.2) = 0)
  have hterm (i : I) :
      (Nat.card {ab : Prod (Units (ZMod (m i))) (Units (ZMod (m i))) //
        P i ((ab.1 : ZMod (m i)), (ab.2 : ZMod (m i)))} : Real) /
        ((m i).totient : Real) ^ 2 =
      if b i then F.localProbability (m i) else 1 - F.localProbability (m i) := by
    by_cases hi : b i
    case pos =>
      simpa only [P, ite_eq_left hi] using
        F.unit_divisibility_probability_eq_local (m i) (hp i)
    case neg =>
      simpa only [P, ite_eq_right hi] using
        F.unit_nondivisibility_probability_eq_one_sub_local (m i) (hp i)
  have hprob (N : Nat) : primePairProbability N (fun ab => forall i : I,
      if b i then Dvd.dvd (m i : Int) (F.value ab.1 ab.2)
      else Not (Dvd.dvd (m i : Int) (F.value ab.1 ab.2))) =
      primePairResidueEventProbability N (Finset.univ.prod m) (fun ab => forall i : I,
        P i ((ZMod.prodEquivPi m hc ab.1) i, (ZMod.prodEquivPi m hc ab.2) i)) := by
    unfold primePairResidueEventProbability
    apply congrArg (primePairProbability N)
    funext ab
    apply propext
    apply forall_congr'
    intro i
    by_cases hi : b i
    case pos =>
      simpa only [P, ite_eq_left hi] using
        F.divides_value_iff_crt_zero m hc ab.1 ab.2 i
    case neg =>
      simpa only [P, ite_eq_right hi] using
        not_congr (F.divides_value_iff_crt_zero m hc ab.1 ab.2 i)
  have hscalar : Finset.univ.prod (fun i : I =>
      (Nat.card {ab : Prod (Units (ZMod (m i))) (Units (ZMod (m i))) //
        P i ((ab.1 : ZMod (m i)), (ab.2 : ZMod (m i)))} : Real) /
        ((m i).totient : Real) ^ 2) =
      Finset.univ.prod (fun i : I =>
        if b i then F.localProbability (m i) else 1 - F.localProbability (m i)) := by
    apply Finset.prod_congr rfl
    intro i hi
    exact hterm i
  rw [<- hscalar]
  simpa only [hprob] using tendsto_prime_pair_crt_pattern_probability m hc P

theorem tendsto_prime_set_pattern (F : AffineSumFamily) (S T : Finset Nat)
    (hS : forall l : Nat, Membership.mem S l -> Nat.Prime l) :
    Filter.Tendsto (fun N : Nat => primePairProbability N (fun ab =>
      forall l : Nat, Membership.mem S l ->
        (Dvd.dvd (l : Int) (F.value ab.1 ab.2) <-> Membership.mem T l))) Filter.atTop
      (nhds (S.prod (fun l =>
        if Membership.mem T l then F.localProbability l else 1 - F.localProbability l))) := by
  let m : S -> Nat := fun i => i.val
  have hp : forall i : S, Nat.Prime (m i) := fun i => hS i.val i.property
  have hc : Pairwise (fun i j : S => (m i).Coprime (m j)) := by
    intro i j hij
    apply (Nat.coprime_primes (hp i) (hp j)).mpr
    intro heq
    exact hij (Subtype.ext heq)
  have hlogic (a b : Prop) [Decidable b] :
      (if b then a else Not a) <-> (a <-> b) := by
    by_cases hb : b <;> simp [hb]
  have h := F.tendsto_prime_divisibility_pattern m hp hc
    (fun i : S => Membership.mem T i.val)
  have hprod := Finset.prod_coe_sort S (fun l : Nat =>
    if Membership.mem T l then F.localProbability l else 1 - F.localProbability l)
  simp only [m] at h
  rw [hprod] at h
  simpa only [hlogic, Subtype.forall] using h

end PrimeFactorOscillations.AffineSumFamily
