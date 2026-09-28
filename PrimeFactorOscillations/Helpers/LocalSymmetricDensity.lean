import PrimeFactorOscillations.Definitions.Reversals
import PrimeFactorUnimodality.Definitions.SymmetricDensity

set_option autoImplicit false

/-!
# Symmetric-polynomial representation for the local density

The exact Bernoulli recursion factors into the product of complementary
probabilities and the elementary symmetric polynomial of the odds. The only
algebraic restriction is that no local probability is one. In particular,
zero probabilities such as the generic odd law at two are allowed.
-/

namespace PrimeFactorOscillations

/-- The exact finite identity used to transfer the first-difference criterion
to elementary-symmetric ratio bounds. -/
theorem finiteLocalMass_eq_base_mul_esymm
    (eta : Nat -> Rat) (entries : List Nat)
    (hne : forall p, List.Mem p entries -> Not (eta p = 1)) (r : Nat) :
    finiteLocalMass eta entries r =
      (entries.map (fun p => 1 - eta p)).prod *
        ((entries.map (fun p => eta p / (1 - eta p)) : List Rat) :
          Multiset Rat).esymm r := by
  induction entries generalizing r with
  | nil =>
      cases r with
      | zero => simp [finiteLocalMass]
      | succ r =>
          rw [finiteLocalMass]
          simp only [List.map_nil, List.prod_nil, one_mul]
          have hnil : (([] : List Rat) : Multiset Rat) = 0 := rfl
          rw [hnil, Multiset.esymm_of_card_lt (by simp)]
  | cons p entries ih =>
      have hp : Not (1 - eta p = 0) :=
        sub_ne_zero.mpr (Ne.symm (hne p (List.Mem.head _)))
      have htail : forall q, List.Mem q entries -> Not (eta q = 1) := by
        intro q hq
        exact hne q (List.Mem.tail _ hq)
      have hcancel : (1 - eta p) * (eta p / (1 - eta p)) = eta p := by
        field_simp
      cases r with
      | zero =>
          rw [finiteLocalMass, ih htail 0]
          simp
      | succ r =>
          rw [finiteLocalMass, ih htail (r + 1), ih htail r]
          simp only [List.map_cons, List.prod_cons]
          have hcons :
              ((eta p / (1 - eta p) ::
                entries.map (fun q => eta q / (1 - eta q)) : List Rat) :
                  Multiset Rat) =
                Multiset.cons (eta p / (1 - eta p))
                  (entries.map (fun q => eta q / (1 - eta q)) : Multiset Rat) := rfl
          rw [hcons, PrimeFactorUnimodality.esymm_cons_succ]
          calc
            _ = ((1 - eta p) *
                (entries.map (fun q => 1 - eta q)).prod) *
                (((entries.map (fun q => eta q / (1 - eta q)) : List Rat) :
                    Multiset Rat).esymm (r + 1)) +
              ((1 - eta p) * (eta p / (1 - eta p))) *
                (entries.map (fun q => 1 - eta q)).prod *
                (((entries.map (fun q => eta q / (1 - eta q)) : List Rat) :
                    Multiset Rat).esymm r) := by rw [hcancel]; ring
            _ = _ := by ring

end PrimeFactorOscillations
